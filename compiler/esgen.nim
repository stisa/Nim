#
#
#           The Nim Compiler
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This is the ES6/ES2015 JavaScript code generator.

discard """
Note: pointer/ptr T/var T/addr/deref
-------
Pointers are emulate by using a function with a getter and setter.
This works fine, but doesn't allow to do things like pointer arithmetic
and sometimes requires deepcopying when dereferencing.
Deepcopy will be implementend in 2 ways:
  - a shallow deepcopy using ...[p.deref]
  - a recursive deepcopy based on ...TODO:

Trick 2
-------
It is preferable to generate '||' and '&&' if possible since that is more
idiomatic and hence should be friendlier for the JS JIT implementation. However
code like ``foo and (let bar = baz())`` cannot be translated this way. Instead
the expressions need to be transformed into statements. ``isSimpleExpr``
implements the required case distinction.

TODO: Actually, trick 2 could be improved, since `let bar=baz(), bar` 
is valid and does what you expect (returning bar) (cf. SequenceExpr)
"""

import
  ast, astalgo, trees, magicsys, options,
  nversion, msgs, idents, types,
  ropes, passes, ccgutils, wordrecg, renderer,
  cgmeth, lowerings, sighashes, pathutils,
  lineinfos, rodutils, transf, injectdestructors, sourcemap

import strutils, intsets, tables
#from math import classify

from modulegraphs import ModuleGraph, PPassContext

import backends/es/[esast, esstmt, esexpr, esrender]

type
  ESGen = ref object of PPassContext
    module: PSym
    graph: ModuleGraph
    config: ConfigRef
    #sigConflicts: CountTable[SigHash]

  ESBackend = ref object of RootObj
    ast: ESNode
    generatedProcs: IntSet
    generatedTypeInfos: IntSet
    sigConflicts: CountTable[string]

  ESTypeKind = enum       # necessary JS "types"
    etyNone,              # no type
    etyNull,              # null type
    etyProc,              # proc type
    etyBool,              # bool type
    etyArray,             # JavaScript's array
    etyInt,               # JavaScript's int
    etyFloat,             # JavaScript's float
    etyString,            # JavaScript's raw string
    etyObject,            # JavaScript's reference to an object
    etyPointer            # Reference emulation needed

template translError(es: ESGen, n: PNode, msg:string) =
  es.config.internalError(n.info, msg & " " & $n.kind)

template translError(es: ESGen, msg:string) =
  es.config.internalError(msg)

proc hasProc(b: ESBackend, s: PSym): bool =
  b.generatedProcs.contains(s.id)

proc hasTypeInfo(b: ESBackend, t: PType): bool =
  b.generatedTypeInfos.contains(t.sym.id)

proc newBackend(): ESBackend =
  new(result)
  result.ast = newESModule(":codegen-temp-module")
  result.generatedProcs = initIntSet()
  result.generatedTypeInfos = initIntSet()
  result.sigConflicts = initCountTable[string]()

proc updateBackendName(b: ESBackend, name:string) = b.ast.mname = name

proc updateLoc(s: PSym, loc: int, kind: TLocKind, skind: TStorageLoc) =
  s.loc.k = kind
  s.loc.storage = skind
  #s.loc.pos = loc
  s.loc.r = loc.rope # for debug purposes

proc exportOrUsed(s: PSym): bool =
  ( s.flags.contains(sfExported) and 
    s.skipGenericOwner.flags.contains(sfMainModule)
  ) or s.flags.contains(sfUsed) or
  ( s.flags.contains(sfExportc) and 
    s.skipGenericOwner.flags.contains(sfMainModule) 
  )


const nkGenSkippedKinds = { nkCommentStmt, nkEmpty, 
                            nkTemplateDef, nkFuncDef, nkProcDef, nkMethodDef, 
                            nkIteratorDef, nkMacroDef, nkIncludeStmt, 
                            nkImportStmt, nkExportStmt, nkExportExceptStmt, 
                            nkImportExceptStmt, nkImportAs, nkConverterDef,
                            nkIncludeStmt, nkTypeSection}#, nkWhenStmt, nkWhenExpr }

proc mapType(typ: PType): ESTypeKind =
  ## Map a nim type to js representation
  ## ptr types -> etyPointer
  ## integer, enum, char -> etyInt
  ## float -> float
  ## bool -> bool
  ## nil -> null
  ## generic stuff -> etyNone
  ## object, tuple, set -> etyobject
  ## array, seqs, string -> etyArray
  ## cstring -> etyString
  ## proc -> etyProc
  
  case typ.kind
  of tyVar, tyRef, tyPtr, tyLent, tyPointer:
    result = etyPointer
  of tyRange, tyDistinct, tyOrdinal, tyProxy:
    result = mapType(typ[0])
  of tyInt..tyInt64, tyUInt..tyUInt64, tyEnum, tyChar: result = etyInt
  of tyBool: result = etyBool
  of tyFloat..tyFloat128: result = etyFloat
  of tyString, tySequence,tyArray, tyOpenArray, tyVarargs, tyUncheckedArray: 
    result = etyArray
  of tyObject, tyTuple, tySet:
    result = etyObject
  of tyNil: result = etyNull
  of tyGenericParam, tyGenericBody, tyGenericInvocation,
    tyNone, tyFromExpr, tyForward, tyEmpty,
    tyUntyped, tyTyped, tyTypeDesc, tyBuiltInTypeClass, tyCompositeTypeClass,
    tyAnd, tyOr, tyNot, tyAnything, tyVoid:
    result = etyNone
  of tyGenericInst, tyInferred, tyAlias, tyUserTypeClass, tyUserTypeClassInst,
    tySink, tyOwned:
    result = mapType(typ.lastSon)
  of tyStatic:
    if typ.n != nil: result = mapType(lastSon typ)
    else: result = etyNone
  of tyProc: result = etyProc
  of tyCString: result = etyString
  of tyOptDeprecated: doAssert false

proc mangleName(es: ESGen, s: PSym): string =
  ## Mangle a symbol name.
  ## If it's not a valid js name, do some common replacement.
  ## If it's still not valid, do some more ugly replacements-
  ## If the symbol is not a field, append the symbol id to avoid collisions.
  ## TODO: append a counter instead of symbol id to have nicer names
  ## maybe have a table with created symbol names and a counter, and a generatedSym 
  ## intsets for the id?
  ## If it's included, lookup, otherwise do the replaces and append a counter if needed.
  ## Hopefully mangling will become easier...
  proc validJsName(name: string): bool =
    result = true
    const reservedWords = ["abstract", "await", "boolean", "break", "byte",
      "case", "catch", "char", "class", "const", "continue", "debugger",
      "default", "delete", "do", "double", "else", "enum", "export", "extends",
      "false", "final", "finally", "float", "for", "function", "goto", "if",
      "implements", "import", "in", "instanceof", "int", "interface", "let",
      "long", "native", "new", "null", "package", "private", "protected",
      "public", "return", "short", "static", "super", "switch", "synchronized",
      "this", "throw", "throws", "transient", "true", "try", "typeof", "var",
      "void", "volatile", "while", "with", "yield"]
    case name
    of reservedWords:
      return false
    else:
      discard
    if name[0] in {'0'..'9'}: return false
    for chr in name:
      if chr notin {'A'..'Z','a'..'z','_','$','0'..'9'}:
        return false

  result = s.name.s # TODO cache in loc.r?
  if not result.validJsName:
    # common ones:
    result = result.multiReplace({"=":"eq","+":"plus","-":"minus","*":"star","/":"slash"})
    if not result.validJsName: # still not valid? fine then
      var x = newStringOfCap(s.name.s.len)
      var i = 0
      while i < s.name.s.len:
        let c = s.name.s[i]
        case c
        of 'A'..'Z', 'a'..'z', '_', '0'..'9':
          x.add c
        else:
          x.add("HEX" & toHex(ord(c), 2))
        inc i
      result = x
  # disambiguation if not field
  if not (s.kind == skField):
    result &= "_" & $s.id

proc escapeJSString(s: string): string =
  result = newStringOfCap(s.len + s.len shr 2)
  #result.add("\"")
  for c in items(s):
    case c
    of '\l': result.add("\\n")
    of '\r': result.add("\\r")
    of '\t': result.add("\\t")
    of '\b': result.add("\\b")
    of '\a': result.add("\\a")
    of '\e': result.add("\\e")
    of '\v': result.add("\\v")
    of '\\': result.add("\\\\")
    of '\"': result.add("\\\"")
    else: result.add(c)
  #result.add("\"")

proc makeJSString(s: string, escapeNonAscii = true): string =
  if escapeNonAscii:
    result = strutils.escape(s)
  else:
    result = escapeJSString(s)

proc gen(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode
proc genDefaultLit(es: ESGen, typ: PType): ESNode

proc genObjTypeInfo(es: ESGen, t: PType, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  ## Note that objects are sealed, ie you can't add or remove properties.
  ## Values of existing properties can still be changed.
  ## type A = object
  ##   x: string
  ## becomes
  ## function A({x=""}={}){
  ##   this.x = x
  ##   Object.seal(this);
  ## }
  # TODO: should be vv ?
  # function Car({make /*string*/, model/*string*/, year}={make:"",model:"",year:0}) {
  #     this.make = make;
  #     this.model = model;
  #     this.year = year;
  #     Object.seal(this);
  # }

  #echo es.config.typeToYaml(t)
  # This piece deals with getting the object type of exceptions
  var tt = t
  if tt.isException:
    assert(tt != nil)

    tt = tt.skipTypes(abstractInst)
    while tt.kind == tyObject:
      if tt.sym != nil and tt.sym.magic == mException: break
      if tt[0] == nil: break
      tt = skipTypes(tt[0], abstractPtrs)
  if tt.isNil: translError(es, "genObjtype" & $t.kind)
  # fin exception
  
  var fields : seq[ESNode] = @[]
  for i, reclst in tt.n:
    #echo "RECLIST", $reclst.typ
    #echo es.config.treeToYaml(reclst)
    fields.add(
      newProperty(es.gen(reclst, stmntbody), es.genDefaultLit(reclst.typ))
    )
  
  result = newObjTypeDecl(
    newESIdent(es.mangleName(t.sym)), t.sym.exportOrUsed, fields
  )


proc genDefaultLit(es: ESGen, typ: PType): ESNode =
  ## Generate a literal with default value for when we do things like
  ## var x : int
  ## Specifically:
  ## etyInt -> 0
  ## etyFloat -> 0.0
  ## etyBool -> false
  ## etyString -> ""
  ## etyObject -> {}
  ## etyArray -> []
  ## etyNull, etyProc -> null
  ## etyPointer -> null
  if isEmptyType(typ):
    echo es.config.typeToYaml(typ)
    translError(es, "isEmptyType")
  case mapType(typ)
  of etyNull, etyProc, etyPointer:
    result = newESEmitExpr("null")
  of etyBool:
    result = newESLiteral(false)
  of etyArray:
    result = newArrayExpr()
  of etyInt:
    result = newESLiteral(0)
  of etyFloat:
    result = newESLiteral(0.0)
  of etyString:
    result = newESLiteral("")
  of etyObject:
    case typ.kind
    of tyTuple:
      result = newObjectExpr()
    of tyObject:
      let b = es.graph.backend.ESBackend
      if not b.generatedTypeInfos.containsOrIncl(typ.sym.id):
        b.ast.add(
          es.genObjTypeInfo(typ, b.ast) # TODO:just don't return the function? or return just the ident?
        )
      result = newNewExpr(newESIdent(es.mangleName(typ.sym)))
    of tySet:
      result = newNewExpr(newESIdent("Set"))
    else:
      translError(es, "etyObject shouldn't be " & $typ.kind)
  else:
    echo es.config.typeToYaml(typ)
    translError(es, "etyNone literal" & $typ.kind)

proc genSym(es: ESGen, s: PSym, wantBaseSym = false): ESNode =
  ## Generate a symbol.
  ## If it's a type, make sure the the corresponding function `typ.sym` exists first.
  ## Otherwise, produce sym
  #echo es.config.symToYaml(s)
  case s.kind
  of skType:
    #echo "SYMTYP"
    if s.typ.mapType == etyObject:
      if not es.graph.backend.ESBackend.generatedTypeInfos.containsOrIncl(s.id):
          es.graph.backend.ESBackend.ast.add(es.genObjTypeInfo(s.typ, es.graph.backend.ESBackend.ast))
      result = newESIdent(es.mangleName(s.typ.sym))
    else:
      result = newESIdent("", "MAYBEBUG")
  of skLabel:
    result = newESIdent(es.mangleName(s))
  else:
    #echo "NON SPECIALIZED SYM: ", s.name.s, $s.kind
    result = newESIdent(es.mangleName(s), s.typ.typeToString)

proc genProc(es: ESGen, prc: PSym) =
  ## Generate a js function based on the prc ast.
  ## If there's a result, produce var result = defaultLit(T)
  ## and corresponding return result
  ## The body of the proc is run through transf before generation.
  ## The complete function is added directly to the ast of the module, this places it before
  ## the first call that asked to generate it
  let res = if prc.ast.len > resultPos :prc.ast[resultPos] else: nil
  let resT = prc.getReturnType
  var bdy = newBlockStmt()
  if not res.isNil:
    #echo "RT::"
    #echo es.config.typeToYaml(resT)
    bdy.add(
      newVarDecl(esLet, false,
        [newVarDeclarator(
          newESIdent(es.mangleName(res.sym), resT.typeToString), es.genDefaultLit(resT)
        )]
      )
    )
  
  # handle params first so change loc is there when generating the body
  let declparams = prc.typ.n
  var params = newSeq[ESNode](declparams.len-1)
  
  for i, p in declparams:
    if i == 0: continue
    if p.sym.ast.isNil: # no default value
      params[i-1] = newESIdent(mangleName(es, p.sym), p.sym.typ.typeToString)
    else:
      params[i-1] = newVarDeclarator(newESIdent(mangleName(es, p.sym), p.sym.typ.typeToString), es.gen(p.sym.ast, bdy)) #body is wrong? 

  var trandiscarded = newBlockStmt()
  # FIXME: looks like this gen generates some wrong parts
  # added directly to the var body passed in, so we store that in
  # trandiscarded and then ignore that
  bdy.add(
    es.gen(transformBody(es.graph, prc, false), trandiscarded)
  )
  
  if not res.isNil:
    bdy.add(
      newReturnStmt(es.genSym(res.sym))
    )

  ESBackend(es.graph.backend).ast.add( #CHECK:ME can I use stmntbody
    newESFuncDecl(
      newESIdent(mangleName(es, prc), if res.isNil: "" else: resT.typeToString),
      bdy,
      params,
      card(prc.flags*{sfExported, sfExportc}) > 0
    )
  )

proc prepareMagic(es: ESGen, name: string): ESNode =
  ## Prepare magic before using. Looks the magic name up in
  ## the list of compilerprocs, and returns the esident to use
  if name.len == 0: es.translError("empty compiler magic name")
  var s = magicsys.getCompilerProc(es.graph, name)
  if s != nil:
    internalAssert es.config, s.kind in {skProc, skFunc, skMethod, skConverter}
    if not ESBackend(es.graph.backend).generatedProcs.containsOrIncl(s.id):
      genProc(es, s)
    result = newESIdent(es.mangleName(s))
  else:
    es.translError("system module needs: " & name)
    
proc isSimpleExpr(n: PNode): bool =
  # TODO: ignored currently
  # calls all the way down --> can stay expression based
  if n.kind in nkCallKinds+{nkBracketExpr, nkDotExpr, nkPar, nkTupleConstr} or
      (n.kind in {nkObjConstr, nkBracket, nkCurly}):
    for c in n:
      if not isSimpleExpr(c): return false
    result = true
  elif n.isAtom:
    result = true

# proc getTemp(p: PProc, defineInLocals: bool = true): Rope =
#   inc(p.unique)
#   result = "Tmp$1" % [rope(p.unique)]
#   if defineInLocals:
#     p.locals.add(p.indentLine("var $1;$n" % [result]))

proc genBinaryExpr(es: ESGen, operator: string, n: PNode, stmntbody: var ESNode): ESNode =
  ## Generate a binary or logical js expression, such as `a || b` or `a+b`
  let a = n[1]
  let b = n[2]
  
  if operator.isLogicalOp:
    result = newLogicalExpr(operator, es.gen(a, stmntbody), es.gen(b, stmntbody))
  else:
    result = newBinaryExpr(operator, es.gen(a, stmntbody), es.gen(b, stmntbody))
  if isSimpleExpr(a) and isSimpleExpr(b):
    echo "TODO: genBinaryExpr complex expr"
    # echo es.config.treeToYaml(a)
    # echo es.config.treeToYaml(b)
    # es.config.internalError("TODO: genBinaryAsgnExpr complex expr")

proc genBinaryAsgnExpr(es: ESGen, operator: string, n: PNode, stmntbody: var ESNode): ESNode =
  ## Generate a binary asgn js expression, such as `a += b`
  let a = n[1]
  let b = n[2]
  echo es.config.treeToYaml(a)
  result = newAsgnExpr(operator, es.gen(a, stmntbody), es.gen(b, stmntbody))
  if isSimpleExpr(a) and isSimpleExpr(b):
    echo "TODO: genBinaryAsgnExpr complex expr"
    # echo es.config.treeToYaml(a)
    # echo es.config.treeToYaml(b)
    # es.config.internalError("TODO: genBinaryAsgnExpr complex expr")


proc genUnaryExpr(es: ESGen, operator: string, prefix:bool, n: PNode, stmntbody: var ESNode): ESNode =
  ## An unary expr, eg `...[1,2,3` or `!a`
  result = newUnaryExpr(operator, prefix, es.gen(n[1], stmntbody))

  if isSimpleExpr(n[0]):
    echo "TODO: genUnaryExpr complex expr"
  # es.config.internalError("TODO: genUnaryExpr complex expr")

proc needsTemp(n: PNode): bool =
  # TODO: ignored
  # check if n contains a call to determine
  # if a temp should be made to prevent multiple evals
  if n.kind in nkCallKinds + {nkTupleConstr, nkObjConstr, nkBracket, nkCurly}:
    return true
  for c in n:
    if needsTemp(c):
      return true

proc magicToProc(magic: TMagic): string =
  # maps a magic to the compilerproc
  result = case magic:
  # of mAddI: "addInt"
  # of mSubI: "subInt"
  # of mMulI: "mulInt"
  # of mDivI: "divInt"
  # of mModI: "modInt"
  # of mSucc: "addInt"
  # of mPred: "subInt"
  #of mMinI: "nimMin"
  #of mMaxI: "nimMax"
  # of mUnaryMinusI: "negInt"
  # of mUnaryMinusI64: "negInt64"
  # of mAbsI: "absInt"
  of mCharToStr: "nimCharToStr" 
  of mBoolToStr: "nimBoolToStr"
  of mIntToStr: "esNimIntToNimStr"
  of mInt64ToStr: "esNimIntToNimStr"
  of mFloatToStr: "esNimFloatToNimStr"
  of mCStrToStr: "esNimStrToJsStr"
  of mNewString: "esNewString"
  of mNewSeq: "esNewSeq"
  of mIsNil: "esIsNil"
  else:  ""
    

proc genCall(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  ## Generate a call to non-magic procs. Also genProc if it's the first time this symbol
  ## is called.
  if not es.graph.backend.ESBackend.generatedProcs.containsOrIncl(n[0].sym.id):
    es.genProc(n[0].sym)

  var args = newSeq[ESNode]()
  for i, arg in n:
    if i == 0: continue
    args.add(es.gen(arg, stmntbody))
    
  result = newCallExpr(
    genSym(es, n[0].sym), args
  )

proc genEcho(es: ESGen, n: PNode, stmntbody: var ESNode): ESNode =
  ## Generate a call to echo.
  ## It's mapped to console.log([array of string converted to jsstring].join('')) to 
  ## match echo's behaviour
  #echo es.config.treeToYaml(n[1])
  let args = n[1].skipConv
  internalAssert es.config, args.kind == nkBracket

  let magicESId = es.prepareMagic("esNimStrToJsStr")

  var esargs: seq[ESNode] = @[]
  for i in 0..<args.len:
    let it = args[i]
    if it.typ.isCompileTimeOnly: continue
    #echo es.config.treeToYaml(it)
    esargs.add(
      newCallExpr(magicESId, es.gen(it, stmntbody))
    )
  
  result = newMemberCallExpr(newESIdent("console"), newESIdent("log"), 
    newMemberCallExpr(newArrayExpr(esargs), newESIdent("join"), newESEmitExpr("''"))
  ) 
  
proc genMagicCall(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  ## A call to a function that has a magic attached.
  let jsmagic = magicToProc(n[0].sym.magic)
  if jsmagic == "": translError es, n, "JSMagic" & $n[0].sym.magic
  let esid = es.prepareMagic(jsmagic)
  var args = newSeq[ESNode]()
  for i, arg in n:
    if i == 0: continue
    args.add(es.gen(arg, stmntbody))
  result = newCallExpr(esid, args)

proc genMagic(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  ## Produce magics
  #es.config.internalError("TODO: genMagicCall" & n[0].sym.name.s & $n[0].sym.magic)
  # TODO: checkedops
  let op = n[0].sym.magic
  case op
  of mOr: result = genBinaryExpr(es, "||", n, stmntbody)
  of mAnd: result = genBinaryExpr(es, "&&", n, stmntbody)
  of mAddU, mAddI: result = genBinaryExpr(es, "+", n, stmntbody)
  of mSubU, mSubI: result = genBinaryExpr(es, "-", n, stmntbody)
  of mMulU, mMulI: result = genBinaryExpr(es, "*", n, stmntbody)
  of mDivU, mDivI: result = genBinaryExpr(es, "/", n, stmntbody)
  of mInc: result = genBinaryAsgnExpr(es, "+=", n, stmntbody)
  of mSucc: result = genUnaryExpr(es, "--", false, n, stmntbody)
  of mPred: result = genUnaryExpr(es, "--", false, n, stmntbody)
  of mDec: result = genBinaryAsgnExpr(es, "-=", n, stmntbody)
  of mAddF64: result = genBinaryExpr(es, "+", n, stmntbody)
  of mSubF64: result = genBinaryExpr(es, "-", n, stmntbody)
  of mMulF64: result = genBinaryExpr(es, "*", n, stmntbody)
  of mDivF64: result = genBinaryExpr(es, "/", n, stmntbody)
  of mEqI, mEqF64, mEqEnum, mEqCh, mEqB, mEqRef,
    mEqCString, mEqProc: result = genBinaryExpr(es, "==", n, stmntbody) 
  of mLeI, mLeF64, mLeU,mLeEnum,mLeCh,mLeB,mLePtr: result = genBinaryExpr(es, "<=", n, stmntbody) 
  of mLtI, mLtF64, mLtU,mLtEnum,mLtCh,mLtB,mLtPtr: result = genBinaryExpr(es, "<", n, stmntbody) 
  of mEcho:
    result = es.genEcho(n, stmntbody)
  of mIntToStr, mInt64ToStr, mFloatToStr, mBoolToStr, mCharToStr, mCStrToStr, 
    mNewString, mNewSeq #[mAppendStrStr, mAppendStrCh, mAppendSeqElem]#: 
    result = es.genMagicCall(n, stmntbody)
  of mNew:
    #echo "MNEW"
    #echo es.config.treeToYaml(n)
    let addrsym = es.prepareMagic("esAddr")
    var tmp : ESNode = newESIdent("tmp")
    # produces (for a ref T):
    # let tmp = default(T)
    # r_ = esAddr(() => {return tmp;}, (v) => {tmp = v;})
    # This is to match what the `new` proc in system expects.
    # for more info on addr, have a look at genAddr/genDeref
    result = newBlockStmt([
      newVarDecl(esLet,false,
        [newVarDeclarator(tmp, es.genDefaultLit(n[1].typ.skipTypes(skipPtrs)))]
      ),
      # TODO: don't emit, generate the right ast
      newExpressionStmt(newAsgnExpr("=", 
        es.gen(n.lastSon, stmntbody),
        newESEmitExpr(
          render(addrsym) & "(() => { return " & 
          render(tmp) & 
          "; }, (v) => { " &
          render(tmp) & " = v; })"
        )
        #newNewExpr(newESIdent(es.mangleName(n[1].typ.skipTypes({tyRef}).sym)))
      )),
    ])
  
  of mAppendStrStr: 
    #echo "APPENDSTRSTR"
    #echo es.config.treeToYaml(n[1])
    result = newAsgnExpr( "=",
      es.gen(n[1], stmntbody),
      newArrayExpr([
        newUnaryExpr("...", true, es.gen(n[1], stmntbody)) ,
        newUnaryExpr("...", true, es.gen(n[2], stmntbody)) 
      ])
    )
  of mAppendStrCh, mAppendSeqElem: 
    result = newAsgnExpr("=",
      es.gen(n[1], stmntbody),
      newArrayExpr([
        newUnaryExpr("...", true, es.gen(n[1], stmntbody)) ,
        es.gen(n[2], stmntbody) 
      ])
    )
  #  of mAppendStrCh, mAppendSeqElem:
  #    result = newMemberCallExpr(es.gen(n[1], stmntbody), newESIdent("push"), es.gen(n[2], stmntbody))
  of mLengthStr: result = newMemberExpr(es.gen(n[1], stmntbody), newESIdent("length"), true)
  of mOrd:
    #echo es.config.treeToYaml(n)
    case skipTypes(n[1].typ, abstractVar + abstractRange).kind
    of tyEnum, tyInt..tyUInt64, tyChar: result = es.gen(n[1], stmntbody)
    of tyBool: result = newCondExpr(es.gen(n[1], stmntbody), newESLiteral(1), newESLiteral(0) )
    else: translError(es, n, "genOrd")
  of mModI:
    result = newMemberCallExpr(
      newESIdent("Math"),newESIdent("trunc"),
      es.genBinaryExpr("%", n, stmntbody))
  of mAshrI:
    if n[1].typ.size <= 4:
      result = es.genBinaryExpr(">>", n, stmntbody)
    else:
      result = newMemberCallExpr(
      newESIdent("Math"),newESIdent("floor"),
        newBinaryExpr("/",
          es.gen(n[1], stmntbody),
          newMemberCallExpr(
            newESIdent("Math"),newESIdent("pow"),
            [newESLiteral(2), es.gen(n[2], stmntbody)]
          )
        )
      )
  of mBitandI: result = es.genBinaryExpr("&", n, stmntbody)
  of mBitorI: result = es.genBinaryExpr("|", n, stmntbody)
  of mBitxorI: result = es.genBinaryExpr("^", n, stmntbody)
  of mModU: result = es.genBinaryExpr("%", n, stmntbody)
  of mXor: result = es.genBinaryExpr("!=", n, stmntbody)
  of mUnaryMinusI:  result = es.genUnaryExpr("-",true, n, stmntbody)
  of mUnaryMinusI64:  result = es.genUnaryExpr("-",true, n, stmntbody)
  of mAbsI: result = newMemberCallExpr(
      newESIdent("Math"),newESIdent("abs"), [es.gen(n[1],stmntbody)]
    )
  of mNot:  result = es.genUnaryExpr("!", true, n, stmntbody)
  of mUnaryPlusI:  result = es.genUnaryExpr("+",true, n, stmntbody)
  of mBitnotI:  result = es.genUnaryExpr("~",true, n, stmntbody)
  of mUnaryPlusF64:  result = es.genUnaryExpr("+",true, n, stmntbody)
  of mUnaryMinusF64:  result = es.genUnaryExpr("-",true, n, stmntbody)
  of mConStrStr: # concat strstr
    #echo es.config.treeToYaml(n)
    #result = es.genBinaryExpr("+", n, stmntbody)
    result = newArrayExpr()
    result.elements = newSeq[ESNode](n.len-1)
    for i, el in n:
      if i == 0: continue
      result.elements[i-1] = newUnaryExpr("...", true, es.gen(n[i], stmntbody))
  of mSetLengthStr, mSetLengthSeq:
    result = newAsgnExpr("=",
      newMemberExpr(es.gen(n[1],stmntbody), newESIdent("length"), true),
      es.gen(n[2], stmntbody)
    )    
  of mIsNil:
    result = es.genMagicCall(n, stmntbody)
    #[
  of mShlI: 
    if n[1].typ.size <= 4:
      applyFormat("($1 << $2)", "($1 << $2)")
    else:
      applyFormat("($1 * Math.pow(2,$2))", "($1 * Math.pow(2,$2))")
  of mMinI: applyFormat("nimMin($1, $2)", "nimMin($1, $2)")
  of mMaxI: applyFormat("nimMax($1, $2)", "nimMax($1, $2)")
  of mEqCString: applyFormat("($1 == $2)", "($1 == $2)")
  of mEqProc: applyFormat("($1 == $2)", "($1 == $2)"
  of mStrToStr, mUnown, mIsolate: applyFormat("$1", "$1")
]#
    # mModI,
    # mShrI, mShlI, mAshrI, mBitandI, mBitorI, mBitxorI,
    # mMinI, mMaxI,
    # mModU,
    # mXor, mEqCString, mEqProc,
    # mUnaryMinusI, mUnaryMinusI64, mAbsI, mNot,
    # mUnaryPlusI, mBitnotI,
    # mUnaryPlusF64, mUnaryMinusF64,
    # mCharToStr, mBoolToStr, mIntToStr, mInt64ToStr, mFloatToStr, mCStrToStr,
    # mStrToStr
  # of mAddI..mStrToStr: arith(p, n, r, op)
  # of mRepr: genRepr(p, n, r)
  # of mSwap: genSwap(p, n)
  # of mAppendStrCh:
  #   binaryExpr(p, n, r, "addChar",
  #       "addChar($1, $2);")
  # of mAppendStrStr:
  #   var lhs, rhs: TCompRes
  #   gen(p, n[1], lhs)
  #   gen(p, n[2], rhs)

  #   if skipTypes(n[1].typ, abstractVarRange).kind == tyCString:
  #     r.res = "$1 += $2;" % [lhs.rdLoc, rhs.rdLoc]
  #   else:
  #     let (a, tmp) = maybeMakeTemp(p, n[1], lhs)
  #     r.res = "$1.push.apply($3, $2);" % [a, rhs.rdLoc, tmp]
  #   r.kind = resExpr
  # of mAppendSeqElem:
  #   var x, y: TCompRes
  #   gen(p, n[1], x)
  #   gen(p, n[2], y)
  #   if mapType(n[2].typ) == etyPointer:
  #     let c = "[$1, $2]" % [y.address, y.res]
  #     r.res = "$1.push($2);" % [x.rdLoc, c]
  #   elif needsNoCopy(p, n[2]):
  #     r.res = "$1.push($2);" % [x.rdLoc, y.rdLoc]
  #   else:
  #     useMagic(p, "nimCopy")
  #     let c = getTemp(p, defineInLocals=false)
  #     lineF(p, "var $1 = nimCopy(null, $2, $3);$n",
  #           [c, y.rdLoc, genTypeInfo(p, n[2].typ)])
  #     r.res = "$1.push($2);" % [x.rdLoc, c]
  #   r.kind = resExpr
  # of mConStrStr:
  #   genConStrStr(p, n, r)
  # of mEqStr:
  #   binaryExpr(p, n, r, "eqStrings", "eqStrings($1, $2)")
  # of mLeStr:
  #   binaryExpr(p, n, r, "cmpStrings", "(cmpStrings($1, $2) <= 0)")
  # of mLtStr:
  #   binaryExpr(p, n, r, "cmpStrings", "(cmpStrings($1, $2) < 0)")
  # of mIsNil:
  #   # we want to accept undefined, so we ==
  #   if mapType(n[1].typ) != etyPointer:
  #     unaryExpr(p, n, r, "", "($1 == null)")
  #   else:
  #     var x: TCompRes
  #     gen(p, n[1], x)
  #     r.res = "($# == null && $# === 0)" % [x.address, x.res]
  # of mEnumToStr: genRepr(p, n, r)
  # of mNew, mNewFinalize: genNew(p, n)
  # of mChr: gen(p, n[1], r)
  # of mArrToSeq:
  #   if needsNoCopy(p, n[1]):
  #     gen(p, n[1], r)
  #   else:
  #     var x: TCompRes
  #     gen(p, n[1], x)
  #     useMagic(p, "nimCopy")
  #     r.res = "nimCopy(null, $1, $2)" % [x.rdLoc, genTypeInfo(p, n.typ)]
  # of mDestroy: discard "ignore calls to the default destructor"
  # of mOrd: genOrd(p, n, r)
  # of mLengthStr, mLengthSeq, mLengthOpenArray, mLengthArray:
  #   unaryExpr(p, n, r, "", "($1).length")
  # of mHigh:
  #   unaryExpr(p, n, r, "", "(($1).length-1)")
  # of mInc:
  #   if n[1].typ.skipTypes(abstractRange).kind in {tyUInt..tyUInt64}:
  #     binaryUintExpr(p, n, r, "+", true)
  #   else:
  #     if optOverflowCheck notin p.options: binaryExpr(p, n, r, "", "$1 += $2")
  #     else: binaryExpr(p, n, r, "addInt", "$1 = addInt($3, $2)", true)
  # of ast.mDec:
  #   if n[1].typ.skipTypes(abstractRange).kind in {tyUInt..tyUInt64}:
  #     binaryUintExpr(p, n, r, "-", true)
  #   else:
  #     if optOverflowCheck notin p.options: binaryExpr(p, n, r, "", "$1 -= $2")
  #     else: binaryExpr(p, n, r, "subInt", "$1 = subInt($3, $2)", true)
  # of mSetLengthStr:
  #   binaryExpr(p, n, r, "mnewString", "($1.length = $2)")
  # of mSetLengthSeq:
  #   var x, y: TCompRes
  #   gen(p, n[1], x)
  #   gen(p, n[2], y)
  #   let t = skipTypes(n[1].typ, abstractVar)[0]
  #   let (a, tmp) = maybeMakeTemp(p, n[1], x)
  #   let (b, tmp2) = maybeMakeTemp(p, n[2], y)
  #   r.res = """if ($1.length < $2) { for (var i=$4.length;i<$5;++i) $4.push($3); }
  #              else { $4.length = $5; }""" % [a, b, createVar(p, t, false), tmp, tmp2]
  #   r.kind = resExpr
  # of mCard: unaryExpr(p, n, r, "SetCard", "SetCard($1)")
  # of mLtSet: binaryExpr(p, n, r, "SetLt", "SetLt($1, $2)")
  # of mLeSet: binaryExpr(p, n, r, "SetLe", "SetLe($1, $2)")
  # of mEqSet: binaryExpr(p, n, r, "SetEq", "SetEq($1, $2)")
  # of mMulSet: binaryExpr(p, n, r, "SetMul", "SetMul($1, $2)")
  # of mPlusSet: binaryExpr(p, n, r, "SetPlus", "SetPlus($1, $2)")
  # of mMinusSet: binaryExpr(p, n, r, "SetMinus", "SetMinus($1, $2)")
  # of mIncl: binaryExpr(p, n, r, "", "$1[$2] = true")
  # of mExcl: binaryExpr(p, n, r, "", "delete $1[$2]")
  # of mInSet:
  #   binaryExpr(p, n, r, "", "($1[$2] != undefined)")
  # of mNewSeq: genNewSeq(p, n)
  # of mNewSeqOfCap: unaryExpr(p, n, r, "", "[]")
  # of mOf: genOf(p, n, r)
  # of mDefault: genDefault(p, n, r)
  # of mReset, mWasMoved: genReset(p, n)
  # of mEcho: genEcho(p, n, r)
  # of mNLen..mNError, mSlurp, mStaticExec:
  #   localError(p.config, n.info, errXMustBeCompileTime % n[0].sym.name.s)
  # of mNewString: unaryExpr(p, n, r, "mnewString", "mnewString($1)")
  # of mNewStringOfCap:
  #   unaryExpr(p, n, r, "mnewString", "mnewString(0)")
  # of mDotDot:
  #   genProcForSymIfNeeded(p, n[0].sym)
  #   genCall(p, n, r)
  # of mParseBiggestFloat:
  #   useMagic(p, "nimParseBiggestFloat")
  #   genCall(p, n, r)
  # of mSlice:
  #   # arr.slice([begin[, end]]): 'end' is exclusive
  #   var x, y, z: TCompRes
  #   gen(p, n[1], x)
  #   gen(p, n[2], y)
  #   gen(p, n[3], z)
  #   r.res = "($1.slice($2, $3+1))" % [x.rdLoc, y.rdLoc, z.rdLoc]
  #   r.kind = resExpr
  # of mMove:
  #   genMove(p, n, r)
  else:
    translError(es, n):
      "genMagic: " & $op

proc genAsgn(es: ESGen, lhs, rhs: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Assignment. For vars, this is probably more complex than simply
  ## a = b due to the need to handle var T parameters and derefs., we propably
  ## need to generate deepcopies somewhere.
  echo "GENASGN"
  #echo es.config.treeToYaml(lhs)
  #echo es.config.treeToYaml(rhs)
  result = newExpressionStmt(
    newAsgnExpr("=", es.gen(lhs, stmntbody), es.gen(rhs, stmntbody))
  )
# TODO: wrong for exception, missing generator function call
proc genObjConstrCall(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  ## An object constructor.
  ## Generates something like
  ## new ObjName({"x":objprop}) if the symbol has an object type
  if n.typ.isNil: es.translError(n, "Empty type for nkobjconstr")

  #echo es.config.treeToYaml(n)
  if n[0].kind != nkSym: # ie a nkPar, eg (ref ValueError)(msg: "wrong value")
    echo "GOBJC", n.typ.typeToString
    echo es.config.treeToYaml(n)
    var props = newSeq[ESNode]()
    for i,p in n:
      if i == 0: continue
      props.add(newProperty(es.gen(p[0],stmntbody), es.gen(p[1],stmntbody)))
    result = newObjectExpr(props)
  else:
    if not es.graph.backend.ESBackend.generatedTypeInfos.containsOrIncl(n.typ.sym.id):
        stmntbody.add(es.genObjTypeInfo(n.typ, stmntbody))
      
    #echo es.config.treeToYaml(n)
    var args = newSeq[ESNode]()
    for i, arg in n:
      # arg is exprcolonexpr, don't care about name tho
      if i == 0: continue
      args.add(newProperty(es.gen(arg[0],stmntbody), es.gen(arg[1],stmntbody)))
    
    result = newNewExpr(
      newESIdent(es.mangleName(n[0].sym)), [newObjectExpr(args)]
    )

proc genTupleConstr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## var x = (x:1,x:2)
  ## let y = (1,2)
  ## becomes
  ## let x = [{"x":1,"y":2,"0":1,"1":2}] # TODO: avoid duplacting fields
  ## const y = {"0":1,"1":2}
  #echo es.config.treeToYaml(n)
  var props = newSeq[ESNode]()
  if n[0].kind == nkExprColonExpr: # a named tuple
    for i, p in n:
      props.add(newProperty(es.gen(p[0], stmntbody), es.gen(p[1],stmntbody)))
      props.add(newProperty(newESIdent($i), es.gen(p[1],stmntbody)))
  else:
    for i, p in n:
      props.add(newProperty(newESIdent($i), es.gen(p,stmntbody)))
  result = newObjectExpr(props)

proc genOfBranch(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation= nil): seq[ESNode] =
  #echo es.config.treeToYaml(n)
  result = @[]
  if n[0].kind != nkRange:
    result.add(newSwitchCase(
        es.gen(n[0], stmntbody),
        [es.gen(n[1], stmntbody)],
        false
    ))
  else:
    let span = n[0][1].intVal - n[0][0].intVal
    for j in 0..<span:
      result.add(
        newSwitchCase(
          newESLiteral(j),
          [newEmptyStmt()],
          true
        )
      )
    
    result.add(
      newSwitchCase(
        newESLiteral(span),
        [es.gen(n[1], stmntbody)],
        false
      )
    )
proc genOfMultiBranch(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation= nil): seq[ESNode] =
  #echo es.config.treeToYaml(n)
  result = @[]
  for i, cl in n:
    if i != n.len-1:
      if cl.kind == nkRange:  
        let span = cl[1].intVal - cl[0].intVal
        let base = cl[0].intVal
        for j in 0..span:
          result.add(newSwitchCase(newESLiteral(j+base), [newEmptyStmt()], true))
      else:
        result.add(newSwitchCase(es.gen(cl, stmntbody), [newEmptyStmt()], true))
    else:
      # reuse last case and make it non-fallthrough
      result[^1].sfall = false
      result[^1].sconsequent = @[es.gen(cl, stmntbody)]

proc genDeaultBranch(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation= nil): ESNode=
  result = newDefaultCase([es.gen(n[0], stmntbody)])

proc genCaseStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## case k:
  ## of 1: echo k
  ## of 2..5: echo k+1
  ## else: echo 0
  ## becomes:
  ## switch(k){
  ##   case(1)
  ##   console.log(k);
  ##   break;
  ##   case(2)
  ##   case(3)
  ##   case(4)
  ##   case(5)
  ##   console.log(k+1);
  ##   break;
  ##   default:
  ##   console.log("0")
  var clauses = newSeq[ESNode]()
  var cond: ESNode
  var def : ESNode = newEmptyStmt()
  for i, cl in n:
    #echo cl.kind
    if i == 0: cond = es.gen(cl, stmntbody) # cond
    elif cl.kind == nkOfBranch:
      if cl.len == 2:
        clauses.add(es.genOfBranch(cl, stmntbody))
      else:
        clauses.add(es.genOfMultiBranch(cl, stmntbody))
    elif cl.kind == nkElse:
      def = es.genDeaultBranch(cl, stmntbody)
    else:
      translError(es, cl):
        "gencasestmt"
  result = newSwitchStmt(cond, clauses, def)

proc genLit(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## 
  case n.kind:
  of nkCharLit..nkUInt64Lit:
    if n.typ.kind == tyBool:
      result = newESLiteral(n.intVal != 0)
    else:
      result = newESLiteral(n.intVal)
  of nkNilLit:
    result = es.genDefaultLit(n.typ)
  of nkStrLit..nkTripleStrLit:
    let magicid = es.prepareMagic("esNimStrLit")
    result = newCallExpr(magicid, newESLiteral(makeJSString(n.strVal, false)))
  of nkFloatLit..nkFloat64Lit:
    result = newESLiteral(n.floatVal)
  else:
    translError(es,n):
      "genLit not handled"


proc genCallOrMagic(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## A nkCall node, dispatch to the right path if a magic is present
  echo "SYMID: ", n[0].sym.id, " name ", mangleName(es, n[0].sym), " magic ", n[0].sym.magic
  if (n[0].kind == nkSym) and (n[0].sym.magic != mNone):
    if n[0].sym.magic == mNew:
      # new is a exprstatement in nim, but for js we need multiple stmts
      result = genMagic(es, n, stmntbody)
    elif isEmptyType(n.typ):  # a magic call stmt
      result = newExpressionStmt(genMagic(es, n, stmntbody))
    else: result = genMagic(es, n, stmntbody)
  elif isEmptyType(n.typ):  # a call stmt
    result = newExpressionStmt(genCall(es, n, stmntbody)) # TODO: use the fact that no result is needed
  else:
    result = genCall(es, n, stmntbody)

proc genVar(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## var x = 0
  ## becomes
  ## let x = 0
  ## while var x: int
  ## becomes let x = 0 (ie let x = defaultLit(T))
  result = newBlockStmt()
  #echo es.config.treeToYaml(n)
  for v in n.sons:
    #v[0].sym.loc.storage = OnHeap
    # TODO: handle noinit?
    if v[2].kind == nkEmpty: # no initial value
      result.add(
        newVarDecl(
          esLet, v[0].sym.exportOrUsed and v[0].sym.owner.kind == skModule,
          [newVarDeclarator(newESIdent(mangleName(es,v[0].sym), v[0].sym.typ.typeToString), es.genDefaultLit(v[0].sym.typ) )]
        )
      )
    else:
      result.add(
        newVarDecl(
          esLet, v[0].sym.exportOrUsed and v[0].sym.owner.kind == skModule,
          [newVarDeclarator(newESIdent(mangleName(es, v[0].sym), v[0].sym.typ.typeToString), es.gen(v[2], stmntbody))]
        )
      )
proc genLet(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## let x = 123 -> const x = 123
  result = newBlockStmt()
  for v in n.sons:
    #echo "letchild"
    #echo es.config.treeToYaml(v)
    result.add(
      newVarDecl(
        esConst, v[0].sym.exportOrUsed  and v[0].sym.owner.kind == skModule,
        [newVarDeclarator(newESIdent(mangleName(es, v[0].sym), v[0].sym.typ.typeToString), es.gen(v[2], stmntbody))]
      )
    )

proc genStmtListExpr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  for i, son in n.sons:
    if i == n.sons.len-1:
      result = es.gen(son,stmntbody)
    else:
      stmntbody.add(es.gen(son,stmntbody))

proc genStmtList(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =  
  ## Generate each stmt and add it to the block.
  ## Tries to adding emptystatements as they lead to a lot of useless newlines
  result = newBlockStmt()
  for son in n.sons:
    let tmp = es.gen(son,stmntbody)
    if tmp.isNil: translError(es, n, "Nil result for stament in stmtlist")
    if tmp.typ == ekEmptyStatement: discard
    else:
      result.add(tmp)

proc genBracket(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =  
  ## Generate arrays literals
  ## Nim arrays and seqs are mapped to js Array
  ## In case a nim array is of one of the types supported
  ## by js typedarrays, use that instead.
  result = newArrayExpr()
  for el in n.sons:
    result.add(es.gen(el,stmntbody))
  
  if n.typ.kind != tySequence:
    # a static array, let's make some optimizations
    # TODO: rewrite magics so they make use of Array mutability
    # instead of reallocating
    var mappedarrtype = case n.typ.lastSon.kind
      of tyInt32, tyInt: "Int32Array"
      of tyInt8: "Int8Array"
      of tyInt16: "Int16Array"
      of tyUInt32, tyUInt: "Uint32Array"
      of tyUInt8: "Uint8Array"
      of tyUInt16: "Uint16Array"
      of tyFloat, tyFloat64: "Float64Array"
      of tyFloat32: "Float32Array"
      else: ""
    if mappedarrtype != "":
      result = newNewExpr(newESIdent(mappedarrtype), result)


proc genCurly(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =  
  ## Nim Sets are mapped to js Set type
  result = newArrayExpr()
  for el in n.sons:
    if el.kind == nkRange:
      let span = el[1].intVal - el[0].intVal
      let base = el[0].intVal
      for j in 0..span:
        result.add(newESLiteral(j))
    else:
      result.add(es.gen(el,stmntbody))
  
  result = newNewExpr(newESIdent("Set"), result)
  

proc genBracketExpr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## An array access expression
  #echo es.config.treeToYaml(n)
  result = newMemberExpr(es.gen(n[0], stmntbody), es.gen(n[1], stmntbody), false)

proc genWhileLoopStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = newWhileStmt(
    es.gen(n[0], stmntbody),
    es.gen(n[1], stmntbody)
  )

proc genBlockStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## A block statement may have a name. This maps to js labeled blocks
  result = newLabeledStmt(
    newESIdent(mangleName(es, n[0].sym)),
    es.gen(n[1], stmntbody)
  )

proc genBlockExpr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  # skip name for block stmt, FIXME:
  for i, son in n[1]:
    if i == n.sons.len-1:
      result = es.gen(son,stmntbody)
    else:
      stmntbody.add(es.gen(son,stmntbody))

proc genConst(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Nim consts are compiletime, and they're mostly not present in the end code
  ## unless the const it is all of the below:
  ## - exported or used or exportc
  ## - owned by mainmodule
  result = newBlockStmt()
  for c in n.sons:
    if c[0].sym.exportOrUsed and c[0].sym.owner.flags.contains(sfMainModule):
      result.add(
        newVarDecl(
          esConst, c[0].sym.exportOrUsed and c[0].sym.owner.flags.contains(sfMainModule),
          [newVarDeclarator(newESIdent(mangleName(es, c[0].sym), c[0].sym.typ.typeToString), es.gen(c[2], stmntbody))]
        )
      )
  if result.len == 0:
      result = newEmptyStmt()

proc genDotExpr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Field access, eg a.b
  echo "DOTEXPR"
  #echo es.config.treeToYaml(n)
  result = newMemberExpr(
    es.gen(n[0],stmntbody), es.gen(n[1],stmntbody), true
  )

proc genAddr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Addressing only works for `var`s, specifically it can be either
  ## a nim `var` or a param passed by `var T`
  ## and the addr operation produces a call to the function esAddr from jssys:
  ## var p = addr x
  ## produces
  ## function esAddr(d,a){
  ##   return { get deref() { return `d`(); }, set deref(v) { `a`(v); } };
  ## }
  ## let p = esAddr(() => { return `x`; }, (v) => { `x` = v; });
  
  let addrsym = es.prepareMagic("esAddr")
  var val : ESNode
  case n[0].kind
  of nkSym:
    val = es.genSym(n[0].sym, wantBaseSym=false)
  of nkDotExpr:
    val = es.gen(n[0], stmntbody)
  of nkBracketExpr:
    val = es.gen(n[0], stmntbody)
  else:
    translError(es, n):
      "TODO addr: "
  #js: addr(() => { return `x`; }, (v) => { `x` = v; });
  # TODO: don't emit, generate the right ast
  result = newESEmitExpr(
    render(addrsym) & "(() => { return " & 
    render(val) & 
    "; }, (v) => { " &
    render(val) & " = v; })")

  
proc genDeref(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Dereference a nim ptr to a js value by accessing the deref property
  ## of a pointer generated by addr (or by constructing a ptr/ref)
  let ident = es.gen(n[0], stmntbody)
  #echo "DEREFIDENT:", n[0].kind
  #if n[0].kind == nkSym: echo n[0].sym.name.s
  #echo render(ident)
  result = newMemberExpr(
    ident, newESIdent("deref"), true
  )
  #echo "DEREF:"
  #echo render(result)


proc genIfExpr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Start from an empty js stmt
  ## Gen the last branch into result
  ## Gen ^2 branch, use last iteration as the else branch (if then else result)
  ## Recursively build the tree: if ^n then ^n else if ^n-1 then ^n-1 else ... if ^2 then ^2 else ^1

  #echo es.config.treeToYaml(n)
  #echo renderTree(n)
  result = newEmptyStmt()
  for bidx in countdown(n.len-1,0):
    #echo "ifExprloop"
    #echo es.config.treeToYaml(n[bidx])
    #result1 = gen else1
    #result2 = gen if1 else result1
    #result3 = gen if2 else result2
    if n[bidx].kind == nkElseExpr:
      result = es.gen(n[bidx][0], stmntbody)
    else: #nkElif
      result = newCondExpr(
        es.gen(n[bidx][0], stmntbody), # cond 
        es.gen(n[bidx][1], stmntbody), # then
        result                         # else
      )

proc genIfStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Start from an empty js stmt
  ## Gen the last branch into result
  ## Gen ^2 branch, use last iteration as the else branch (if then else result)
  ## Recursively build the tree: if ^n then ^n else if ^n-1 then ^n-1 else ... if ^2 then ^2 else ^1

  #echo conf.treeToYaml(n)
  #echo renderTree(n)
  result = newEmptyStmt()
  for bidx in countdown(n.len-1,0):
    #result1 = gen else1
    #result2 = gen if1 else result1
    #result3 = gen if2 else result2
    if n[bidx].kind == nkElse:
      result = es.gen(n[bidx][0], stmntbody)
    else: #nkElif
      result = newIfStmt(
        es.gen(n[bidx][0], stmntbody), # cond 
        es.gen(n[bidx][1], stmntbody), # then
        result                         # else
      )

proc genPragma(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Only handles emit for now
  
  #echo es.config.treeToYaml(n)
  let maybeEmit = n.getPragmaStmt(wEmit)
  if not maybeEmit.isNil:
    #echo es.config.treeToYaml(maybeEmit)
    var emitstr: string = ""
    for el in maybeEmit[1]: # [0] is !"emit"
      if el.kind in nkStrKinds: emitstr.add(el.getStr)
      elif el.kind == nkIdent: 
        emitstr.add(el.ident.s) # TODO: mangling?
      elif el.kind == nkSym:
        emitstr.add(render(genSym(es, el.sym, wantBaseSym=false)))
      else: discard
    result = newESEmitExpr(emitstr)
  else: 
    message(es.config, n.info, warnUser, "maybe unhandled pragma")
    result = newEmptyStmt()

proc genAsm(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Basically the same as genEmit, but we don't have to search for the emit expression
  var emitstr: string = ""
  echo es.config.treeToYaml(n)
  for el in n:
    if el.kind in nkStrKinds: emitstr.add(el.getStr)
    elif el.kind == nkIdent: 
      emitstr.add(el.ident.s) # TODO: mangling?
    elif el.kind == nkSym:
      emitstr.add(render(genSym(es, el.sym, wantBaseSym=false)))
    else: discard
  result = newESEmitExpr(emitstr)

proc genRaise(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Raise a nim exception. They are mapped to a js `throw` plus some wrapping for stacktraces
  ## raise newException(AssertionDefect, "my message") 
  ## becomes
  ## raiseException(excption, "AssertionDefect")
  ## where excption is 
  ## new AssertionDefect_id({msg: "my message"})
  ## 
  let id = es.prepareMagic("raiseException")
  echo "GENRAISE"
  #echo es.config.typeToYaml(n[0].typ.skipTypes(skipPtrs))
  result = newCallExpr(id, [es.gen(n[0],stmntbody), newESLiteral(n[0].typ.skipTypes(skipPtrs).sym.name.s)])

proc genFinally(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = es.gen(n[0], stmntbody)

proc genExceptBranch(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  if n[0].kind == nkType:
    if n[1].kind == nkStmtListExpr:
      # search for the symbol to use for the exception
      let exsym = es.genSym(n[1][0][0][0].sym)
      var exbody = newBlockStmt()
      for i,son in n[1]:
        if i == 0: continue
        exbody.add(
          es.gen(son, stmntbody)
        )
      result = newCatchClause(
        exsym,
        exbody
      )
    else:
      result = newCatchClause(
        es.genSym(n[0].typ.sym),
        es.gen(n[1], stmntbody)
      )
  #elif n[0].kind == 
  else:
    result = newCatchClause(
      newESIdent("_"),
      es.gen(n[0], stmntbody)
    )
  

proc genTryStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Maps nim try stmt to js try catch
  ## try branch -> try
  ## except -> catch
  ## finally -> finally
  ## see https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Statements/try...catch 
  ## at "Conditional Catch Blocks"
  ## the js exception is called "lastJSError" and it gets assigned to the name
  ## nim expects (ie `e` in `except ValueError as e`) through `getCurrentException`
  #echo "TRYSTMT"
  #echo es.config.treeToYaml(n)
  var catches = newSeq[ESNode]()
  
  var ifcl : ESNode = newEmptyStmt()

  for i in countdown(n.len-1,0):
    let son = n[i]
    if son.kind == nkExceptBranch: 
      if son[0].kind == nkType:
        if son[1].kind == nkStmtListExpr:
          # search for the symbol to use for the exception
          #let exsym = es.genSym(son[1][0][0][0].sym)
          #echo es.config.treeToYaml(son)
          ifcl = newIfStmt(
            newBinaryExpr("instanceof",
              newESIdent("lastJSError"),
              es.genSym(son[0].typ.sym)
            ),
            #exbody sa
            newBlockStmt([
              es.gen(son[1][0], stmntbody),
              es.gen(son[1][1], stmntbody)
            ]),
            ifcl
          )
        else:
          ifcl = newIfStmt(
            newLogicalExpr("==",
              newESIdent("lastJSError"),
              es.genSym(son[0].typ.sym)
            ),            
            es.gen(son[1], stmntbody),
            ifcl
          )
      else:
        # begin here
        ifcl = es.gen(son[0], stmntbody)

  result = newTryStmt(
    es.gen(n[0], stmntbody),
    newCatchClause(newESIdent("lastJSError"), ifcl),
    if n[^1].kind == nkFinally: es.genFinally(n[^1], stmntbody) else: newEmptyStmt()
  )
  

proc genStringToCString(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## A conv from nim string to cstring
  ## TODO: introduce a third type to represent raw js strings, and make cstring a Uint8Array.
  ## because the Uint8array would map better to how cstring work in nim, as they are mutable, whereas
  ## raw js string are immutable
  let id = es.prepareMagic("esNimStrToJsStr")
  result = newCallExpr(id, es.gen(n[0],stmntbody))

proc genCStringToString(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  let id = es.prepareMagic("esNimStrLit")
  result = newCallExpr(id, es.gen(n[0],stmntbody))


proc genRangeCheck(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Check the number is in the specified range. See jssys chckRange
  let id = es.prepareMagic("chckRange")
  #echo es.config.treeToYaml(n)
  result = newCallExpr(id, [es.gen(n[0],stmntbody),es.gen(n[1],stmntbody),es.gen(n[2],stmntbody)])


proc genReturnStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Generate a return statement
  ## If n[0] is an assignment, generate first the assignment return result
  ## else generate return(gen(n[0]))
  #echo "RNTMNR"
  if n[0].kind == nkAsgn:
    #echo es.config.treeToYaml(n)
    result = newBlockStmt(es.gen(n[0], stmntbody))
  else:
    result = newReturnStmt(es.gen(n[0], stmntbody))

proc genDiscardStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Generate a discard statement. They are mapped to js void.
  ## Semantics look similar: run the expression, but return undefined instead of whatever the expression returns
  #echo "DISCARD"
  #echo es.config.treeToYaml(n)
  if n.len == 0 or n[0].kind == nkEmpty: result = newEmptyStmt()
  else: result = newUnaryExpr("void", true, es.gen(n[0], stmntbody))

proc genBreakStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Generate a break statement. In case n[0] is present, break the corresponding label
  #echo "BREAK"
  #echo es.config.treeToYaml(n)
  if n.len == 0:
    result = newBreakStmt(newEmptyStmt())
  else: result = newBreakStmt(es.gen(n[0], stmntbody))


proc genConv(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Convert between types. Largely unneeded in js, but should probably at least handle
  ## objects with a js type, typedarrays that need casting between types, and strings/chars.
  #echo "CONV to ", $n[0].typ.kind
  #echo es.config.treeToYaml(n)
  if n[0].kind == nkSym:
    let t = n[0].sym.typ.kind
    case t:
    of tyChar:
      # new Uint8Array([val])[0]
      result = newMemberExpr(newNewExpr(newESIdent("Uint8Array"),newArrayExpr([es.gen(n[1], stmntbody)])), newESLiteral(0), false)
    of tyUInt8:
      if n[1].typ.kind == tyChar:
        result = newMemberCallExpr(es.gen(n[1], stmntbody), newESIdent("charCodeAt"))
      else:
        echo "#ignored nkConv from ", $n[1].typ.kind ," to ", $t
        result = es.gen(n[1],stmntbody)  
    else:
      echo "#ignored nkConv to ", $t
      result = es.gen(n[1],stmntbody)
  else:
    echo "#non sym conv type target", $n[0].kind
    result = es.gen(n[1], stmntbody)#TODO: figure out conv of non basic types?

proc gen(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## Big bad case stmt. Send each nodekind to its proper gen<Kind> function, ignoring some
  ## node kinds that we dont need (look at nkGenSkippedKinds for a list).
  if n.kind notin nkGenSkippedKinds+{nkStmtList,nkPragma,nkPragmaBlock} and defined debug:
    echo renderTree(n, {renderNoComments, renderIr})
    echo "# gen: ", $n.kind, " module: ", es.config.toFilename(n.info.fileIndex)  
  case n.kind:
  of nkGenSkippedKinds: result = newEmptyStmt() # returns ';'
  of nkSym:
    result = es.genSym(n.sym)
  of nkLiterals, nkNilLit:
    result = es.genLit(n, stmntbody)
  of nkCallKinds:
    result = es.genCallOrMagic(n, stmntbody)
  of nkVarSection:
    result = es.genVar(n, stmntbody)
  of nkLetSection:
    result = es.genLet(n, stmntbody)
  of nkAsgn, nkFastAsgn:
    result = es.genAsgn(n[0], n[1], stmntbody)
  of nkStmtListExpr:
    result = es.genStmtListExpr(n, stmntbody)
  of nkStmtList:
    result = es.genStmtList(n, stmntbody)
  of nkBracket:
    result = es.genBracket(n, stmntbody)
  of nkBracketExpr:
    result = es.genBracketExpr(n, stmntbody)
  of nkWhileStmt:
    result = es.genWhileLoopStmt(n, stmntbody)
  of nkBlockStmt:
    result = es.genBlockStmt(n, stmntbody)
  of nkConstSection: 
    result = es.genConst(n, stmntbody)
  of nkObjConstr:
    result = es.genObjConstrCall(n, stmntbody)
  of nkAddr, nkHiddenAddr:
    result = es.genAddr(n, stmntbody)
  of nkIfStmt:
    result = es.genIfStmt(n, stmntbody)
  of nkIfExpr:
    result = es.genIfExpr(n, stmntbody)
  of nkDerefExpr, nkHiddenDeref:
    result = es.genDeref(n, stmntbody)
  of nkDotExpr:
    result = es.genDotExpr(n, stmntbody)
  of nkPragma:
    result = es.genPragma(n, stmntbody)
  of nkCaseStmt:
    result = es.genCaseStmt(n, stmntbody)
  of nkTupleConstr:
    result = es.genTupleConstr(n, stmntbody)
  of nkPragmaBlock:
    result= es.gen(n.lastSon,stmntbody)
  of nkAsmStmt:
    result = es.genAsm(n, stmntbody)
  of nkRaiseStmt:
    result = es.genRaise(n, stmntbody)
  of nkConv, nkHiddenStdConv, nkHiddenSubConv:
    result = es.genConv(n, stmntbody)
  of nkStringToCString:
    result = es.genStringToCString(n, stmntbody)
  of nkCStringToString:
    result = es.genCStringToString(n, stmntbody)
  of nkReturnStmt:
    result = es.genReturnStmt(n, stmntbody)
  of nkDiscardStmt:
    result = es.genDiscardStmt(n, stmntbody)
  of nkCurly:
    result = es.genCurly(n, stmntbody)
  of nkChckRangeF, nkChckRange64, nkChckRange:
    result = es.genRangeCheck(n, stmntbody)
  of nkBreakStmt:
    result = es.genBreakStmt(n, stmntbody)
  of nkTryStmt, nkHiddenTryStmt:
    result = es.genTryStmt(n, stmntbody)
  of nkCast:
    #echo "CAST"
    #echo es.config.treeToYaml(n)
    result = es.gen(n[1], stmntbody)
  else: 
    echo es.config.treeToYaml(n)
    translError(es, n, "gen: unknown node kind")

  if result.isNil:
    echo "Generated NIL ESNode: ", n.kind
  #[
  of nkClosure:
  of nkPar:
  of nkCheckedFieldExpr:
  of nkObjDownConv:
  of nkObjUpConv:
  of nkCast:
  of nkLambdaKinds
  of nkType:
  of nkBlockExpr:
  of nkTryStmt, nkHiddenTryStmt:
  ]#

proc myProcess(b: PPassContext, n: PNode): PNode =
  ## Process each top level piece of the program.
  ## We split up nkStmtList so that the program is not generated all at once. CHECK: do we need to?
  result = n
  let m = ESGen(b)
  if passes.skipCodegen(m.config, n): return n
  if m.module == nil: internalError(m.config, n.info, "esgen:myProcess")
  let es = ESBackend(m.graph.backend)
  
  #if es.ast.mname notin toFilename(m.config, n.info): return # FIXME: this skippes everything not coming from mainmodule
  var transfN = transformStmt(m.graph,m.module,n)
  if transfN.kind in nkGenSkippedKinds: return
  var tmp : ESNode
  if not (transfN.kind == nkStmtList):
    tmp = m.gen(transfN, es.ast)
    if not tmp.isNil and not (tmp.typ == ekEmptyStatement):
      es.ast.add(tmp)
  else:
    for stmt in transfN:
      tmp = m.gen(stmt, es.ast)
      if not tmp.isNil and not (tmp.typ == ekEmptyStatement):
        es.ast.add(tmp)

proc myClose(graph: ModuleGraph; b: PPassContext, n: PNode): PNode =
  ## Render the js ast to a file when closing the main module.
  ## If asking to run on nodejs, save with `mjs` extension as that's
  ## the one node expects for es6 module.
  ## TODO: select ES6 vs UMD style module and exports/imports, pass it to render
  ## so we don't have to change extension for node to work.
  
  if passes.skipCodegen(graph.config, n): return n
  result = myProcess(b, n)
  var m = ESGen(b)
  let es = ESBackend(m.graph.backend)
  if sfMainModule in m.module.flags:
    let outFile = if graph.config.isDefined("node"):
        m.config.prepareToWriteOutput().changeFileExt("mjs")
      else: m.config.prepareToWriteOutput()
    
    writeFile($outFile, es.ast.render())

proc myOpen(graph: ModuleGraph; s: PSym): PPassContext =
  ## Start working on the module, initialized the backend if nil.
  ## If it's mainmodule, use its name as the name of the js module.
  var es = ESGen(module: s, graph: graph, config: graph.config)
  if es.graph.backend == nil:
    es.graph.backend = newBackend()
  if s.flags.contains(sfMainModule):
    ESBackend(es.graph.backend).updateBackendName(s.name.s)
  result = es

const ESgenPass* = makePass(myOpen, myProcess, myClose)

#[
  http://esprima.org/demo/parse.html
  https://nim-lang.org/docs/macros.html
  TODO: used/exported mainmodule procdef should be generated
]#