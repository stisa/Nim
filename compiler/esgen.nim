#
#
#           The Nim Compiler
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This is the JavaScript code generator.

discard """
The JS code generator contains only 2 tricks:

Trick 1
-------
Some locations (for example 'var int') require "fat pointers" (``etyBaseIndex``)
which are pairs (array, index). The derefence operation is then 'array[index]'.
Check ``mapType`` for the details.

Trick 2
-------
It is preferable to generate '||' and '&&' if possible since that is more
idiomatic and hence should be friendlier for the JS JIT implementation. However
code like ``foo and (let bar = baz())`` cannot be translated this way. Instead
the expressions need to be transformed into statements. ``isSimpleExpr``
implements the required case distinction.

Edit: Actually, trick 2 could be improved, since `let bar=baz(), bar` 
is valid and does what you expect (returning bar)
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
    etyNone,                  # no type
    etyNull,                  # null type
    etyProc,                  # proc type
    etyBool,                  # bool type
    etySeq,                   # Nim seq or string type
    etyInt,                   # JavaScript's int
    etyFloat,                 # JavaScript's float
    etyString,                # JavaScript's string
    etyObject,                # JavaScript's reference to an object
    etyBaseIndex              # base + index needed

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

const
  MappedToObject = {tyObject, tyArray, tyTuple, tyOpenArray,
    tySet, tyVarargs}

proc mapType(typ: PType): ESTypeKind =
  let t = skipTypes(typ, abstractInst)
  case t.kind
  of tyVar, tyRef, tyPtr, tyLent:
    if skipTypes(t.lastSon, abstractInst).kind in MappedToObject:
      result = etyObject
    else:
      result = etyBaseIndex
  of tyPointer:
    # treat a tyPointer like a typed pointer to an array of bytes
    result = etyBaseIndex
  of tyRange, tyDistinct, tyOrdinal, tyProxy:
    result = mapType(t[0])
  of tyInt..tyInt64, tyUInt..tyUInt64, tyEnum, tyChar: result = etyInt
  of tyBool: result = etyBool
  of tyFloat..tyFloat128: result = etyFloat
  of tySet: result = etyObject # map a set to a table
  of tyString, tySequence: result = etySeq
  of tyObject, tyArray, tyTuple, tyOpenArray, tyVarargs, tyUncheckedArray:
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
    if t.n != nil: result = mapType(lastSon t)
    else: result = etyNone
  of tyProc: result = etyProc
  of tyCString: result = etyString
  of tyOptDeprecated: doAssert false

proc mangleName(es: ESGen, s: PSym): string =
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
  # disambiguation may be needed for procs
  result &= "_" & $s.id

proc escapeJSString(s: string): string =
  result = newStringOfCap(s.len + s.len shr 2)
  result.add("\"")
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
  result.add("\"")

proc makeJSString(s: string, escapeNonAscii = true): string =
  if escapeNonAscii:
    result = strutils.escape(s)
  else:
    result = escapeJSString(s)

proc gen(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode

proc genNilLit(es: ESGen, typ: PType): ESNode = 
  if isEmptyType(typ):
    discard
  elif mapType(typ) == etyBaseIndex:
    result = newArrayExpr([newESEmitExpr("null")])
  elif mapType(typ) in {etyInt, etyFloat}:
    result = newESLiteral(0)
  elif mapType(typ) in {etyFloat}:
    result = newESLiteral(0.0)
  elif mapType(typ) == etyBool:
    result = newESLiteral(false)
  else:
    result = newESEmitExpr("null")

proc genSym(es: ESGen, s: PSym, noDeref = false): ESNode =
  if s.loc.storage == OnHeap and not noDeref:
    echo es.mangleName(s), " ",s.typ.kind
    result = newMemberExpr(
      newESIdent(es.mangleName(s), s.typ.typeToString), 
      newESLiteral(0), false
    )
  else:
    result = newESIdent(es.mangleName(s), s.typ.typeToString)

proc genProc(es: ESGen, prc: PSym) =
  let res = if prc.ast.len > resultPos :prc.ast[resultPos] else: nil
  var bdy = newBlockStmt()
  if not res.isNil:
    res.sym.loc.storage = OnHeap
    bdy.add(
      newVarDecl(esLet, false,
        [newVarDeclarator(
          newESIdent(es.mangleName(res.sym), res.typ.typeToString), newArrayExpr([es.genNilLit(res.typ)])
        )]
      )
    )
  
  var trandiscarded = newBlockStmt()
  # FIXME: looks like this gen generates some wrong parts
  # added directly to the var body passed in, so we store that in
  # trandiscarded and then ignore that
  bdy.add(
    es.gen(transformBody(es.graph, prc, false), trandiscarded)
  )
  if not res.isNil:
    #if ressym.typ.kind == tyVar:
      # bdy.add(
      #   newReturnStmt(es.genSym(ressym, noDeref=true))
      # )
    #else:
      bdy.add(
        newReturnStmt(es.genSym(res.sym))
      )
  let declparams = prc.typ.n
  var params = newSeq[ESNode](declparams.len-1)
  
  for i, p in declparams:
    if i == 0: continue
    if p.sym.ast.isNil:
      params[i-1] = newESIdent(mangleName(es, p.sym), p.sym.typ.typeToString)
    else:
      params[i-1] = newVarDeclarator(newESIdent(mangleName(es, p.sym), p.sym.typ.typeToString), es.gen(p.sym.ast, bdy)) #body is wrong? 

  ESBackend(es.graph.backend).ast.add( #CHECK:ME can I use stmntbody
    newESFuncDecl(
      newESIdent(mangleName(es, prc), if res.isNil: "" else: res.typ.typeToString),
      bdy,
      params,
      card(prc.flags*{sfExported, sfExportc}) > 0
    )
  )

proc prepareMagic(es: ESGen, name: string): ESNode =
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
  let a = n[1]
  let b = n[2]
  result = newAsgnExpr(operator, es.gen(a, stmntbody), es.gen(b, stmntbody))
  if isSimpleExpr(a) and isSimpleExpr(b):
    echo "TODO: genBinaryAsgnExpr complex expr"
    # echo es.config.treeToYaml(a)
    # echo es.config.treeToYaml(b)
    # es.config.internalError("TODO: genBinaryAsgnExpr complex expr")


proc genUnaryExpr(es: ESGen, operator: string, prefix:bool, n: PNode, stmntbody: var ESNode): ESNode =
  result = newUnaryExpr(operator, prefix, es.gen(n[1], stmntbody))

  if isSimpleExpr(n[0]):
    echo "TODO: genUnaryExpr complex expr"
  # es.config.internalError("TODO: genUnaryExpr complex expr")

proc needsTemp(n: PNode): bool =
  # check if n contains a call to determine
  # if a temp should be made to prevent multiple evals
  if n.kind in nkCallKinds + {nkTupleConstr, nkObjConstr, nkBracket, nkCurly}:
    return true
  for c in n:
    if needsTemp(c):
      return true

proc magicToProc(magic: TMagic): string =
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
  else:  ""

proc genCall(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  if not es.graph.backend.ESBackend.generatedProcs.containsOrIncl(n[0].sym.id):
    es.genProc(n[0].sym)

  var args = newSeq[ESNode]()
  for i, arg in n:
    if i == 0: continue
    args.add(es.gen(arg, stmntbody))
  result = newCallExpr(
    newESIdent(mangleName(es, n[0].sym)), args
  )

proc genEcho(es: ESGen, n: PNode, stmntbody: var ESNode): ESNode =
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

  # # console.log(...arg)
    
  
proc genMagicCall(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  let esid = es.prepareMagic(magicToProc(n[0].sym.magic))
  var args = newSeq[ESNode]()
  for i, arg in n:
    if i == 0: continue
    args.add(es.gen(arg, stmntbody))
  result = newCallExpr(esid, args)

proc genMagic(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  #es.config.internalError("TODO: genMagicCall" & n[0].sym.name.s & $n[0].sym.magic)
  # TODO: checkedop
  let op = n[0].sym.magic
  case op
  of mOr: result = genBinaryExpr(es, "||", n, stmntbody)
  of mAnd: result = genBinaryExpr(es, "&&", n, stmntbody)
  of mAddU, mAddI: result = genBinaryExpr(es, "+", n, stmntbody)
  of mSubU, mSubI: result = genBinaryExpr(es, "-", n, stmntbody)
  of mMulU: result = genBinaryExpr(es, "*", n, stmntbody)
  of mDivU: result = genBinaryExpr(es, "/", n, stmntbody)
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
    mNewString, #[mAppendStrStr, mAppendStrCh, mAppendSeqElem]#: 
    result = es.genMagicCall(n, stmntbody)
  of mAppendStrStr: 
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
    echo es.config.treeToYaml(n)
    #result = es.genBinaryExpr("+", n, stmntbody)
    result = newArrayExpr()
    result.elements = newSeq[ESNode](n.len-1)
    for i, el in n:
      if i == 0: continue
      result.elements[i-1] = newUnaryExpr("...", true, es.gen(n[i], stmntbody))
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
  of mCharToStr: applyFormat("nimCharToStr($1)", "nimCharToStr($1)")
  of mBoolToStr: applyFormat("nimBoolToStr($1)", "nimBoolToStr($1)")
  of mIntToStr: applyFormat("cstrToNimstr(($1)+\"\")", "cstrToNimstr(($1)+\"\")")
  of mInt64ToStr: applyFormat("cstrToNimstr(($1)+\"\")", "cstrToNimstr(($1)+\"\")")
  of mFloatToStr:
    useMagic(p, "nimFloatToString")
    applyFormat "cstrToNimstr(nimFloatToString($1))"
  of mCStrToStr: applyFormat("cstrToNimstr($1)", "cstrToNimstr($1)")
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
  #   if mapType(n[2].typ) == etyBaseIndex:
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
  #   if mapType(n[1].typ) != etyBaseIndex:
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
    # try to generate the proc
    # if not es.graph.backend.ESBackend.generatedProcs.containsOrIncl(n[0].sym.id):
    #   es.genProc(n[0].sym)
    # result = genCall(es, n, stmntbody)
    translError(es, n):
      "genMagic: " & $op

proc genAsgn(es: ESGen, lhs, rhs: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = newExpressionStmt(
    newAsgnExpr("=", es.gen(lhs, stmntbody), es.gen(rhs, stmntbody))
  )

proc genObjTypeInfo(es: ESGen, t: PType, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  # https://nim-lang.org/docs/macros.html#statements-type-section
  var fields : seq[ESNode] = @[]
  for i, reclst in t.n:
    #echo es.config.treeToYaml(reclst)
    fields.add(es.gen(reclst, stmntbody))
  newObjTypeDecl(newESIdent(t.sym.name.s), t.sym.exportOrUsed, fields)

proc genObjConstrCall(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil) : ESNode=
  #echo es.config.treeToYaml(n)
  if n[0].kind != nkSym:
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
      args.add(es.gen(arg[1], stmntbody))
    result = newNewExpr(
      newESIdent(n[0].sym.name.s), args
    )

proc genTupleConstr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  ## var x = (x:1,x:2)
  ## let y = (1,2)
  ## becomes
  ## let x = [{"0":1,"1":2}]
  ## const y = {"0":1,"1":2}
  echo es.config.treeToYaml(n)
  var props = newSeq[ESNode]()
  if n[0].kind == nkExprColonExpr: # a named tuple
    for i, p in n:
      props.add(newProperty(es.gen(p[0], stmntbody), es.gen(p[1],stmntbody)))
      # TODO: avoid duplacting fields
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
  echo es.config.treeToYaml(n)
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
  ##   
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
  case n.kind:
  of nkCharLit..nkUInt64Lit:
    if n.typ.kind == tyBool:
      result = newESLiteral(n.intVal != 0)
    else:
      result = newESLiteral(n.intVal)
  of nkNilLit:
    result = es.genNilLit(n.typ)
  of nkStrLit..nkTripleStrLit:
    result = newESLiteral(n.strVal)
  of nkFloatLit..nkFloat64Lit:
    result = newESLiteral(n.floatVal)
  else:
    translError(es,n):
      "genLit not handled"


proc genCallOrMagic(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  echo "SYMID: ", n[0].sym.id, " name ", mangleName(es, n[0].sym)
  if (n[0].kind == nkSym) and (n[0].sym.magic != mNone):
    if isEmptyType(n.typ):  # a magic call stmt
      result = newExpressionStmt(genMagic(es, n, stmntbody))
    else: result = genMagic(es, n, stmntbody)
  elif isEmptyType(n.typ):  # a call stmt
    result = newExpressionStmt(genCall(es, n, stmntbody)) # TODO: use the fact that no result is needed
  else:
    result = genCall(es, n, stmntbody)

proc genVar(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = newBlockStmt()
  # CHECK: if v[2] is nkCallKind no need for brackets, the returned result is already a var?
  for v in n.sons:
    v[0].sym.loc.storage = OnHeap #TODO: proper fix later on...
    if v[2].kind == nkEmpty:
      result.add(
        newVarDecl(
          esLet, v[0].sym.exportOrUsed and v[0].sym.owner.kind == skModule,
          [newVarDeclarator(newESIdent(mangleName(es,v[0].sym), v[0].sym.typ.typeToString), newArrayExpr([ es.genNilLit(v[0].sym.typ) ]))]
        )
      )
    else:
      result.add(
        newVarDecl(
          esLet, v[0].sym.exportOrUsed and v[0].sym.owner.kind == skModule,
          [newVarDeclarator(newESIdent(mangleName(es, v[0].sym), v[0].sym.typ.typeToString), newArrayExpr([es.gen(v[2], stmntbody)]))]
        )
      )
proc genLet(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = newBlockStmt()
  for v in n.sons:
    result.add(
      newVarDecl(
        esConst, v[0].sym.exportOrUsed and v[0].sym.owner.kind == skModule,
        [newVarDeclarator(newESIdent(mangleName(es, v[0].sym), v[0].sym.typ.typeToString), es.gen(v[2], stmntbody))]
      )
    )

proc genStmtListExpr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  #TODO: use https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Comma_Operator
  for i, son in n.sons:
    if i == n.sons.len-1:
      result = es.gen(son,stmntbody)
    stmntbody.add(es.gen(son,stmntbody))

proc genStmtList(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =  
  result = newBlockStmt()
  for son in n.sons:
    result.add(es.gen(son,stmntbody))

proc genBracket(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =  
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

proc genBracketExpr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  echo es.config.treeToYaml(n)
  result = newMemberExpr(es.gen(n[0], stmntbody), es.gen(n[1], stmntbody), false)

proc genWhileLoopStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = newWhileStmt(
    es.gen(n[0], stmntbody),
    es.gen(n[1], stmntbody)
  )

proc genBlockStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = newLabeledStmt(
    newESIdent(mangleName(es, n[0].sym) & $n[0].sym.id),
    es.gen(n[1], stmntbody)
  )

proc genConst(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = newBlockStmt()
  for c in n.sons:
    if c[0].sym.exportOrUsed and c[0].sym.owner.kind == skModule:
      result.add(
        newVarDecl(
          esConst, c[0].sym.exportOrUsed and c[0].sym.owner.kind == skModule,
          [newVarDeclarator(newESIdent(mangleName(es, c[0].sym), c[0].sym.typ.typeToString), es.gen(c[2], stmntbody))]
        )
      )
  if result.len == 0:
      result = newEmptyStmt()

proc genAddr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  if n[0].kind == nkSym:
    result = newArrayExpr([
      es.genSym(n[0].sym, noDeref=true), newESLiteral(0)
    ])
  else:
    result = newArrayExpr([
      es.gen(n[0], stmntbody), newESLiteral(0)
    ])

proc genDeref(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  let ident = es.gen(n[0], stmntbody)
  result = newMemberExpr(
    newMemberExpr(ident, newESLiteral(0), false),
    newMemberExpr(ident, newESLiteral(1), false),
    false
  )

proc genIfStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
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

proc genDotExpr(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  echo es.config.treeToYaml(n)
  result = newMemberExpr(
    es.gen(n[0],stmntbody), es.gen(n[1],stmntbody), true
  )

proc genPragma(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  #echo es.config.treeToYaml(n)
  let maybeEmit = n.getPragmaStmt(wEmit)
  if not maybeEmit.isNil:
    #echo es.config.treeToYaml(maybeEmit)
    var emitstr: string = ""
    for el in maybeEmit[1]: # [0] is !"emit"
      if el.kind == nkStrLit: emitstr.add(el.getStr)
      elif el.kind == nkIdent: 
        emitstr.add(el.ident.s) # TODO: mangling?
      elif el.kind == nkSym:
        emitstr.add(mangleName(es, el.sym))
      else: discard
    result = newESEmitExpr(emitstr)
  else: 
    echo es.config.treeToYaml(n)
    translError(es, n, "unhandled pragma")

proc genAsm(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  var emitstr: string = ""
  #echo es.config.treeToYaml(n)
  for el in n: # [0] is !"emit"
    if el.kind == nkStrLit: emitstr.add(el.getStr)
    elif el.kind == nkIdent: 
      emitstr.add(el.ident.s) # TODO: mangling?
    elif el.kind == nkSym:
      emitstr.add(mangleName(es, el.sym))
    else: discard
  result = newESEmitExpr(emitstr)

proc genRaise(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  let id = es.prepareMagic("raiseException")
  result = newCallExpr(id, es.gen(n[0],stmntbody))

proc genStringToCString(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  let id = es.prepareMagic("esNimStrToJsStr")
  result = newCallExpr(id, es.gen(n[0],stmntbody))

proc genReturnStmt(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = newReturnStmt(es.gen(n[1], stmntbody))

proc genConv(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  result = es.gen(n[1], stmntbody)#TODO: figure out conv of non basic types?

proc gen(es: ESGen, n: PNode, stmntbody: var ESNode, loc: SourceLocation = nil): ESNode =
  echo "# gen: ", $n.kind, " module: ", es.config.toFilename(n.info.fileIndex)
  echo "# working on: ", n.kind
  if not (n.kind == nkStmtList):
    echo renderTree(n)
    
  case n.kind:
  of nkGenSkippedKinds: result = newEmptyStmt() # returns ';'
  of nkSym:
    result = es.genSym(n.sym)
  of nkLiterals:
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
    if n.typ.isNil: es.translError(n, "Empty type for nkobjconstr")
    result = es.genObjConstrCall(n, stmntbody)
  of nkAddr, nkHiddenAddr:
    result = es.genAddr(n, stmntbody)
  of nkIfStmt:
    result = es.genIfStmt(n, stmntbody)
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
    # TODO:
    result= es.gen(n.lastSon,stmntbody)
  of nkAsmStmt:
    result = es.genAsm(n, stmntbody)
  of nkRaiseStmt:
    result = es.genRaise(n, stmntbody)
  of nkConv, nkHiddenStdConv:
    result = es.genConv(n, stmntbody)
  of nkStringToCString:
    result = es.genStringToCString(n, stmntbody)
  of nkReturnStmt:
    result = es.genReturnStmt(n, stmntbody)
  else: 
    echo es.config.treeToYaml(n)
    translError(es, n, "gen: unknown node kind")

  #[
  of nkClosure:
  of nkCurly:
  of nkPar:
  of nkHiddenStdConv, nkHiddenSubConv, nkConv:
  of nkCheckedFieldExpr:
  of nkObjDownConv:
  of nkObjUpConv:
  of nkCast:
  of nkChckRangeF:
  of nkChckRange64:
  of nkChckRange:
  of nkCStringToString:
  of nkEmpty:
  of nkLambdaKinds
  of nkType:
  of nkBlockExpr:
  of nkIfExpr:
  of nkBreakStmt:
  of nkDiscardStmt
  of nkTryStmt, nkHiddenTryStmt:
  ]#

proc myProcess(b: PPassContext, n: PNode): PNode =
  result = n
  let m = ESGen(b)
  if passes.skipCodegen(m.config, n): return n
  if m.module == nil: internalError(m.config, n.info, "esgen:myProcess")
  let es = ESBackend(m.graph.backend)
  
  if es.ast.mname notin toFilename(m.config, n.info): return # FIXME: this skippes everything not coming from mainmodule
  var transfN = transformStmt(m.graph,m.module,n)
  if transfN.kind in nkGenSkippedKinds: return

  if not (transfN.kind == nkStmtList):
    es.ast.add(m.gen(transfN, es.ast))
  else:
    for stmt in transfN:
      es.ast.add(m.gen(stmt, es.ast))

proc myClose(graph: ModuleGraph; b: PPassContext, n: PNode): PNode =
  if passes.skipCodegen(graph.config, n): return n
  result = myProcess(b, n)
  # TODO: select ES6 vs UMD style module and exports/imports, pass it to render
  var m = ESGen(b)
  let es = ESBackend(m.graph.backend)
  if sfMainModule in m.module.flags:
    let outFile = m.config.prepareToWriteOutput()
    writeFile($outFile, es.ast.render())

proc myOpen(graph: ModuleGraph; s: PSym): PPassContext =
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