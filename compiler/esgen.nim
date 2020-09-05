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
"""

import
  ast, astalgo, trees, magicsys, options,
  nversion, msgs, idents, types,
  ropes, passes, ccgutils, wordrecg, renderer,
  cgmeth, lowerings, sighashes, pathutils,
  lineinfos, rodutils, transf, injectdestructors, sourcemap

import strutils, intsets
from math import classify

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
    tmpcounter: int

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

proc hasProc(b: ESBackend, s: PSym): bool =
  b.generatedProcs.contains(s.id)

proc hasTypeInfo(b: ESBackend, s: PSym): bool =
  b.generatedTypeInfos.contains(s.id)

proc newBackend(): ESBackend =
  new(result)
  result.ast = newESModule(":codegen-temp-module")
  result.generatedProcs = initIntSet()
  result.generatedTypeInfos = initIntSet()

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


const nkGenSkippedKinds = { nkCommentStmt, nkPragma, nkEmpty, 
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

proc mangleName(m: ESGen, s: PSym): Rope =
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
  result = s.loc.r
  if result == nil:
    if s.kind == skField and s.name.s.validJsName:
      result = rope(s.name.s)
    elif s.kind == skTemp:
      result = rope(mangle(s.name.s))
    else:
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
      result = rope(x)
    # From ES5 on reserved words can be used as object field names
    if s.kind != skField:
        result.add("_")
        result.add(rope(s.id))
    s.loc.r = result

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

proc gen(es: ESGen, n: PNode, piece: var ESNode, loc: SourceLocation = nil): ESNode

#[
proc genTypeInfo(p: PProc, typ: PType): Rope
proc genObjectFields(p: PProc, typ: PType, n: PNode): Rope =
  var
    s, u: Rope
    field: PSym
    b: PNode
  result = nil
  case n.kind
  of nkRecList:
    if n.len == 1:
      result = genObjectFields(p, typ, n[0])
    else:
      s = nil
      for i in 0..<n.len:
        if i > 0: s.add(", \L")
        s.add(genObjectFields(p, typ, n[i]))
      result = ("{kind: 2, len: $1, offset: 0, " &
          "typ: null, name: null, sons: [$2]}") % [rope(n.len), s]
  of nkSym:
    field = n.sym
    s = genTypeInfo(p, field.typ)
    result = ("{kind: 1, offset: \"$1\", len: 0, " &
        "typ: $2, name: $3, sons: null}") %
                   [mangleName(p.module, field), s,
                    makeJSString(field.name.s)]
  of nkRecCase:
    if (n[0].kind != nkSym): internalError(p.config, n.info, "genObjectFields")
    field = n[0].sym
    s = genTypeInfo(p, field.typ)
    for i in 1..<n.len:
      b = n[i]           # branch
      u = nil
      case b.kind
      of nkOfBranch:
        if b.len < 2:
          internalError(p.config, b.info, "genObjectFields; nkOfBranch broken")
        for j in 0..<b.len - 1:
          if u != nil: u.add(", ")
          if b[j].kind == nkRange:
            u.addf("[$1, $2]", [rope(getOrdValue(b[j][0])),
                                 rope(getOrdValue(b[j][1]))])
          else:
            u.add(rope(getOrdValue(b[j])))
      of nkElse:
        u = rope(lengthOrd(p.config, field.typ))
      else: internalError(p.config, n.info, "genObjectFields(nkRecCase)")
      if result != nil: result.add(", \L")
      result.addf("[setConstr($1), $2]",
           [u, genObjectFields(p, typ, lastSon(b))])
    result = ("{kind: 3, offset: \"$1\", len: $3, " &
        "typ: $2, name: $4, sons: [$5]}") % [
        mangleName(p.module, field), s,
        rope(lengthOrd(p.config, field.typ)), makeJSString(field.name.s), result]
  else: internalError(p.config, n.info, "genObjectFields")

proc objHasTypeField(t: PType): bool {.inline.} =
  tfInheritable in t.flags or t[0] != nil

proc genObjectInfo(p: PProc, typ: PType, name: Rope) =
  let kind = if objHasTypeField(typ): tyObject else: tyTuple
  var s = ("var $1 = {size: 0, kind: $2, base: null, node: null, " &
           "finalizer: null};$n") % [name, rope(ord(kind))]
  prepend(p.g.typeInfo, s)
  p.g.typeInfo.addf("var NNI$1 = $2;$n",
       [rope(typ.id), genObjectFields(p, typ, typ.n)])
  p.g.typeInfo.addf("$1.node = NNI$2;$n", [name, rope(typ.id)])
  if (typ.kind == tyObject) and (typ[0] != nil):
    p.g.typeInfo.addf("$1.base = $2;$n",
         [name, genTypeInfo(p, typ[0].skipTypes(skipPtrs))])

proc genTupleFields(p: PProc, typ: PType): Rope =
  var s: Rope = nil
  for i in 0..<typ.len:
    if i > 0: s.add(", \L")
    s.addf("{kind: 1, offset: \"Field$1\", len: 0, " &
           "typ: $2, name: \"Field$1\", sons: null}",
           [i.rope, genTypeInfo(p, typ[i])])
  result = ("{kind: 2, len: $1, offset: 0, " &
            "typ: null, name: null, sons: [$2]}") % [rope(typ.len), s]

proc genTupleInfo(p: PProc, typ: PType, name: Rope) =
  var s = ("var $1 = {size: 0, kind: $2, base: null, node: null, " &
           "finalizer: null};$n") % [name, rope(ord(typ.kind))]
  prepend(p.g.typeInfo, s)
  p.g.typeInfo.addf("var NNI$1 = $2;$n",
       [rope(typ.id), genTupleFields(p, typ)])
  p.g.typeInfo.addf("$1.node = NNI$2;$n", [name, rope(typ.id)])

proc genEnumInfo(p: PProc, typ: PType, name: Rope) =
  var s: Rope = nil
  for i in 0..<typ.n.len:
    if (typ.n[i].kind != nkSym): internalError(p.config, typ.n.info, "genEnumInfo")
    let field = typ.n[i].sym
    if i > 0: s.add(", \L")
    let extName = if field.ast == nil: field.name.s else: field.ast.strVal
    s.addf("\"$1\": {kind: 1, offset: $1, typ: $2, name: $3, len: 0, sons: null}",
         [rope(field.position), name, makeJSString(extName)])
  var n = ("var NNI$1 = {kind: 2, offset: 0, typ: null, " &
      "name: null, len: $2, sons: {$3}};$n") % [rope(typ.id), rope(typ.n.len), s]
  s = ("var $1 = {size: 0, kind: $2, base: null, node: null, " &
       "finalizer: null};$n") % [name, rope(ord(typ.kind))]
  prepend(p.g.typeInfo, s)
  p.g.typeInfo.add(n)
  p.g.typeInfo.addf("$1.node = NNI$2;$n", [name, rope(typ.id)])
  if typ[0] != nil:
    p.g.typeInfo.addf("$1.base = $2;$n",
         [name, genTypeInfo(p, typ[0])])

proc genTypeInfo(p: PProc, typ: PType): Rope =
  let t = typ.skipTypes({tyGenericInst, tyDistinct, tyAlias, tySink, tyOwned})
  result = "NTI$1" % [rope(t.id)]
  if containsOrIncl(p.g.typeInfoGenerated, t.id): return
  case t.kind
  of tyDistinct:
    result = genTypeInfo(p, t[0])
  of tyPointer, tyProc, tyBool, tyChar, tyCString, tyString, tyInt..tyUInt64:
    var s =
      "var $1 = {size: 0,kind: $2,base: null,node: null,finalizer: null};$n" %
      [result, rope(ord(t.kind))]
    prepend(p.g.typeInfo, s)
  of tyVar, tyLent, tyRef, tyPtr, tySequence, tyRange, tySet:
    var s =
      "var $1 = {size: 0,kind: $2,base: null,node: null,finalizer: null};$n" %
              [result, rope(ord(t.kind))]
    prepend(p.g.typeInfo, s)
    p.g.typeInfo.addf("$1.base = $2;$n",
         [result, genTypeInfo(p, t.lastSon)])
  of tyArray:
    var s =
      "var $1 = {size: 0,kind: $2,base: null,node: null,finalizer: null};$n" %
              [result, rope(ord(t.kind))]
    prepend(p.g.typeInfo, s)
    p.g.typeInfo.addf("$1.base = $2;$n",
         [result, genTypeInfo(p, t[1])])
  of tyEnum: genEnumInfo(p, t, result)
  of tyObject: genObjectInfo(p, t, result)
  of tyTuple: genTupleInfo(p, t, result)
  of tyStatic:
    if t.n != nil: result = genTypeInfo(p, lastSon t)
    else: internalError(p.config, "genTypeInfo(" & $t.kind & ')')
  else: internalError(p.config, "genTypeInfo(" & $t.kind & ')')


proc gen(p: PProc, n: PNode, r: var TCompRes)
proc genStmt(p: PProc, n: PNode)
proc genProc(oldProc: PProc, prc: PSym): Rope
proc genConstant(p: PProc, c: PSym)


proc hasFrameInfo(p: PProc): bool =
  ({optLineTrace, optStackTrace} * p.options == {optLineTrace, optStackTrace}) and
      ((p.prc == nil) or not (sfPure in p.prc.flags))

proc lineDir(config: ConfigRef, info: TLineInfo, line: int): Rope =
  ropes.`%`("// line $2 \"$1\"$n",
         [rope(toFullPath(config, info)), rope(line)])

proc genLineDir(p: PProc, n: PNode) =
  let line = toLinenumber(n.info)
  if line < 0:
    return
  if optLineDir in p.options or optLineDir in p.config.options:
    lineF(p, "$1", [lineDir(p.config, n.info, line)])
  if hasFrameInfo(p):
    lineF(p, "F.line = $1;$n", [rope(line)])

proc genWhileStmt(p: PProc, n: PNode) =
  var cond: TCompRes
  internalAssert p.config, isEmptyType(n.typ)
  genLineDir(p, n)
  inc(p.unique)
  setLen(p.blocks, p.blocks.len + 1)
  p.blocks[^1].id = -p.unique
  p.blocks[^1].isLoop = true
  let labl = p.unique.rope
  lineF(p, "L$1: while (true) {$n", [labl])
  p.nested: gen(p, n[0], cond)
  lineF(p, "if (!$1) break L$2;$n",
       [cond.res, labl])
  p.nested: genStmt(p, n[1])
  lineF(p, "}$n", [labl])
  setLen(p.blocks, p.blocks.len - 1)

proc moveInto(p: PProc, src: var TCompRes, dest: TCompRes) =
  if src.kind != resNone:
    if dest.kind != resNone:
      lineF(p, "$1 = $2;$n", [dest.rdLoc, src.rdLoc])
    else:
      lineF(p, "$1;$n", [src.rdLoc])
    src.kind = resNone
    src.res = nil

proc genTry(p: PProc, n: PNode, r: var TCompRes) =
  # code to generate:
  #
  #  ++excHandler;
  #  var tmpFramePtr = framePtr;
  #  try {
  #    stmts;
  #    --excHandler;
  #  } catch (EXC) {
  #    var prevJSError = lastJSError; lastJSError = EXC;
  #    framePtr = tmpFramePtr;
  #    --excHandler;
  #    if (e.typ && e.typ == NTI433 || e.typ == NTI2321) {
  #      stmts;
  #    } else if (e.typ && e.typ == NTI32342) {
  #      stmts;
  #    } else {
  #      stmts;
  #    }
  #    lastJSError = prevJSError;
  #  } finally {
  #    framePtr = tmpFramePtr;
  #    stmts;
  #  }
  genLineDir(p, n)
  if not isEmptyType(n.typ):
    r.kind = resVal
    r.res = getTemp(p)
  inc(p.unique)
  var i = 1
  var catchBranchesExist = n.len > 1 and n[i].kind == nkExceptBranch
  if catchBranchesExist:
    p.body.add("++excHandler;\L")
  var tmpFramePtr = rope"F"
  if optStackTrace notin p.options:
    tmpFramePtr = p.getTemp(true)
    line(p, tmpFramePtr & " = framePtr;\L")
  lineF(p, "try {$n", [])
  var a: TCompRes
  gen(p, n[0], a)
  moveInto(p, a, r)
  var generalCatchBranchExists = false
  if catchBranchesExist:
    p.body.addf("--excHandler;$n} catch (EXC) {$n var prevJSError = lastJSError;$n" &
        " lastJSError = EXC;$n --excHandler;$n", [])
    line(p, "framePtr = $1;$n" % [tmpFramePtr])
  while i < n.len and n[i].kind == nkExceptBranch:
    if n[i].len == 1:
      # general except section:
      generalCatchBranchExists = true
      if i > 1: lineF(p, "else {$n", [])
      gen(p, n[i][0], a)
      moveInto(p, a, r)
      if i > 1: lineF(p, "}$n", [])
    else:
      var orExpr: Rope = nil
      var excAlias: PNode = nil

      useMagic(p, "isObj")
      for j in 0..<n[i].len - 1:
        var throwObj: PNode
        let it = n[i][j]

        if it.isInfixAs():
          throwObj = it[1]
          excAlias = it[2]
          # If this is a ``except exc as sym`` branch there must be no following
          # nodes
          doAssert orExpr == nil
        elif it.kind == nkType:
          throwObj = it
        else:
          internalError(p.config, n.info, "genTryStmt")

        if orExpr != nil: orExpr.add("||")
        # Generate the correct type checking code depending on whether this is a
        # NIM-native or a JS-native exception
        # if isJsObject(throwObj.typ):
        if isImportedException(throwObj.typ, p.config):
          orExpr.addf("lastJSError instanceof $1",
            [throwObj.typ.sym.loc.r])
        else:
          orExpr.addf("isObj(lastJSError.m_type, $1)",
               [genTypeInfo(p, throwObj.typ)])

      if i > 1: line(p, "else ")
      lineF(p, "if (lastJSError && ($1)) {$n", [orExpr])
      # If some branch requires a local alias introduce it here. This is needed
      # since JS cannot do ``catch x as y``.
      if excAlias != nil:
        excAlias.sym.loc.r = mangleName(p.module, excAlias.sym)
        lineF(p, "var $1 = lastJSError;$n", excAlias.sym.loc.r)
      gen(p, n[i][^1], a)
      moveInto(p, a, r)
      lineF(p, "}$n", [])
    inc(i)
  if catchBranchesExist:
    if not generalCatchBranchExists:
      useMagic(p, "reraiseException")
      line(p, "else {\L")
      line(p, "\treraiseException();\L")
      line(p, "}\L")
    lineF(p, "lastJSError = prevJSError;$n")
  line(p, "} finally {\L")
  line(p, "framePtr = $1;$n" % [tmpFramePtr])
  if i < n.len and n[i].kind == nkFinally:
    genStmt(p, n[i][0])
  line(p, "}\L")

proc genRaiseStmt(p: PProc, n: PNode) =
  if n[0].kind != nkEmpty:
    var a: TCompRes
    gen(p, n[0], a)
    let typ = skipTypes(n[0].typ, abstractPtrs)
    genLineDir(p, n)
    useMagic(p, "raiseException")
    lineF(p, "raiseException($1, $2);$n",
             [a.rdLoc, makeJSString(typ.sym.name.s)])
  else:
    genLineDir(p, n)
    useMagic(p, "reraiseException")
    line(p, "reraiseException();\L")

proc genCaseJS(p: PProc, n: PNode, r: var TCompRes) =
  var
    cond, stmt: TCompRes
  genLineDir(p, n)
  gen(p, n[0], cond)
  let stringSwitch = skipTypes(n[0].typ, abstractVar).kind == tyString
  if stringSwitch:
    useMagic(p, "toJSStr")
    lineF(p, "switch (toJSStr($1)) {$n", [cond.rdLoc])
  else:
    lineF(p, "switch ($1) {$n", [cond.rdLoc])
  if not isEmptyType(n.typ):
    r.kind = resVal
    r.res = getTemp(p)
  for i in 1..<n.len:
    let it = n[i]
    case it.kind
    of nkOfBranch:
      for j in 0..<it.len - 1:
        let e = it[j]
        if e.kind == nkRange:
          var v = copyNode(e[0])
          while v.intVal <= e[1].intVal:
            gen(p, v, cond)
            lineF(p, "case $1:$n", [cond.rdLoc])
            inc(v.intVal)
        else:
          if stringSwitch:
            case e.kind
            of nkStrLit..nkTripleStrLit: lineF(p, "case $1:$n",
                [makeJSString(e.strVal, false)])
            else: internalError(p.config, e.info, "jsgen.genCaseStmt: 2")
          else:
            gen(p, e, cond)
            lineF(p, "case $1:$n", [cond.rdLoc])
      p.nested:
        gen(p, lastSon(it), stmt)
        moveInto(p, stmt, r)
        lineF(p, "break;$n", [])
    of nkElse:
      lineF(p, "default: $n", [])
      p.nested:
        gen(p, it[0], stmt)
        moveInto(p, stmt, r)
        lineF(p, "break;$n", [])
    else: internalError(p.config, it.info, "jsgen.genCaseStmt")
  lineF(p, "}$n", [])

proc genBlock(p: PProc, n: PNode, r: var TCompRes) =
  inc(p.unique)
  let idx = p.blocks.len
  if n[0].kind != nkEmpty:
    # named block?
    if (n[0].kind != nkSym): internalError(p.config, n.info, "genBlock")
    var sym = n[0].sym
    sym.loc.k = locOther
    sym.position = idx+1
  let labl = p.unique
  lineF(p, "L$1: do {$n", [labl.rope])
  setLen(p.blocks, idx + 1)
  p.blocks[idx].id = - p.unique # negative because it isn't used yet
  gen(p, n[1], r)
  setLen(p.blocks, idx)
  lineF(p, "} while(false);$n", [labl.rope])

proc genBreakStmt(p: PProc, n: PNode) =
  var idx: int
  genLineDir(p, n)
  if n[0].kind != nkEmpty:
    # named break?
    assert(n[0].kind == nkSym)
    let sym = n[0].sym
    assert(sym.loc.k == locOther)
    idx = sym.position-1
  else:
    # an unnamed 'break' can only break a loop after 'transf' pass:
    idx = p.blocks.len - 1
    while idx >= 0 and not p.blocks[idx].isLoop: dec idx
    if idx < 0 or not p.blocks[idx].isLoop:
      internalError(p.config, n.info, "no loop to break")
  p.blocks[idx].id = abs(p.blocks[idx].id) # label is used
  lineF(p, "break L$1;$n", [rope(p.blocks[idx].id)])

proc genAsmOrEmitStmt(p: PProc, n: PNode) =
  genLineDir(p, n)
  p.body.add p.indentLine(nil)
  for i in 0..<n.len:
    let it = n[i]
    case it.kind
    of nkStrLit..nkTripleStrLit:
      p.body.add(it.strVal)
    of nkSym:
      let v = it.sym
      # for backwards compatibility we don't deref syms here :-(
      if false:
        discard
      else:
        var r: TCompRes
        gen(p, it, r)

        if it.typ.kind == tyPointer:
          # A fat pointer is disguised as an array
          r.res = r.address
          r.address = nil
          r.typ = etyNone
        elif r.typ == etyBaseIndex:
          # Deference first
          r.res = "$1[$2]" % [r.address, r.res]
          r.address = nil
          r.typ = etyNone

        p.body.add(r.rdLoc)
    else:
      var r: TCompRes
      gen(p, it, r)
      p.body.add(r.rdLoc)
  p.body.add "\L"

proc genIf(p: PProc, n: PNode, r: var TCompRes) =
  var cond, stmt: TCompRes
  var toClose = 0
  if not isEmptyType(n.typ):
    r.kind = resVal
    r.res = getTemp(p)
  for i in 0..<n.len:
    let it = n[i]
    if it.len != 1:
      if i > 0:
        lineF(p, "else {$n", [])
        inc(toClose)
      p.nested: gen(p, it[0], cond)
      lineF(p, "if ($1) {$n", [cond.rdLoc])
      gen(p, it[1], stmt)
    else:
      # else part:
      lineF(p, "else {$n", [])
      p.nested: gen(p, it[0], stmt)
    moveInto(p, stmt, r)
    lineF(p, "}$n", [])
  line(p, repeat('}', toClose) & "\L")

proc generateHeader(p: PProc, typ: PType): Rope =
  result = nil
  for i in 1..<typ.n.len:
    assert(typ.n[i].kind == nkSym)
    var param = typ.n[i].sym
    if isCompileTimeOnly(param.typ): continue
    if result != nil: result.add(", ")
    var name = mangleName(p.module, param)
    result.add(name)
    if mapType(param.typ) == etyBaseIndex:
      result.add(", ")
      result.add(name)
      result.add("_Idx")

proc countJsParams(typ: PType): int =
  for i in 1..<typ.n.len:
    assert(typ.n[i].kind == nkSym)
    var param = typ.n[i].sym
    if isCompileTimeOnly(param.typ): continue
    if mapType(param.typ) == etyBaseIndex:
      inc result, 2
    else:
      inc result

const
  nodeKindsNeedNoCopy = {nkCharLit..nkInt64Lit, nkStrLit..nkTripleStrLit,
    nkFloatLit..nkFloat64Lit, nkPar, nkStringToCString,
    nkObjConstr, nkTupleConstr, nkBracket,
    nkCStringToString, nkCall, nkPrefix, nkPostfix, nkInfix,
    nkCommand, nkHiddenCallConv, nkCallStrLit}

proc needsNoCopy(p: PProc; y: PNode): bool =
  return y.kind in nodeKindsNeedNoCopy or
        ((mapType(y.typ) != etyBaseIndex or (y.kind == nkSym and y.sym.kind == skParam)) and
          (skipTypes(y.typ, abstractInst).kind in
            {tyRef, tyPtr, tyLent, tyVar, tyCString, tyProc, tyOwned} + IntegralTypes))

proc genAsgnAux(p: PProc, x, y: PNode, noCopyNeeded: bool) =
  var a, b: TCompRes
  var xtyp = mapType(p, x.typ)

  gen(p, x, a)
  genLineDir(p, y)
  gen(p, y, b)

  # we don't care if it's an etyBaseIndex (global) of a string, it's
  # still a string that needs to be copied properly:
  if x.typ.skipTypes(abstractInst).kind in {tySequence, tyString}:
    xtyp = etySeq
  case xtyp
  of etySeq:
    if (needsNoCopy(p, y) and needsNoCopy(p, x)) or noCopyNeeded:
      lineF(p, "$1 = $2;$n", [a.rdLoc, b.rdLoc])
    else:
      useMagic(p, "nimCopy")
      lineF(p, "$1 = nimCopy(null, $2, $3);$n",
               [a.rdLoc, b.res, genTypeInfo(p, y.typ)])
  of etyObject:
    if x.typ.kind in {tyVar} or (needsNoCopy(p, y) and needsNoCopy(p, x)) or noCopyNeeded:
      lineF(p, "$1 = $2;$n", [a.rdLoc, b.rdLoc])
    else:
      useMagic(p, "nimCopy")
      lineF(p, "nimCopy($1, $2, $3);$n",
               [a.res, b.res, genTypeInfo(p, y.typ)])
  of etyBaseIndex:
    if a.typ != etyBaseIndex or b.typ != etyBaseIndex:
      if y.kind == nkCall:
        let tmp = p.getTemp(false)
        lineF(p, "var $1 = $4; $2 = $1[0]; $3 = $1[1];$n", [tmp, a.address, a.res, b.rdLoc])
      elif b.typ == etyBaseIndex:
        lineF(p, "$# = [$#, $#];$n", [a.res, b.address, b.res])
      elif b.typ == etyNone:
        internalAssert p.config, b.address == nil
        lineF(p, "$# = [$#, 0];$n", [a.address, b.res])
      elif x.typ.kind == tyVar and y.typ.kind == tyPtr:
        lineF(p, "$# = [$#, $#];$n", [a.res, b.address, b.res])
        lineF(p, "$1 = $2;$n", [a.address, b.res])
        lineF(p, "$1 = $2;$n", [a.rdLoc, b.rdLoc])
      else:
        internalError(p.config, x.info, $("genAsgn", b.typ, a.typ))
    else:
      lineF(p, "$1 = $2; $3 = $4;$n", [a.address, b.address, a.res, b.res])
  else:
    lineF(p, "$1 = $2;$n", [a.rdLoc, b.rdLoc])

proc genAsgn(p: PProc, n: PNode) =
  genAsgnAux(p, n[0], n[1], noCopyNeeded=false)

proc genFastAsgn(p: PProc, n: PNode) =
  # 'shallowCopy' always produced 'noCopyNeeded = true' here but this is wrong
  # for code like
  #  while j >= pos:
  #    dest[i].shallowCopy(dest[j])
  # See bug #5933. So we try to be more compatible with the C backend semantics
  # here for 'shallowCopy'. This is an educated guess and might require further
  # changes later:
  let noCopy = n[0].typ.skipTypes(abstractInst).kind in {tySequence, tyString}
  genAsgnAux(p, n[0], n[1], noCopyNeeded=noCopy)

proc genSwap(p: PProc, n: PNode) =
  var a, b: TCompRes
  gen(p, n[1], a)
  gen(p, n[2], b)
  var tmp = p.getTemp(false)
  if mapType(p, skipTypes(n[1].typ, abstractVar)) == etyBaseIndex:
    let tmp2 = p.getTemp(false)
    if a.typ != etyBaseIndex or b.typ != etyBaseIndex:
      internalError(p.config, n.info, "genSwap")
    lineF(p, "var $1 = $2; $2 = $3; $3 = $1;$n",
             [tmp, a.address, b.address])
    tmp = tmp2
  lineF(p, "var $1 = $2; $2 = $3; $3 = $1;",
           [tmp, a.res, b.res])

proc getFieldPosition(p: PProc; f: PNode): int =
  case f.kind
  of nkIntLit..nkUInt64Lit: result = int(f.intVal)
  of nkSym: result = f.sym.position
  else: internalError(p.config, f.info, "genFieldPosition")

proc genFieldAddr(p: PProc, n: PNode, r: var TCompRes) =
  var a: TCompRes
  r.typ = etyBaseIndex
  let b = if n.kind == nkHiddenAddr: n[0] else: n
  gen(p, b[0], a)
  if skipTypes(b[0].typ, abstractVarRange).kind == tyTuple:
    r.res = makeJSString("Field" & $getFieldPosition(p, b[1]))
  else:
    if b[1].kind != nkSym: internalError(p.config, b[1].info, "genFieldAddr")
    var f = b[1].sym
    if f.loc.r == nil: f.loc.r = mangleName(p.module, f)
    r.res = makeJSString($f.loc.r)
  internalAssert p.config, a.typ != etyBaseIndex
  r.address = a.res
  r.kind = resExpr

proc genFieldAccess(p: PProc, n: PNode, r: var TCompRes) =
  gen(p, n[0], r)
  r.typ = mapType(n.typ)
  let otyp = skipTypes(n[0].typ, abstractVarRange)

  template mkTemp(i: int) =
    if r.typ == etyBaseIndex:
      if needsTemp(p, n[i]):
        let tmp = p.getTemp
        r.address = "($1 = $2, $1)[0]" % [tmp, r.res]
        r.res = "$1[1]" % [tmp]
        r.tmpLoc = tmp
      else:
        r.address = "$1[0]" % [r.res]
        r.res = "$1[1]" % [r.res]
  if otyp.kind == tyTuple:
    r.res = ("$1.Field$2") %
        [r.res, getFieldPosition(p, n[1]).rope]
    mkTemp(0)
  else:
    if n[1].kind != nkSym: internalError(p.config, n[1].info, "genFieldAccess")
    var f = n[1].sym
    if f.loc.r == nil: f.loc.r = mangleName(p.module, f)
    r.res = "$1.$2" % [r.res, f.loc.r]
    mkTemp(1)
  r.kind = resExpr

proc genAddr(p: PProc, n: PNode, r: var TCompRes)

proc genCheckedFieldOp(p: PProc, n: PNode, addrTyp: PType, r: var TCompRes) =
  internalAssert p.config, n.kind == nkCheckedFieldExpr
  # nkDotExpr to access the requested field
  let accessExpr = n[0]
  # nkCall to check if the discriminant is valid
  var checkExpr = n[1]

  let negCheck = checkExpr[0].sym.magic == mNot
  if negCheck:
    checkExpr = checkExpr[^1]

  # Field symbol
  var field = accessExpr[1].sym
  internalAssert p.config, field.kind == skField
  if field.loc.r == nil: field.loc.r = mangleName(p.module, field)
  # Discriminant symbol
  let disc = checkExpr[2].sym
  internalAssert p.config, disc.kind == skField
  if disc.loc.r == nil: disc.loc.r = mangleName(p.module, disc)

  var setx: TCompRes
  gen(p, checkExpr[1], setx)

  var obj: TCompRes
  gen(p, accessExpr[0], obj)
  # Avoid evaluating the LHS twice (one to read the discriminant and one to read
  # the field)
  let tmp = p.getTemp()
  lineF(p, "var $1 = $2;$n", tmp, obj.res)

  useMagic(p, "raiseFieldError")
  useMagic(p, "makeNimstrLit")
  let msg = genFieldDefect(field, disc)
  lineF(p, "if ($1[$2.$3]$4undefined) { raiseFieldError(makeNimstrLit($5)); }$n",
    setx.res, tmp, disc.loc.r, if negCheck: ~"!==" else: ~"===",
    makeJSString(msg))

  if addrTyp != nil and mapType(p, addrTyp) == etyBaseIndex:
    r.typ = etyBaseIndex
    r.res = makeJSString($field.loc.r)
    r.address = tmp
  else:
    r.typ = etyNone
    r.res = "$1.$2" % [tmp, field.loc.r]
  r.kind = resExpr

proc genArrayAddr(p: PProc, n: PNode, r: var TCompRes) =
  var
    a, b: TCompRes
    first: Int128
  r.typ = etyBaseIndex
  let m = if n.kind == nkHiddenAddr: n[0] else: n
  gen(p, m[0], a)
  gen(p, m[1], b)
  #internalAssert p.config, a.typ != etyBaseIndex and b.typ != etyBaseIndex
  let (x, tmp) = maybeMakeTemp(p, m[0], a)
  r.address = x
  var typ = skipTypes(m[0].typ, abstractPtrs)
  if typ.kind == tyArray:
    first = firstOrd(p.config, typ[0])
  if optBoundsCheck in p.options:
    useMagic(p, "chckIndx")
    if first == 0: # save a couple chars
      r.res = "chckIndx($1, 0, ($2).length-1)" % [b.res, tmp]
    else:
      r.res = "chckIndx($1, $2, ($3).length+($2)-1)-($2)" % [
        b.res, rope(first), tmp]
  elif first != 0:
    r.res = "($1)-($2)" % [b.res, rope(first)]
  else:
    r.res = b.res
  r.kind = resExpr

proc genArrayAccess(p: PProc, n: PNode, r: var TCompRes) =
  var ty = skipTypes(n[0].typ, abstractVarRange)
  if ty.kind in {tyRef, tyPtr, tyLent, tyOwned}: ty = skipTypes(ty.lastSon, abstractVarRange)
  case ty.kind
  of tyArray, tyOpenArray, tySequence, tyString, tyCString, tyVarargs:
    genArrayAddr(p, n, r)
  of tyTuple:
    genFieldAddr(p, n, r)
  else: internalError(p.config, n.info, "expr(nkBracketExpr, " & $ty.kind & ')')
  r.typ = mapType(n.typ)
  if r.res == nil: internalError(p.config, n.info, "genArrayAccess")
  if ty.kind == tyCString:
    r.res = "$1.charCodeAt($2)" % [r.address, r.res]
  elif r.typ == etyBaseIndex:
    if needsTemp(p, n[0]):
      let tmp = p.getTemp
      r.address = "($1 = $2, $1)[0]" % [tmp, r.rdLoc]
      r.res = "$1[1]" % [tmp]
      r.tmpLoc = tmp
    else:
      let x = r.rdLoc
      r.address = "$1[0]" % [x]
      r.res = "$1[1]" % [x]
  else:
    r.res = "$1[$2]" % [r.address, r.res]
  r.kind = resExpr

template isIndirect(x: PSym): bool =
  let v = x
  ({sfAddrTaken, sfGlobal} * v.flags != {} and
    #(mapType(v.typ) != etyObject) and
    {sfImportc, sfExportc} * v.flags == {} and
    v.kind notin {skProc, skFunc, skConverter, skMethod, skIterator,
                  skConst, skTemp, skLet})

proc genAddr(p: PProc, n: PNode, r: var TCompRes) =
  case n[0].kind
  of nkSym:
    let s = n[0].sym
    if s.loc.r == nil: internalError(p.config, n.info, "genAddr: 3")
    case s.kind
    of skParam:
      r.res = s.loc.r
      r.address = nil
      r.typ = etyNone
    of skVar, skLet, skResult:
      r.kind = resExpr
      let jsType = mapType(p, n.typ)
      if jsType == etyObject:
        # make addr() a no-op:
        r.typ = etyNone
        if isIndirect(s):
          r.res = s.loc.r & "[0]"
        else:
          r.res = s.loc.r
        r.address = nil
      elif {sfGlobal, sfAddrTaken} * s.flags != {} or jsType == etyBaseIndex:
        # for ease of code generation, we do not distinguish between
        # sfAddrTaken and sfGlobal.
        r.typ = etyBaseIndex
        r.address = s.loc.r
        r.res = rope("0")
      else:
        # 'var openArray' for instance produces an 'addr' but this is harmless:
        gen(p, n[0], r)
        #internalError(p.config, n.info, "genAddr: 4 " & renderTree(n))
    else: internalError(p.config, n.info, $("genAddr: 2", s.kind))
  of nkCheckedFieldExpr:
    genCheckedFieldOp(p, n[0], n.typ, r)
  of nkDotExpr:
    if mapType(p, n.typ) == etyBaseIndex:
      genFieldAddr(p, n[0], r)
    else:
      genFieldAccess(p, n[0], r)
  of nkBracketExpr:
    var ty = skipTypes(n[0].typ, abstractVarRange)
    if ty.kind in MappedToObject:
      gen(p, n[0], r)
    else:
      let kindOfIndexedExpr = skipTypes(n[0][0].typ, abstractVarRange).kind
      case kindOfIndexedExpr
      of tyArray, tyOpenArray, tySequence, tyString, tyCString, tyVarargs:
        genArrayAddr(p, n[0], r)
      of tyTuple:
        genFieldAddr(p, n[0], r)
      else: internalError(p.config, n[0].info, "expr(nkBracketExpr, " & $kindOfIndexedExpr & ')')
  of nkObjDownConv:
    gen(p, n[0], r)
  of nkHiddenDeref:
    gen(p, n[0], r)
  of nkHiddenAddr:
    gen(p, n[0], r)
  of nkStmtListExpr:
    if n.len == 1: gen(p, n[0], r)
    else: internalError(p.config, n[0].info, "genAddr for complex nkStmtListExpr")
  else: internalError(p.config, n[0].info, "genAddr: " & $n[0].kind)

proc attachProc(p: PProc; content: Rope; s: PSym) =
  p.g.code.add(content)

proc attachProc(p: PProc; s: PSym) =
  let newp = genProc(p, s)
  attachProc(p, newp, s)

proc genProcForSymIfNeeded(p: PProc, s: PSym) =
  if not p.g.generatedSyms.containsOrIncl(s.id):
    let newp = genProc(p, s)
    var owner = p
    while owner != nil and owner.prc != s.owner:
      owner = owner.up
    if owner != nil: owner.locals.add(newp)
    else: attachProc(p, newp, s)

proc genCopyForParamIfNeeded(p: PProc, n: PNode) =
  let s = n.sym
  if p.prc == s.owner or needsNoCopy(p, n):
    return
  var owner = p.up
  while true:
    if owner == nil:
      internalError(p.config, n.info, "couldn't find the owner proc of the closed over param: " & s.name.s)
    if owner.prc == s.owner:
      if not owner.generatedParamCopies.containsOrIncl(s.id):
        let copy = "$1 = nimCopy(null, $1, $2);$n" % [s.loc.r, genTypeInfo(p, s.typ)]
        owner.locals.add(owner.indentLine(copy))
      return
    owner = owner.up

proc genVarInit(p: PProc, v: PSym, n: PNode)

proc genSym(p: PProc, n: PNode, r: var TCompRes) =
  var s = n.sym
  case s.kind
  of skVar, skLet, skParam, skTemp, skResult, skForVar:
    if s.loc.r == nil:
      internalError(p.config, n.info, "symbol has no generated name: " & s.name.s)
    if sfCompileTime in s.flags:
      genVarInit(p, s, if s.ast != nil: s.ast else: newNodeI(nkEmpty, s.info))
    if s.kind == skParam:
      genCopyForParamIfNeeded(p, n)
    let k = mapType(p, s.typ)
    if k == etyBaseIndex:
      r.typ = etyBaseIndex
      if {sfAddrTaken, sfGlobal} * s.flags != {}:
        if isIndirect(s):
          r.address = "$1[0][0]" % [s.loc.r]
          r.res = "$1[0][1]" % [s.loc.r]
        else:
          r.address = "$1[0]" % [s.loc.r]
          r.res = "$1[1]" % [s.loc.r]
      else:
        r.address = s.loc.r
        r.res = s.loc.r & "_Idx"
    elif isIndirect(s):
      r.res = "$1[0]" % [s.loc.r]
    else:
      r.res = s.loc.r
  of skConst:
    genConstant(p, s)
    if s.loc.r == nil:
      internalError(p.config, n.info, "symbol has no generated name: " & s.name.s)
    r.res = s.loc.r
  of skProc, skFunc, skConverter, skMethod:
    if sfCompileTime in s.flags:
      localError(p.config, n.info, "request to generate code for .compileTime proc: " &
          s.name.s)
    discard mangleName(p.module, s)
    r.res = s.loc.r
    if lfNoDecl in s.loc.flags or s.magic != mNone or
       {sfImportc, sfInfixCall} * s.flags != {}:
      discard
    elif s.kind == skMethod and s.getBody.kind == nkEmpty:
      # we cannot produce code for the dispatcher yet:
      discard
    elif sfForward in s.flags:
      p.g.forwarded.add(s)
    else:
      genProcForSymIfNeeded(p, s)
  else:
    if s.loc.r == nil:
      internalError(p.config, n.info, "symbol has no generated name: " & s.name.s)
    r.res = s.loc.r
  r.kind = resVal

proc genDeref(p: PProc, n: PNode, r: var TCompRes) =
  let it = n[0]
  let t = mapType(p, it.typ)
  if t == etyObject:
    gen(p, it, r)
  else:
    var a: TCompRes
    gen(p, it, a)
    r.kind = a.kind
    r.typ = mapType(p, n.typ)
    if r.typ == etyBaseIndex:
      let tmp = p.getTemp
      r.address = "($1 = $2, $1)[0]" % [tmp, a.rdLoc]
      r.res = "$1[1]" % [tmp]
      r.tmpLoc = tmp
    elif a.typ == etyBaseIndex:
      if a.tmpLoc != nil:
        r.tmpLoc = a.tmpLoc
      r.res = a.rdLoc
    else:
      internalError(p.config, n.info, "genDeref")

proc genArgNoParam(p: PProc, n: PNode, r: var TCompRes) =
  var a: TCompRes
  gen(p, n, a)
  if a.typ == etyBaseIndex:
    r.res.add(a.address)
    r.res.add(", ")
    r.res.add(a.res)
  else:
    r.res.add(a.res)

proc genArg(p: PProc, n: PNode, param: PSym, r: var TCompRes; emitted: ptr int = nil) =
  var a: TCompRes
  gen(p, n, a)
  if skipTypes(param.typ, abstractVar).kind in {tyOpenArray, tyVarargs} and
      a.typ == etyBaseIndex:
    r.res.add("$1[$2]" % [a.address, a.res])
  elif a.typ == etyBaseIndex:
    r.res.add(a.address)
    r.res.add(", ")
    r.res.add(a.res)
    if emitted != nil: inc emitted[]
  elif n.typ.kind in {tyVar, tyPtr, tyRef, tyLent, tyOwned} and
      n.kind in nkCallKinds and mapType(param.typ) == etyBaseIndex:
    # this fixes bug #5608:
    let tmp = getTemp(p)
    r.res.add("($1 = $2, $1[0]), $1[1]" % [tmp, a.rdLoc])
    if emitted != nil: inc emitted[]
  else:
    r.res.add(a.res)

proc genArgs(p: PProc, n: PNode, r: var TCompRes; start=1) =
  r.res.add("(")
  var hasArgs = false

  var typ = skipTypes(n[0].typ, abstractInst)
  assert(typ.kind == tyProc)
  assert(typ.len == typ.n.len)
  var emitted = start-1

  for i in start..<n.len:
    let it = n[i]
    var paramType: PNode = nil
    if i < typ.len:
      assert(typ.n[i].kind == nkSym)
      paramType = typ.n[i]
      if paramType.typ.isCompileTimeOnly: continue

    if hasArgs: r.res.add(", ")
    if paramType.isNil:
      genArgNoParam(p, it, r)
    else:
      genArg(p, it, paramType.sym, r, addr emitted)
    inc emitted
    hasArgs = true
  r.res.add(")")
  when false:
    # XXX look into this:
    let jsp = countJsParams(typ)
    if emitted != jsp and tfVarargs notin typ.flags:
      localError(p.config, n.info, "wrong number of parameters emitted; expected: " & $jsp &
        " but got: " & $emitted)
  r.kind = resExpr

proc genOtherArg(p: PProc; n: PNode; i: int; typ: PType;
                 generated: var int; r: var TCompRes) =
  if i >= n.len:
    globalError(p.config, n.info, "wrong importcpp pattern; expected parameter at position " & $i &
        " but got only: " & $(n.len-1))
  let it = n[i]
  var paramType: PNode = nil
  if i < typ.len:
    assert(typ.n[i].kind == nkSym)
    paramType = typ.n[i]
    if paramType.typ.isCompileTimeOnly: return
  if paramType.isNil:
    genArgNoParam(p, it, r)
  else:
    genArg(p, it, paramType.sym, r)
  inc generated

proc genPatternCall(p: PProc; n: PNode; pat: string; typ: PType;
                    r: var TCompRes) =
  var i = 0
  var j = 1
  r.kind = resExpr
  while i < pat.len:
    case pat[i]
    of '@':
      var generated = 0
      for k in j..<n.len:
        if generated > 0: r.res.add(", ")
        genOtherArg(p, n, k, typ, generated, r)
      inc i
    of '#':
      var generated = 0
      genOtherArg(p, n, j, typ, generated, r)
      inc j
      inc i
    of '\31':
      # unit separator
      r.res.add("#")
      inc i
    of '\29':
      # group separator
      r.res.add("@")
      inc i
    else:
      let start = i
      while i < pat.len:
        if pat[i] notin {'@', '#', '\31', '\29'}: inc(i)
        else: break
      if i - 1 >= start:
        r.res.add(substr(pat, start, i - 1))

proc genInfixCall(p: PProc, n: PNode, r: var TCompRes) =
  # don't call '$' here for efficiency:
  let f = n[0].sym
  if f.loc.r == nil: f.loc.r = mangleName(p.module, f)
  if sfInfixCall in f.flags:
    let pat = n[0].sym.loc.r.data
    internalAssert p.config, pat.len > 0
    if pat.contains({'#', '(', '@'}):
      var typ = skipTypes(n[0].typ, abstractInst)
      assert(typ.kind == tyProc)
      genPatternCall(p, n, pat, typ, r)
      return
  if n.len != 1:
    gen(p, n[1], r)
    if r.typ == etyBaseIndex:
      if r.address == nil:
        globalError(p.config, n.info, "cannot invoke with infix syntax")
      r.res = "$1[$2]" % [r.address, r.res]
      r.address = nil
      r.typ = etyNone
    r.res.add(".")
  var op: TCompRes
  gen(p, n[0], op)
  r.res.add(op.res)
  genArgs(p, n, r, 2)

proc genCall(p: PProc, n: PNode, r: var TCompRes) =
  gen(p, n[0], r)
  genArgs(p, n, r)
  if n.typ != nil:
    let t = mapType(n.typ)
    if t == etyBaseIndex:
      let tmp = p.getTemp
      r.address = "($1 = $2, $1)[0]" % [tmp, r.rdLoc]
      r.res = "$1[1]" % [tmp]
      r.tmpLoc = tmp
      r.typ = t

proc genEcho(p: PProc, n: PNode, r: var TCompRes) =
  let n = n[1].skipConv
  internalAssert p.config, n.kind == nkBracket
  useMagic(p, "toJSStr") # Used in rawEcho
  useMagic(p, "rawEcho")
  r.res.add("rawEcho(")
  for i in 0..<n.len:
    let it = n[i]
    if it.typ.isCompileTimeOnly: continue
    if i > 0: r.res.add(", ")
    genArgNoParam(p, it, r)
  r.res.add(")")
  r.kind = resExpr

proc putToSeq(s: string, indirect: bool): Rope =
  result = rope(s)
  if indirect: result = "[$1]" % [result]

proc createVar(p: PProc, typ: PType, indirect: bool): Rope
proc createRecordVarAux(p: PProc, rec: PNode, excludedFieldIDs: IntSet, output: var Rope) =
  case rec.kind
  of nkRecList:
    for i in 0..<rec.len:
      createRecordVarAux(p, rec[i], excludedFieldIDs, output)
  of nkRecCase:
    createRecordVarAux(p, rec[0], excludedFieldIDs, output)
    for i in 1..<rec.len:
      createRecordVarAux(p, lastSon(rec[i]), excludedFieldIDs, output)
  of nkSym:
    # Do not produce code for void types
    if isEmptyType(rec.sym.typ): return
    if rec.sym.id notin excludedFieldIDs:
      if output.len > 0: output.add(", ")
      output.addf("$#: ", [mangleName(p.module, rec.sym)])
      output.add(createVar(p, rec.sym.typ, false))
  else: internalError(p.config, rec.info, "createRecordVarAux")

proc createObjInitList(p: PProc, typ: PType, excludedFieldIDs: IntSet, output: var Rope) =
  var t = typ
  if objHasTypeField(t):
    if output.len > 0: output.add(", ")
    output.addf("m_type: $1", [genTypeInfo(p, t)])
  while t != nil:
    t = t.skipTypes(skipPtrs)
    createRecordVarAux(p, t.n, excludedFieldIDs, output)
    t = t[0]

proc arrayTypeForElemType(typ: PType): string =
  # XXX This should also support tyEnum and tyBool
  case typ.kind
  of tyInt, tyInt32: "Int32Array"
  of tyInt16: "Int16Array"
  of tyInt8: "Int8Array"
  of tyUInt, tyUInt32: "Uint32Array"
  of tyUInt16: "Uint16Array"
  of tyUInt8: "Uint8Array"
  of tyFloat32: "Float32Array"
  of tyFloat64, tyFloat: "Float64Array"
  else: ""

proc createVar(p: PProc, typ: PType, indirect: bool): Rope =
  var t = skipTypes(typ, abstractInst)
  case t.kind
  of tyInt..tyInt64, tyUInt..tyUInt64, tyEnum, tyChar:
    result = putToSeq("0", indirect)
  of tyFloat..tyFloat128:
    result = putToSeq("0.0", indirect)
  of tyRange, tyGenericInst, tyAlias, tySink, tyOwned:
    result = createVar(p, lastSon(typ), indirect)
  of tySet:
    result = putToSeq("{}", indirect)
  of tyBool:
    result = putToSeq("false", indirect)
  of tyNil:
    result = putToSeq("null", indirect)
  of tyArray:
    let length = toInt(lengthOrd(p.config, t))
    let e = elemType(t)
    let jsTyp = arrayTypeForElemType(e)
    if jsTyp.len > 0:
      result = "new $1($2)" % [rope(jsTyp), rope(length)]
    elif length > 32:
      useMagic(p, "arrayConstr")
      # XXX: arrayConstr depends on nimCopy. This line shouldn't be necessary.
      useMagic(p, "nimCopy")
      result = "arrayConstr($1, $2, $3)" % [rope(length),
          createVar(p, e, false), genTypeInfo(p, e)]
    else:
      result = rope("[")
      var i = 0
      while i < length:
        if i > 0: result.add(", ")
        result.add(createVar(p, e, false))
        inc(i)
      result.add("]")
    if indirect: result = "[$1]" % [result]
  of tyTuple:
    result = rope("{")
    for i in 0..<t.len:
      if i > 0: result.add(", ")
      result.addf("Field$1: $2", [i.rope,
            createVar(p, t[i], false)])
    result.add("}")
    if indirect: result = "[$1]" % [result]
  of tyObject:
    var initList: Rope
    createObjInitList(p, t, initIntSet(), initList)
    result = ("({$1})") % [initList]
    if indirect: result = "[$1]" % [result]
  of tyVar, tyPtr, tyLent, tyRef, tyPointer:
    if mapType(p, t) == etyBaseIndex:
      result = putToSeq("[null, 0]", indirect)
    else:
      result = putToSeq("null", indirect)
  of tySequence, tyString:
    result = putToSeq("[]", indirect)
  of tyCString, tyProc:
    result = putToSeq("null", indirect)
  of tyStatic:
    if t.n != nil:
      result = createVar(p, lastSon t, indirect)
    else:
      internalError(p.config, "createVar: " & $t.kind)
      result = nil
  else:
    internalError(p.config, "createVar: " & $t.kind)
    result = nil

template returnType: untyped = ~""

proc genVarInit(p: PProc, v: PSym, n: PNode) =
  var
    a: TCompRes
    s: Rope
    varCode: string
    varName = mangleName(p.module, v)
    useReloadingGuard = sfGlobal in v.flags and p.config.hcrOn

  if v.constraint.isNil:
    if useReloadingGuard:
      lineF(p, "var $1;$n", varName)
      lineF(p, "if ($1 === undefined) {$n", varName)
      varCode = $varName
      inc p.extraIndent
    else:
      varCode = "var $2"
  else:
    # Is this really a thought through feature?  this basically unused
    # feature makes it impossible for almost all format strings in
    # this function to be checked at compile time.
    varCode = v.constraint.strVal

  if n.kind == nkEmpty:
    if not isIndirect(v) and
      v.typ.kind in {tyVar, tyPtr, tyLent, tyRef, tyOwned} and mapType(p, v.typ) == etyBaseIndex:
      lineF(p, "var $1 = null;$n", [varName])
      lineF(p, "var $1_Idx = 0;$n", [varName])
    else:
      line(p, runtimeFormat(varCode & " = $3;$n", [returnType, varName, createVar(p, v.typ, isIndirect(v))]))
  else:
    gen(p, n, a)
    case mapType(p, v.typ)
    of etyObject, etySeq:
      if needsNoCopy(p, n):
        s = a.res
      else:
        useMagic(p, "nimCopy")
        s = "nimCopy(null, $1, $2)" % [a.res, genTypeInfo(p, n.typ)]
    of etyBaseIndex:
      let targetBaseIndex = {sfAddrTaken, sfGlobal} * v.flags == {}
      if a.typ == etyBaseIndex:
        if targetBaseIndex:
          line(p, runtimeFormat(varCode & " = $3, $2_Idx = $4;$n",
                   [returnType, v.loc.r, a.address, a.res]))
        else:
          if isIndirect(v):
            line(p, runtimeFormat(varCode & " = [[$3, $4]];$n",
                     [returnType, v.loc.r, a.address, a.res]))
          else:
            line(p, runtimeFormat(varCode & " = [$3, $4];$n",
                     [returnType, v.loc.r, a.address, a.res]))
      else:
        if targetBaseIndex:
          let tmp = p.getTemp
          lineF(p, "var $1 = $2, $3 = $1[0], $3_Idx = $1[1];$n",
                   [tmp, a.res, v.loc.r])
        else:
          line(p, runtimeFormat(varCode & " = $3;$n", [returnType, v.loc.r, a.res]))
      return
    else:
      s = a.res
    if isIndirect(v):
      line(p, runtimeFormat(varCode & " = [$3];$n", [returnType, v.loc.r, s]))
    else:
      line(p, runtimeFormat(varCode & " = $3;$n", [returnType, v.loc.r, s]))

  if useReloadingGuard:
    dec p.extraIndent
    lineF(p, "}$n")

proc genVarStmt(p: PProc, n: PNode) =
  for i in 0..<n.len:
    var a = n[i]
    if a.kind != nkCommentStmt:
      if a.kind == nkVarTuple:
        let unpacked = lowerTupleUnpacking(p.module.graph, a, p.prc)
        genStmt(p, unpacked)
      else:
        assert(a.kind == nkIdentDefs)
        assert(a[0].kind == nkSym)
        var v = a[0].sym
        if lfNoDecl notin v.loc.flags and sfImportc notin v.flags:
          genLineDir(p, a)
          if sfCompileTime notin v.flags:
            genVarInit(p, v, a[2])
          else:
            # lazy emit, done when it's actually used.
            if v.ast == nil: v.ast = a[2]

proc genConstant(p: PProc, c: PSym) =
  if lfNoDecl notin c.loc.flags and not p.g.generatedSyms.containsOrIncl(c.id):
    let oldBody = p.body
    p.body = nil
    #genLineDir(p, c.ast)
    genVarInit(p, c, c.ast)
    p.g.constants.add(p.body)
    p.body = oldBody

proc genNew(p: PProc, n: PNode) =
  var a: TCompRes
  gen(p, n[1], a)
  var t = skipTypes(n[1].typ, abstractVar)[0]
  if mapType(t) == etyObject:
    lineF(p, "$1 = $2;$n", [a.rdLoc, createVar(p, t, false)])
  elif a.typ == etyBaseIndex:
    lineF(p, "$1 = [$3]; $2 = 0;$n", [a.address, a.res, createVar(p, t, false)])
  else:
    lineF(p, "$1 = [[$2], 0];$n", [a.rdLoc, createVar(p, t, false)])

proc genNewSeq(p: PProc, n: PNode) =
  var x, y: TCompRes
  gen(p, n[1], x)
  gen(p, n[2], y)
  let t = skipTypes(n[1].typ, abstractVar)[0]
  lineF(p, "$1 = new Array($2); for (var i=0;i<$2;++i) {$1[i]=$3;}", [
    x.rdLoc, y.rdLoc, createVar(p, t, false)])

proc genOrd(p: PProc, n: PNode, r: var TCompRes) =
  case skipTypes(n[1].typ, abstractVar + abstractRange).kind
  of tyEnum, tyInt..tyUInt64, tyChar: gen(p, n[1], r)
  of tyBool: unaryExpr(p, n, r, "", "($1 ? 1:0)")
  else: internalError(p.config, n.info, "genOrd")

proc genConStrStr(p: PProc, n: PNode, r: var TCompRes) =
  var a: TCompRes

  gen(p, n[1], a)
  r.kind = resExpr
  if skipTypes(n[1].typ, abstractVarRange).kind == tyChar:
    r.res.add("[$1].concat(" % [a.res])
  else:
    r.res.add("($1 || []).concat(" % [a.res])

  for i in 2..<n.len - 1:
    gen(p, n[i], a)
    if skipTypes(n[i].typ, abstractVarRange).kind == tyChar:
      r.res.add("[$1]," % [a.res])
    else:
      r.res.add("$1 || []," % [a.res])

  gen(p, n[^1], a)
  if skipTypes(n[^1].typ, abstractVarRange).kind == tyChar:
    r.res.add("[$1])" % [a.res])
  else:
    r.res.add("$1 || [])" % [a.res])

proc genReprAux(p: PProc, n: PNode, r: var TCompRes, magic: string, typ: Rope = nil) =
  useMagic(p, magic)
  r.res.add(magic & "(")
  var a: TCompRes

  gen(p, n[1], a)
  if magic == "reprAny":
    # the pointer argument in reprAny is expandend to
    # (pointedto, pointer), so we need to fill it
    if a.address.isNil:
      r.res.add(a.res)
      r.res.add(", null")
    else:
      r.res.add("$1, $2" % [a.address, a.res])
  else:
    r.res.add(a.res)

  if not typ.isNil:
    r.res.add(", ")
    r.res.add(typ)
  r.res.add(")")

proc genRepr(p: PProc, n: PNode, r: var TCompRes) =
  let t = skipTypes(n[1].typ, abstractVarRange)
  case t.kind:
  of tyInt..tyInt64, tyUInt..tyUInt64:
    genReprAux(p, n, r, "reprInt")
  of tyChar:
    genReprAux(p, n, r, "reprChar")
  of tyBool:
    genReprAux(p, n, r, "reprBool")
  of tyFloat..tyFloat128:
    genReprAux(p, n, r, "reprFloat")
  of tyString:
    genReprAux(p, n, r, "reprStr")
  of tyEnum, tyOrdinal:
    genReprAux(p, n, r, "reprEnum", genTypeInfo(p, t))
  of tySet:
    genReprAux(p, n, r, "reprSet", genTypeInfo(p, t))
  of tyEmpty, tyVoid:
    localError(p.config, n.info, "'repr' doesn't support 'void' type")
  of tyPointer:
    genReprAux(p, n, r, "reprPointer")
  of tyOpenArray, tyVarargs:
    genReprAux(p, n, r, "reprJSONStringify")
  else:
    genReprAux(p, n, r, "reprAny", genTypeInfo(p, t))

proc genOf(p: PProc, n: PNode, r: var TCompRes) =
  var x: TCompRes
  let t = skipTypes(n[2].typ,
                    abstractVarRange+{tyRef, tyPtr, tyLent, tyTypeDesc, tyOwned})
  gen(p, n[1], x)
  if tfFinal in t.flags:
    r.res = "($1.m_type == $2)" % [x.res, genTypeInfo(p, t)]
  else:
    useMagic(p, "isObj")
    r.res = "isObj($1.m_type, $2)" % [x.res, genTypeInfo(p, t)]
  r.kind = resExpr

proc genDefault(p: PProc, n: PNode; r: var TCompRes) =
  r.res = createVar(p, n.typ, indirect = false)
  r.kind = resExpr

proc genReset(p: PProc, n: PNode) =
  var x: TCompRes
  useMagic(p, "genericReset")
  gen(p, n[1], x)
  if x.typ == etyBaseIndex:
    lineF(p, "$1 = null, $2 = 0;$n", [x.address, x.res])
  else:
    let (a, tmp) = maybeMakeTempAssignable(p, n[1], x)
    lineF(p, "$1 = genericReset($3, $2);$n", [a,
                  genTypeInfo(p, n[1].typ), tmp])

proc genMove(p: PProc; n: PNode; r: var TCompRes) =
  var a: TCompRes
  r.kind = resVal
  r.res = p.getTemp()
  gen(p, n[1], a)
  lineF(p, "$1 = $2;$n", [r.rdLoc, a.rdLoc])
  genReset(p, n)
  #lineF(p, "$1 = $2;$n", [dest.rdLoc, src.rdLoc])

proc genSetConstr(p: PProc, n: PNode, r: var TCompRes) =
  var
    a, b: TCompRes
  useMagic(p, "setConstr")
  r.res = rope("setConstr(")
  r.kind = resExpr
  for i in 0..<n.len:
    if i > 0: r.res.add(", ")
    var it = n[i]
    if it.kind == nkRange:
      gen(p, it[0], a)
      gen(p, it[1], b)
      r.res.addf("[$1, $2]", [a.res, b.res])
    else:
      gen(p, it, a)
      r.res.add(a.res)
  r.res.add(")")
  # emit better code for constant sets:
  if isDeepConstExpr(n):
    inc(p.g.unique)
    let tmp = rope("ConstSet") & rope(p.g.unique)
    p.g.constants.addf("var $1 = $2;$n", [tmp, r.res])
    r.res = tmp

proc genArrayConstr(p: PProc, n: PNode, r: var TCompRes) =
  var a: TCompRes
  r.res = rope("[")
  r.kind = resExpr
  for i in 0..<n.len:
    if i > 0: r.res.add(", ")
    gen(p, n[i], a)
    if a.typ == etyBaseIndex:
      r.res.addf("[$1, $2]", [a.address, a.res])
    else:
      if not needsNoCopy(p, n[i]):
        let typ = n[i].typ.skipTypes(abstractInst)
        useMagic(p, "nimCopy")
        a.res = "nimCopy(null, $1, $2)" % [a.rdLoc, genTypeInfo(p, typ)]
      r.res.add(a.res)
  r.res.add("]")

proc genTupleConstr(p: PProc, n: PNode, r: var TCompRes) =
  var a: TCompRes
  r.res = rope("{")
  r.kind = resExpr
  for i in 0..<n.len:
    if i > 0: r.res.add(", ")
    var it = n[i]
    if it.kind == nkExprColonExpr: it = it[1]
    gen(p, it, a)
    let typ = it.typ.skipTypes(abstractInst)
    if a.typ == etyBaseIndex:
      r.res.addf("Field$#: [$#, $#]", [i.rope, a.address, a.res])
    else:
      if not needsNoCopy(p, it):
        useMagic(p, "nimCopy")
        a.res = "nimCopy(null, $1, $2)" % [a.rdLoc, genTypeInfo(p, typ)]
      r.res.addf("Field$#: $#", [i.rope, a.res])
  r.res.add("}")

proc genObjConstr(p: PProc, n: PNode, r: var TCompRes) =
  var a: TCompRes
  r.kind = resExpr
  var initList : Rope
  var fieldIDs = initIntSet()
  for i in 1..<n.len:
    if i > 1: initList.add(", ")
    var it = n[i]
    internalAssert p.config, it.kind == nkExprColonExpr
    let val = it[1]
    gen(p, val, a)
    var f = it[0].sym
    if f.loc.r == nil: f.loc.r = mangleName(p.module, f)
    fieldIDs.incl(f.id)

    let typ = val.typ.skipTypes(abstractInst)
    if a.typ == etyBaseIndex:
      initList.addf("$#: [$#, $#]", [f.loc.r, a.address, a.res])
    else:
      if not needsNoCopy(p, val):
        useMagic(p, "nimCopy")
        a.res = "nimCopy(null, $1, $2)" % [a.rdLoc, genTypeInfo(p, typ)]
      initList.addf("$#: $#", [f.loc.r, a.res])
  let t = skipTypes(n.typ, abstractInst + skipPtrs)
  createObjInitList(p, t, fieldIDs, initList)
  r.res = ("{$1}") % [initList]

proc genConv(p: PProc, n: PNode, r: var TCompRes) =
  var dest = skipTypes(n.typ, abstractVarRange)
  var src = skipTypes(n[1].typ, abstractVarRange)
  gen(p, n[1], r)
  if dest.kind == src.kind:
    # no-op conversion
    return
  case dest.kind:
  of tyBool:
    r.res = "(!!($1))" % [r.res]
    r.kind = resExpr
  of tyInt:
    r.res = "(($1)|0)" % [r.res]
  else:
    # TODO: What types must we handle here?
    discard

proc upConv(p: PProc, n: PNode, r: var TCompRes) =
  gen(p, n[0], r)        # XXX

proc genRangeChck(p: PProc, n: PNode, r: var TCompRes, magic: string) =
  var a, b: TCompRes
  gen(p, n[0], r)
  if optRangeCheck notin p.options or (skipTypes(n.typ, abstractVar).kind in {tyUInt..tyUInt64} and
      checkUnsignedConversions notin p.config.legacyFeatures):
    discard "XXX maybe emit masking instructions here"
  else:
    gen(p, n[1], a)
    gen(p, n[2], b)
    useMagic(p, "chckRange")
    r.res = "chckRange($1, $2, $3)" % [r.res, a.res, b.res]
    r.kind = resExpr

proc convStrToCStr(p: PProc, n: PNode, r: var TCompRes) =
  # we do an optimization here as this is likely to slow down
  # much of the code otherwise:
  if n[0].kind == nkCStringToString:
    gen(p, n[0][0], r)
  else:
    gen(p, n[0], r)
    if r.res == nil: internalError(p.config, n.info, "convStrToCStr")
    useMagic(p, "toJSStr")
    r.res = "toJSStr($1)" % [r.res]
    r.kind = resExpr

proc convCStrToStr(p: PProc, n: PNode, r: var TCompRes) =
  # we do an optimization here as this is likely to slow down
  # much of the code otherwise:
  if n[0].kind == nkStringToCString:
    gen(p, n[0][0], r)
  else:
    gen(p, n[0], r)
    if r.res == nil: internalError(p.config, n.info, "convCStrToStr")
    useMagic(p, "cstrToNimstr")
    r.res = "cstrToNimstr($1)" % [r.res]
    r.kind = resExpr

proc genReturnStmt(p: PProc, n: PNode) =
  if p.procDef == nil: internalError(p.config, n.info, "genReturnStmt")
  p.beforeRetNeeded = true
  if n[0].kind != nkEmpty:
    genStmt(p, n[0])
  else:
    genLineDir(p, n)
  lineF(p, "break BeforeRet;$n", [])

proc frameCreate(p: PProc; procname, filename: Rope): Rope =
  const frameFmt =
    "var F={procname:$1,prev:framePtr,filename:$2,line:0};$n"

  result = p.indentLine(frameFmt % [procname, filename])
  result.add p.indentLine(ropes.`%`("framePtr = F;$n", []))

proc frameDestroy(p: PProc): Rope =
  result = p.indentLine rope(("framePtr = F.prev;") & "\L")

proc genProcBody(p: PProc, prc: PSym): Rope =
  if hasFrameInfo(p):
    result = frameCreate(p,
              makeJSString(prc.owner.name.s & '.' & prc.name.s),
              makeJSString(toFilenameOption(p.config, prc.info.fileIndex, foStacktrace)))
  else:
    result = nil
  if p.beforeRetNeeded:
    result.add p.indentLine(~"BeforeRet: do {$n")
    result.add p.body
    result.add p.indentLine(~"} while (false);$n")
  else:
    result.add(p.body)
  if prc.typ.callConv == ccSysCall:
    result = ("try {$n$1} catch (e) {$n" &
      " alert(\"Unhandled exception:\\n\" + e.message + \"\\n\"$n}") % [result]
  if hasFrameInfo(p):
    result.add(frameDestroy(p))

proc optionalLine(p: Rope): Rope =
  if p == nil:
    return nil
  else:
    return p & "\L"

proc genProc(oldProc: PProc, prc: PSym): Rope =
  var
    resultSym: PSym
    a: TCompRes
  #if gVerbosity >= 3:
  #  echo "BEGIN generating code for: " & prc.name.s
  var p = newProc(oldProc.g, oldProc.module, prc.ast, prc.options)
  p.up = oldProc
  var returnStmt: Rope = nil
  var resultAsgn: Rope = nil
  var name = mangleName(p.module, prc)
  let header = generateHeader(p, prc.typ)
  if prc.typ[0] != nil and sfPure notin prc.flags:
    resultSym = prc.ast[resultPos].sym
    let mname = mangleName(p.module, resultSym)
    if not isIndirect(resultSym) and
      resultSym.typ.kind in {tyVar, tyPtr, tyLent, tyRef, tyOwned} and
        mapType(p, resultSym.typ) == etyBaseIndex:
      resultAsgn = p.indentLine(("var $# = null;$n") % [mname])
      resultAsgn.add p.indentLine("var $#_Idx = 0;$n" % [mname])
    else:
      let resVar = createVar(p, resultSym.typ, isIndirect(resultSym))
      resultAsgn = p.indentLine(("var $# = $#;$n") % [mname, resVar])
    gen(p, prc.ast[resultPos], a)
    if mapType(p, resultSym.typ) == etyBaseIndex:
      returnStmt = "return [$#, $#];$n" % [a.address, a.res]
    else:
      returnStmt = "return $#;$n" % [a.res]

  var transformedBody = transformBody(oldProc.module.graph, prc, cache = false)
  if sfInjectDestructors in prc.flags:
    transformedBody = injectDestructorCalls(oldProc.module.graph, prc, transformedBody)

  p.nested: genStmt(p, transformedBody)


  if optLineDir in p.config.options:
    result = lineDir(p.config, prc.info, toLinenumber(prc.info))

  var def: Rope
  if not prc.constraint.isNil:
    def = runtimeFormat(prc.constraint.strVal & " {$n$#$#$#$#$#",
            [ returnType,
              name,
              header,
              optionalLine(p.globals),
              optionalLine(p.locals),
              optionalLine(resultAsgn),
              optionalLine(genProcBody(p, prc)),
              optionalLine(p.indentLine(returnStmt))])
  else:
    # if optLineDir in p.config.options:
      # result.add(~"\L")

    if p.config.hcrOn:
      # Here, we introduce thunks that create the equivalent of a jump table
      # for all global functions, because references to them may be stored
      # in JavaScript variables. The added indirection ensures that such
      # references will end up calling the reloaded code.
      var thunkName = name
      name = name & "IMLP"
      result.add("function $#() { return $#.apply(this, arguments); }$n" %
                 [thunkName, name])

    def = "function $#($#) {$n$#$#$#$#$#" %
            [ name,
              header,
              optionalLine(p.globals),
              optionalLine(p.locals),
              optionalLine(resultAsgn),
              optionalLine(genProcBody(p, prc)),
              optionalLine(p.indentLine(returnStmt))]

  dec p.extraIndent
  result.add p.indentLine(def)
  result.add p.indentLine(~"}$n")

  #if gVerbosity >= 3:
  #  echo "END   generated code for: " & prc.name.s

proc genStmt(p: PProc, n: PNode) =
  var r: TCompRes
  gen(p, n, r)
  if r.res != nil: lineF(p, "$#;$n", [r.res])

proc genPragma(p: PProc, n: PNode) =
  for it in n.sons:
    case whichPragma(it)
    of wEmit: genAsmOrEmitStmt(p, it[1])
    else: discard

proc genCast(p: PProc, n: PNode, r: var TCompRes) =
  var dest = skipTypes(n.typ, abstractVarRange)
  var src = skipTypes(n[1].typ, abstractVarRange)
  gen(p, n[1], r)
  if dest.kind == src.kind:
    # no-op conversion
    return
  let toInt = (dest.kind in tyInt..tyInt32)
  let toUint = (dest.kind in tyUInt..tyUInt32)
  let fromInt = (src.kind in tyInt..tyInt32)
  let fromUint = (src.kind in tyUInt..tyUInt32)

  if toUint and (fromInt or fromUint):
    let trimmer = unsignedTrimmer(dest.size)
    r.res = "($1 $2)" % [r.res, trimmer]
  elif toInt:
    if fromInt:
      let trimmer = unsignedTrimmer(dest.size)
      r.res = "($1 $2)" % [r.res, trimmer]
    elif fromUint:
      if src.size == 4 and dest.size == 4:
        # XXX prevent multi evaluations
        r.res = "($1|0)" % [r.res]
      else:
        let trimmer = unsignedTrimmer(dest.size)
        let minuend = case dest.size
          of 1: "0xfe"
          of 2: "0xfffe"
          of 4: "0xfffffffe"
          else: ""
        r.res = "($1 - ($2 $3))" % [rope minuend, r.res, trimmer]
  elif (src.kind == tyPtr and mapType(p, src) == etyObject) and dest.kind == tyPointer:
    r.address = r.res
    r.res = ~"null"
    r.typ = etyBaseIndex
  elif (dest.kind == tyPtr and mapType(p, dest) == etyObject) and src.kind == tyPointer:
    r.res = r.address
    r.typ = etyObject
]#

proc genProc(es: ESGen, prc: PSym) =
  let ressym = if prc.ast.len > resultPos :prc.ast[resultPos] else: nil
  var bdy = newBlockStmt()
  if not ressym.isNil:
    bdy.add(
      newVarDecl(esLet, false,
        [newVarDeclarator(
          newESIdent("result", ressym.typ.typeToString),    
          if mapType(ressym.typ) == etyBaseIndex:
            newArrayExpr([newArrayExpr([newESEmitExpr("null")])])
          else: newArrayExpr([newESEmitExpr("null")])
        )]
      )
    )
  var tmpbody = es.gen(transformBody(es.graph, prc, false), bdy)
  bdy.add(tmpbody)
  if not ressym.isNil:
    #if ressym.typ.kind == tyVar:
      bdy.add(
        newReturnStmt(newESIdent("result"))
      )
    #else:
    #  bdy.add(
    #    newReturnStmt(newMemberExpr(newESIdent("result"), newESLiteral(0), false))
    #  )
  let declparams = prc.ast[paramsPos]
  var params = newSeq[ESNode](declparams.len-1)
  #echo es.config.treeToYaml(declparams)
  for i, p in declparams:
    echo i
    if i == 0: continue
    var tname: string
    if not p[1].isNil and p[1].kind == nkSym: tname = p[1].sym.name.s
    elif not p[2].isNil and not p[2].typ.isNil: tname = p[2].typ.typeToString
    else:
      echo es.config.treeToYaml(p)
      es.config.internalError("param has no type: " & p[0].ident.s)
    params[i-1] = newESIdent(p[0].ident.s, tname)

  ESBackend(es.graph.backend).ast.add(
    newESFuncDecl(
      newESIdent(prc.name.s, if ressym.isNil: "" else: ressym.typ.typeToString),
      bdy,
      params,
      card(prc.flags*{sfExported, sfExportc}) > 0
    )
  )

proc useMagic(es: ESGen, name: string, piece: var ESNode) : ESNode=
  if name.len == 0: es.config.internalError("empty compiler magic name")
  var s = magicsys.getCompilerProc(es.graph, name)
  if s != nil:
    internalAssert es.config, s.kind in {skProc, skFunc, skMethod, skConverter}
    if not ESBackend(es.graph.backend).generatedProcs.containsOrIncl(s.id):
      genProc(es, s)
  else:
    es.config.internalError("system module needs: " & name)
    
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

proc genAnd(es: ESGen, a, b: PNode, piece: var ESNode): ESNode =
  if isSimpleExpr(a) and isSimpleExpr(b):
    result = newBinaryExpr("&&", es.gen(a, piece), es.gen(b, piece))
  else:
    es.config.internalError("TODO: genAnd")

proc genOr(es: ESGen, a, b: PNode, piece: var ESNode): ESNode =
  if isSimpleExpr(a) and isSimpleExpr(b):
    result = newBinaryExpr("||", es.gen(a, piece), es.gen(b, piece))
  else:
    es.config.internalError("TODO: genOr")


type
  TMagicFrmt = array[0..1, string]
  TMagicOps = array[mAddI..mStrToStr, TMagicFrmt]

const # magic checked op; magic unchecked op;
  jsMagics: TMagicOps = [
    mAddI: ["addInt", ""],
    mSubI: ["subInt", ""],
    mMulI: ["mulInt", ""],
    mDivI: ["divInt", ""],
    mModI: ["modInt", ""],
    mSucc: ["addInt", ""],
    mPred: ["subInt", ""],
    mAddF64: ["", ""],
    mSubF64: ["", ""],
    mMulF64: ["", ""],
    mDivF64: ["", ""],
    mShrI: ["", ""],
    mShlI: ["", ""],
    mAshrI: ["", ""],
    mBitandI: ["", ""],
    mBitorI: ["", ""],
    mBitxorI: ["", ""],
    mMinI: ["nimMin", "nimMin"],
    mMaxI: ["nimMax", "nimMax"],
    mAddU: ["", ""],
    mSubU: ["", ""],
    mMulU: ["", ""],
    mDivU: ["", ""],
    mModU: ["", ""],
    mEqI: ["", ""],
    mLeI: ["", ""],
    mLtI: ["", ""],
    mEqF64: ["", ""],
    mLeF64: ["", ""],
    mLtF64: ["", ""],
    mLeU: ["", ""],
    mLtU: ["", ""],
    mEqEnum: ["", ""],
    mLeEnum: ["", ""],
    mLtEnum: ["", ""],
    mEqCh: ["", ""],
    mLeCh: ["", ""],
    mLtCh: ["", ""],
    mEqB: ["", ""],
    mLeB: ["", ""],
    mLtB: ["", ""],
    mEqRef: ["", ""],
    mLePtr: ["", ""],
    mLtPtr: ["", ""],
    mXor: ["", ""],
    mEqCString: ["", ""],
    mEqProc: ["", ""],
    mUnaryMinusI: ["negInt", ""],
    mUnaryMinusI64: ["negInt64", ""],
    mAbsI: ["absInt", ""],
    mNot: ["", ""],
    mUnaryPlusI: ["", ""],
    mBitnotI: ["", ""],
    mUnaryPlusF64: ["", ""],
    mUnaryMinusF64: ["", ""],
    mCharToStr: ["nimCharToStr", "nimCharToStr"],
    mBoolToStr: ["nimBoolToStr", "nimBoolToStr"],
    mIntToStr: ["cstrToNimstr", "cstrToNimstr"],
    mInt64ToStr: ["cstrToNimstr", "cstrToNimstr"],
    mFloatToStr: ["cstrToNimstr", "cstrToNimstr"],
    mCStrToStr: ["cstrToNimstr", "cstrToNimstr"],
    mStrToStr: ["", ""]]

proc needsTemp(n: PNode): bool =
  # check if n contains a call to determine
  # if a temp should be made to prevent multiple evals
  if n.kind in nkCallKinds + {nkTupleConstr, nkObjConstr, nkBracket, nkCurly}:
    return true
  for c in n:
    if needsTemp(c):
      return true
#[
template binaryExpr(p: PProc, n: PNode, r: var TCompRes, magic, frmt: string,
                    reassign = false) =
  # $1 and $2 in the `frmt` string bind to lhs and rhs of the expr,
  # if $3 or $4 are present they will be substituted with temps for
  # lhs and rhs respectively
  var x, y: TCompRes
  useMagic(p, magic)
  gen(p, n[1], x)
  gen(p, n[2], y)

  var
    a, tmp = x.rdLoc
    b, tmp2 = y.rdLoc
  when reassign:
    (a, tmp) = maybeMakeTempAssignable(p, n[1], x)
  else:
    when "$3" in frmt: (a, tmp) = maybeMakeTemp(p, n[1], x)
    when "$4" in frmt: (b, tmp2) = maybeMakeTemp(p, n[2], y)

  r.res = frmt % [a, b, tmp, tmp2]
  r.kind = resExpr

proc unsignedTrimmerJS(size: BiggestInt): Rope =
  case size
  of 1: rope"& 0xff"
  of 2: rope"& 0xffff"
  of 4: rope">>> 0"
  else: rope""


template unsignedTrimmer(size: BiggestInt): Rope =
  size.unsignedTrimmerJS

proc binaryUintExpr(p: PProc, n: PNode, r: var TCompRes, op: string,
                    reassign: static[bool] = false) =
  var x, y: TCompRes
  gen(p, n[1], x)
  gen(p, n[2], y)
  let trimmer = unsignedTrimmer(n[1].typ.skipTypes(abstractRange).size)
  when reassign:
    let (a, tmp) = maybeMakeTempAssignable(p, n[1], x)
    r.res = "$1 = (($5 $2 $3) $4)" % [a, rope op, y.rdLoc, trimmer, tmp]
  else:
    r.res = "(($1 $2 $3) $4)" % [x.rdLoc, rope op, y.rdLoc, trimmer]
  r.kind = resExpr

template ternaryExpr(p: PProc, n: PNode, r: var TCompRes, magic, frmt: string) =
  var x, y, z: TCompRes
  useMagic(p, magic)
  gen(p, n[1], x)
  gen(p, n[2], y)
  gen(p, n[3], z)
  r.res = frmt % [x.rdLoc, y.rdLoc, z.rdLoc]
  r.kind = resExpr

template unaryExpr(p: PProc, n: PNode, r: var TCompRes, magic, frmt: string) =
  # $1 binds to n[1], if $2 is present it will be substituted to a tmp of $1
  useMagic(p, magic)
  gen(p, n[1], r)
  var a, tmp = r.rdLoc
  if "$2" in frmt: (a, tmp) = maybeMakeTemp(p, n[1], r)
  r.res = frmt % [a, tmp]
  r.kind = resExpr

proc arithAux(p: PProc, n: PNode, r: var TCompRes, op: TMagic) =
  var
    x, y: TCompRes
    xLoc,yLoc: Rope
  let i = ord(optOverflowCheck notin p.options)
  useMagic(p, jsMagics[op][i])
  if n.len > 2:
    gen(p, n[1], x)
    gen(p, n[2], y)
    xLoc = x.rdLoc
    yLoc = y.rdLoc
  else:
    gen(p, n[1], r)
    xLoc = r.rdLoc

  template applyFormat(frmt) =
    r.res = frmt % [xLoc, yLoc]
  template applyFormat(frmtA, frmtB) =
    if i == 0: applyFormat(frmtA) else: applyFormat(frmtB)

  case op:
  of mAddI: applyFormat("addInt($1, $2)", "($1 + $2)")
  of mSubI: applyFormat("subInt($1, $2)", "($1 - $2)")
  of mMulI: applyFormat("mulInt($1, $2)", "($1 * $2)")
  of mDivI: applyFormat("divInt($1, $2)", "Math.trunc($1 / $2)")
  of mModI: applyFormat("modInt($1, $2)", "Math.trunc($1 % $2)")
  of mSucc: applyFormat("addInt($1, $2)", "($1 + $2)")
  of mPred: applyFormat("subInt($1, $2)", "($1 - $2)")
  of mAddF64: applyFormat("($1 + $2)", "($1 + $2)")
  of mSubF64: applyFormat("($1 - $2)", "($1 - $2)")
  of mMulF64: applyFormat("($1 * $2)", "($1 * $2)")
  of mDivF64: applyFormat("($1 / $2)", "($1 / $2)")
  of mShrI: applyFormat("", "")
  of mShlI: 
    if n[1].typ.size <= 4:
      applyFormat("($1 << $2)", "($1 << $2)")
    else:
      applyFormat("($1 * Math.pow(2,$2))", "($1 * Math.pow(2,$2))")
  of mAshrI: 
    if n[1].typ.size <= 4:
      applyFormat("($1 >> $2)", "($1 >> $2)")
    else:
      applyFormat("Math.floor($1 / Math.pow(2,$2))", "Math.floor($1 / Math.pow(2,$2))")
  of mBitandI: applyFormat("($1 & $2)", "($1 & $2)")
  of mBitorI: applyFormat("($1 | $2)", "($1 | $2)")
  of mBitxorI: applyFormat("($1 ^ $2)", "($1 ^ $2)")
  of mMinI: applyFormat("nimMin($1, $2)", "nimMin($1, $2)")
  of mMaxI: applyFormat("nimMax($1, $2)", "nimMax($1, $2)")
  of mAddU: applyFormat("", "")
  of mSubU: applyFormat("", "")
  of mMulU: applyFormat("", "")
  of mDivU: applyFormat("", "")
  of mModU: applyFormat("($1 % $2)", "($1 % $2)")
  of mEqI: applyFormat("($1 == $2)", "($1 == $2)")
  of mLeI: applyFormat("($1 <= $2)", "($1 <= $2)")
  of mLtI: applyFormat("($1 < $2)", "($1 < $2)")
  of mEqF64: applyFormat("($1 == $2)", "($1 == $2)")
  of mLeF64: applyFormat("($1 <= $2)", "($1 <= $2)")
  of mLtF64: applyFormat("($1 < $2)", "($1 < $2)")
  of mLeU: applyFormat("($1 <= $2)", "($1 <= $2)")
  of mLtU: applyFormat("($1 < $2)", "($1 < $2)")
  of mEqEnum: applyFormat("($1 == $2)", "($1 == $2)")
  of mLeEnum: applyFormat("($1 <= $2)", "($1 <= $2)")
  of mLtEnum: applyFormat("($1 < $2)", "($1 < $2)")
  of mEqCh: applyFormat("($1 == $2)", "($1 == $2)")
  of mLeCh: applyFormat("($1 <= $2)", "($1 <= $2)")
  of mLtCh: applyFormat("($1 < $2)", "($1 < $2)")
  of mEqB: applyFormat("($1 == $2)", "($1 == $2)")
  of mLeB: applyFormat("($1 <= $2)", "($1 <= $2)")
  of mLtB: applyFormat("($1 < $2)", "($1 < $2)")
  of mEqRef: applyFormat("($1 == $2)", "($1 == $2)")
  of mLePtr: applyFormat("($1 <= $2)", "($1 <= $2)")
  of mLtPtr: applyFormat("($1 < $2)", "($1 < $2)")
  of mXor: applyFormat("($1 != $2)", "($1 != $2)")
  of mEqCString: applyFormat("($1 == $2)", "($1 == $2)")
  of mEqProc: applyFormat("($1 == $2)", "($1 == $2)")
  of mUnaryMinusI: applyFormat("negInt($1)", "-($1)")
  of mUnaryMinusI64: applyFormat("negInt64($1)", "-($1)")
  of mAbsI: applyFormat("absInt($1)", "Math.abs($1)")
  of mNot: applyFormat("!($1)", "!($1)")
  of mUnaryPlusI: applyFormat("+($1)", "+($1)")
  of mBitnotI: applyFormat("~($1)", "~($1)")
  of mUnaryPlusF64: applyFormat("+($1)", "+($1)")
  of mUnaryMinusF64: applyFormat("-($1)", "-($1)")
  of mCharToStr: applyFormat("nimCharToStr($1)", "nimCharToStr($1)")
  of mBoolToStr: applyFormat("nimBoolToStr($1)", "nimBoolToStr($1)")
  of mIntToStr: applyFormat("cstrToNimstr(($1)+\"\")", "cstrToNimstr(($1)+\"\")")
  of mInt64ToStr: applyFormat("cstrToNimstr(($1)+\"\")", "cstrToNimstr(($1)+\"\")")
  of mFloatToStr:
    useMagic(p, "nimFloatToString")
    applyFormat "cstrToNimstr(nimFloatToString($1))"
  of mCStrToStr: applyFormat("cstrToNimstr($1)", "cstrToNimstr($1)")
  of mStrToStr, mUnown, mIsolate: applyFormat("$1", "$1")
  else:
    assert false, $op

proc arith(p: PProc, n: PNode, r: var TCompRes, op: TMagic) =
  case op
  of mAddU: binaryUintExpr(p, n, r, "+")
  of mSubU: binaryUintExpr(p, n, r, "-")
  of mMulU: binaryUintExpr(p, n, r, "*")
  of mDivU: binaryUintExpr(p, n, r, "/")
  of mDivI:
    arithAux(p, n, r, op)
  of mModI:
    arithAux(p, n, r, op)
  of mShrI:
    var x, y: TCompRes
    gen(p, n[1], x)
    gen(p, n[2], y)
    let trimmer = unsignedTrimmer(n[1].typ.skipTypes(abstractRange).size)
    r.res = "(($1 $2) >>> $3)" % [x.rdLoc, trimmer, y.rdLoc]
  of mCharToStr, mBoolToStr, mIntToStr, mInt64ToStr, mFloatToStr,
      mCStrToStr, mStrToStr, mEnumToStr:
    arithAux(p, n, r, op)
  of mEqRef:
    if mapType(n[1].typ) != etyBaseIndex:
      arithAux(p, n, r, op)
    else:
      var x, y: TCompRes
      gen(p, n[1], x)
      gen(p, n[2], y)
      r.res = "($# == $# && $# == $#)" % [x.address, y.address, x.res, y.res]
  else:
    arithAux(p, n, r, op)
  r.kind = resExpr


proc genMagic(p: PProc, n: PNode, r: var TCompRes) =
  var
    a: TCompRes
    line, filen: Rope
  var op = n[0].sym.magic
  case op
  of mOr: genOr(p, n[1], n[2], r)
  of mAnd: genAnd(p, n[1], n[2], r)
  of mAddI..mStrToStr: arith(p, n, r, op)
  of mRepr: genRepr(p, n, r)
  of mSwap: genSwap(p, n)
  of mAppendStrCh:
    binaryExpr(p, n, r, "addChar",
        "addChar($1, $2);")
  of mAppendStrStr:
    var lhs, rhs: TCompRes
    gen(p, n[1], lhs)
    gen(p, n[2], rhs)

    if skipTypes(n[1].typ, abstractVarRange).kind == tyCString:
      r.res = "$1 += $2;" % [lhs.rdLoc, rhs.rdLoc]
    else:
      let (a, tmp) = maybeMakeTemp(p, n[1], lhs)
      r.res = "$1.push.apply($3, $2);" % [a, rhs.rdLoc, tmp]
    r.kind = resExpr
  of mAppendSeqElem:
    var x, y: TCompRes
    gen(p, n[1], x)
    gen(p, n[2], y)
    if mapType(n[2].typ) == etyBaseIndex:
      let c = "[$1, $2]" % [y.address, y.res]
      r.res = "$1.push($2);" % [x.rdLoc, c]
    elif needsNoCopy(p, n[2]):
      r.res = "$1.push($2);" % [x.rdLoc, y.rdLoc]
    else:
      useMagic(p, "nimCopy")
      let c = getTemp(p, defineInLocals=false)
      lineF(p, "var $1 = nimCopy(null, $2, $3);$n",
            [c, y.rdLoc, genTypeInfo(p, n[2].typ)])
      r.res = "$1.push($2);" % [x.rdLoc, c]
    r.kind = resExpr
  of mConStrStr:
    genConStrStr(p, n, r)
  of mEqStr:
    binaryExpr(p, n, r, "eqStrings", "eqStrings($1, $2)")
  of mLeStr:
    binaryExpr(p, n, r, "cmpStrings", "(cmpStrings($1, $2) <= 0)")
  of mLtStr:
    binaryExpr(p, n, r, "cmpStrings", "(cmpStrings($1, $2) < 0)")
  of mIsNil:
    # we want to accept undefined, so we ==
    if mapType(n[1].typ) != etyBaseIndex:
      unaryExpr(p, n, r, "", "($1 == null)")
    else:
      var x: TCompRes
      gen(p, n[1], x)
      r.res = "($# == null && $# === 0)" % [x.address, x.res]
  of mEnumToStr: genRepr(p, n, r)
  of mNew, mNewFinalize: genNew(p, n)
  of mChr: gen(p, n[1], r)
  of mArrToSeq:
    if needsNoCopy(p, n[1]):
      gen(p, n[1], r)
    else:
      var x: TCompRes
      gen(p, n[1], x)
      useMagic(p, "nimCopy")
      r.res = "nimCopy(null, $1, $2)" % [x.rdLoc, genTypeInfo(p, n.typ)]
  of mDestroy: discard "ignore calls to the default destructor"
  of mOrd: genOrd(p, n, r)
  of mLengthStr, mLengthSeq, mLengthOpenArray, mLengthArray:
    unaryExpr(p, n, r, "", "($1).length")
  of mHigh:
    unaryExpr(p, n, r, "", "(($1).length-1)")
  of mInc:
    if n[1].typ.skipTypes(abstractRange).kind in {tyUInt..tyUInt64}:
      binaryUintExpr(p, n, r, "+", true)
    else:
      if optOverflowCheck notin p.options: binaryExpr(p, n, r, "", "$1 += $2")
      else: binaryExpr(p, n, r, "addInt", "$1 = addInt($3, $2)", true)
  of ast.mDec:
    if n[1].typ.skipTypes(abstractRange).kind in {tyUInt..tyUInt64}:
      binaryUintExpr(p, n, r, "-", true)
    else:
      if optOverflowCheck notin p.options: binaryExpr(p, n, r, "", "$1 -= $2")
      else: binaryExpr(p, n, r, "subInt", "$1 = subInt($3, $2)", true)
  of mSetLengthStr:
    binaryExpr(p, n, r, "mnewString", "($1.length = $2)")
  of mSetLengthSeq:
    var x, y: TCompRes
    gen(p, n[1], x)
    gen(p, n[2], y)
    let t = skipTypes(n[1].typ, abstractVar)[0]
    let (a, tmp) = maybeMakeTemp(p, n[1], x)
    let (b, tmp2) = maybeMakeTemp(p, n[2], y)
    r.res = """if ($1.length < $2) { for (var i=$4.length;i<$5;++i) $4.push($3); }
               else { $4.length = $5; }""" % [a, b, createVar(p, t, false), tmp, tmp2]
    r.kind = resExpr
  of mCard: unaryExpr(p, n, r, "SetCard", "SetCard($1)")
  of mLtSet: binaryExpr(p, n, r, "SetLt", "SetLt($1, $2)")
  of mLeSet: binaryExpr(p, n, r, "SetLe", "SetLe($1, $2)")
  of mEqSet: binaryExpr(p, n, r, "SetEq", "SetEq($1, $2)")
  of mMulSet: binaryExpr(p, n, r, "SetMul", "SetMul($1, $2)")
  of mPlusSet: binaryExpr(p, n, r, "SetPlus", "SetPlus($1, $2)")
  of mMinusSet: binaryExpr(p, n, r, "SetMinus", "SetMinus($1, $2)")
  of mIncl: binaryExpr(p, n, r, "", "$1[$2] = true")
  of mExcl: binaryExpr(p, n, r, "", "delete $1[$2]")
  of mInSet:
    binaryExpr(p, n, r, "", "($1[$2] != undefined)")
  of mNewSeq: genNewSeq(p, n)
  of mNewSeqOfCap: unaryExpr(p, n, r, "", "[]")
  of mOf: genOf(p, n, r)
  of mDefault: genDefault(p, n, r)
  of mReset, mWasMoved: genReset(p, n)
  of mEcho: genEcho(p, n, r)
  of mNLen..mNError, mSlurp, mStaticExec:
    localError(p.config, n.info, errXMustBeCompileTime % n[0].sym.name.s)
  of mNewString: unaryExpr(p, n, r, "mnewString", "mnewString($1)")
  of mNewStringOfCap:
    unaryExpr(p, n, r, "mnewString", "mnewString(0)")
  of mDotDot:
    genProcForSymIfNeeded(p, n[0].sym)
    genCall(p, n, r)
  of mParseBiggestFloat:
    useMagic(p, "nimParseBiggestFloat")
    genCall(p, n, r)
  of mSlice:
    # arr.slice([begin[, end]]): 'end' is exclusive
    var x, y, z: TCompRes
    gen(p, n[1], x)
    gen(p, n[2], y)
    gen(p, n[3], z)
    r.res = "($1.slice($2, $3+1))" % [x.rdLoc, y.rdLoc, z.rdLoc]
    r.kind = resExpr
  of mMove:
    genMove(p, n, r)
  else:
    genCall(p, n, r)
    #else internalError(p.config, e.info, 'genMagic: ' + magicToStr[op]);
]#

proc genMagicCall(es: ESGen, n: PNode, piece: var ESNode, loc: SourceLocation = nil) : ESNode=
  es.config.internalError("TODO: genMagicCall")
  if not es.graph.backend.ESBackend.generatedProcs.containsOrIncl(n[0].sym.id):
    es.genProc(n[0].sym)


proc genCall(es: ESGen, n: PNode, piece: var ESNode, loc: SourceLocation = nil) : ESNode=
  if not es.graph.backend.ESBackend.generatedProcs.containsOrIncl(n[0].sym.id):
    es.genProc(n[0].sym)

  var args = newSeq[ESNode]()
  for i, arg in n:
    if i == 0: continue
    args.add(es.gen(arg, piece))
  result = newCallExpr(
    newESIdent(n[0].sym.name.s), args
  )
proc genAsgn(es: ESGen, lhs, rhs: PNode, piece: var ESNode, loc: SourceLocation = nil): ESNode =
  result = newExpressionStmt(
    newAsgnExpr("=", es.gen(lhs, piece), es.gen(rhs, piece))
  )
proc gen(es: ESGen, n: PNode, piece: var ESNode, loc: SourceLocation = nil): ESNode =
  let conf = es.config
  let b = ESBackend(es.graph.backend)
  
  echo "#GTL: ", $n.kind, " module: ", conf.toFilename(n.info.fileIndex)
  echo "# working on: ", n.kind
  if not (n.kind == nkStmtList):
    echo renderTree(n)
    
  case n.kind:
  of nkGenSkippedKinds: result = newEmptyStmt() # returns ';'
  of nkSym:
    result = newESIdent(n.sym.name.s, n.sym.typ.typeToString)
  of nkCharLit..nkUInt64Lit:
    if n.typ.kind == tyBool:
      result = newESLiteral(n.intVal != 0)
    else:
      result = newESLiteral(n.intVal)
  of nkNilLit:
    if isEmptyType(n.typ):
      discard
    elif mapType(n.typ) == etyBaseIndex:
      result = newArrayExpr([newESEmitExpr("null")])
    else:
      result = newESEmitExpr("null")
  of nkStrLit..nkTripleStrLit:
    result = newESLiteral(n.strVal)
  of nkFloatLit..nkFloat64Lit:
    result = newESLiteral(n.floatVal)
  of nkCallKinds:
    if isEmptyType(n.typ):
      result = genCall(es, n, piece) # TODO: use the fact that no result is needed
    if (n[0].kind == nkSym) and (n[0].sym.magic != mNone):
      result = genMagicCall(es, n, piece)
    else:
      result = genCall(es, n, piece)
  of nkVarSection:
    result = newBlockStmt()
    # TODO: if v[2] is nkCallKind no need for brackets, the returned result is already a var
    for v in n.sons:
      result.add(
        newVarDecl(
          esLet, v[0].sym.exportOrUsed,
          [newVarDeclarator(es.gen(v[0], piece), newArrayExpr([es.gen(v[2], piece)]))]
        )
      )
  of nkLetSection:
    result = newBlockStmt()
    for v in n.sons:
      result.add(
        newVarDecl(
          esConst, v[0].sym.exportOrUsed,
          [newVarDeclarator(es.gen(v[0], piece), es.gen(v[2], piece))]
        )
      )
  of nkAsgn:
    result = es.genAsgn(n[0], n[1], piece)
  of nkStmtListExpr:
    for i, son in n.sons:
      if i == n.sons.len-1:
        result = es.gen(son,piece)
      piece.add(es.gen(son,piece))
  of nkStmtList:
    result = newBlockStmt()
    for son in n.sons:
      result.add(es.gen(son,piece))
  of nkBracket:
    result = newArrayExpr()
    for el in n.sons:
      result.add(es.gen(el,piece))
  of nkWhileStmt:
    result = newWhileStmt(
      es.gen(n[0], piece),
      es.gen(n[1], piece)
    )
  of nkBlockStmt:
    echo es.config.treeToYaml(n)
    result = newLabeledStmt(
      newESIdent(n[0].sym.name.s.mangle),
      es.gen(n[1], piece)
    )
  else: internalError(es.config, "gen: unknown node type: " & $n.kind)

  #[
  of nkClosure:
  of nkCurly:
  of nkBracket:
  of nkPar, nkTupleConstr:
  of nkObjConstr:
  of nkHiddenStdConv, nkHiddenSubConv, nkConv:
  of nkAddr, nkHiddenAddr
  of nkDerefExpr, nkHiddenDeref:
  of nkBracketExpr:
  of nkDotExpr:
  of nkCheckedFieldExpr:
  of nkObjDownConv:
  of nkObjUpConv:
  of nkCast:
  of nkChckRangeF:
  of nkChckRange64:
  of nkChckRange:
  of nkStringToCString:
  of nkCStringToString:
  of nkEmpty:
  of nkLambdaKinds
  of nkType:
  of nkStmtList, nkStmtListExpr
  of nkBlockStmt, nkBlockExpr:
  of nkIfStmt, nkIfExpr:
  of nkWhileStmt:
  of nkVarSection, nkLetSection:
  of nkConstSection:
  of nkCaseStmt:
  of nkReturnStmt:
  of nkBreakStmt:
  of nkAsgn:
  of nkFastAsgn:
  of nkDiscardStmt
  of nkAsmStmt:
  of nkTryStmt, nkHiddenTryStmt:
  of nkRaiseStmt:
  of nkPragma:
  of nkProcDef, nkFuncDef, nkMethodDef, nkConverterDef:
  of nkPragmaBlock:
  ]#

proc myProcess(b: PPassContext, n: PNode): PNode =
  result = n
  let m = ESGen(b)
  if passes.skipCodegen(m.config, n): return n
  if m.module == nil: internalError(m.config, n.info, "myProcess")
  let es = ESBackend(m.graph.backend)
  
  if es.ast.mname notin toFilename(m.config, n.info): return # FIXME: this skippes everything not coming from mainmodule
  var transfN = transformStmt(m.graph,m.module,n)
  if transfN.kind in nkGenSkippedKinds: return

  es.ast.add(m.gen(transfN, es.ast))

proc myClose(graph: ModuleGraph; b: PPassContext, n: PNode): PNode =
  if passes.skipCodegen(graph.config, n): return n
  result = myProcess(b, n)
  
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
]#