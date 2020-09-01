import
  ast, astalgo, types, sighashes, msgs, wordrecg, trees, ropes, options, modulegraphs

import md5

from wasm/wasmast import WasmValueType, WasmOpKind

from strutils import toHex, Digits

proc getPragmaStmt*(n: PNode, w: TSpecialWord): PNode =
  case n.kind
  of nkStmtList:
    for i in 0..<n.len:
      result = getPragmaStmt(n[i], w)
      if result != nil: break
  of nkPragma:
    for i in 0..<n.len:
      if whichPragma(n[i]) == w: return n[i]
  else: discard

proc stmtsContainPragma*(n: PNode, w: TSpecialWord): bool =
  result = getPragmaStmt(n, w) != nil


#[
proc mapType(conf: ConfigRef; typ: PType): TCTypeKind =
  ## Maps a Nim type to a C type
  case typ.kind
  of tyNone, tyTyped: result = ctVoid
  of tyBool: result = ctBool
  of tyChar: result = ctChar
  of tyNil: result = ctPtr
  of tySet: result = mapSetType(conf, typ)
  of tyOpenArray, tyArray, tyVarargs, tyUncheckedArray: result = ctArray
  of tyObject, tyTuple: result = ctStruct
  of tyUserTypeClasses:
    doAssert typ.isResolvedUserTypeClass
    return mapType(conf, typ.lastSon)
  of tyGenericBody, tyGenericInst, tyGenericParam, tyDistinct, tyOrdinal,
     tyTypeDesc, tyAlias, tySink, tyInferred, tyOwned:
    result = mapType(conf, lastSon(typ))
  of tyEnum:
    if firstOrd(conf, typ) < 0:
      result = ctInt32
    else:
      case int(getSize(conf, typ))
      of 1: result = ctUInt8
      of 2: result = ctUInt16
      of 4: result = ctInt32
      of 8: result = ctInt64
      else: result = ctInt32
  of tyRange: result = mapType(conf, typ[0])
  of tyPtr, tyVar, tyLent, tyRef:
    var base = skipTypes(typ.lastSon, typedescInst)
    case base.kind
    of tyOpenArray, tyArray, tyVarargs, tyUncheckedArray: result = ctPtrToArray
    of tySet:
      if mapSetType(conf, base) == ctArray: result = ctPtrToArray
      else: result = ctPtr
    else: result = ctPtr
  of tyPointer: result = ctPtr
  of tySequence: result = ctNimSeq
  of tyProc: result = if typ.callConv != ccClosure: ctProc else: ctStruct
  of tyString: result = ctNimStr
  of tyCString: result = ctCString
  of tyInt..tyUInt64:
    result = TCTypeKind(ord(typ.kind) - ord(tyInt) + ord(ctInt))
  of tyStatic:
    if typ.n != nil: result = mapType(conf, lastSon typ)
    else: doAssert(false, "mapType")
  else: doAssert(false, "mapType")

proc mapReturnType(conf: ConfigRef; typ: PType): TCTypeKind =
  #if skipTypes(typ, typedescInst).kind == tyArray: result = ctPtr
  #else:
  result = mapType(conf, typ)
]#

const
  irrelevantForBackend = {tyGenericBody, tyGenericInst, tyGenericInvocation,
                          tyDistinct, tyRange, tyStatic, tyAlias, tySink,
                          tyInferred, tyOwned, tyGenericParam}

const allTypes = {tyNone..tyVoid}
proc mapType*(c: ConfigRef, tt:PType):WasmValueType =
  if tt.isNil: return vtNone
  #echo "#maptyp", tt.kind #,c.typeToYaml(tt)
  if tt.kind == tyVarargs: return vtI32
  
  let t = if not tt.isNil: tt.skipTypes(allTypes-ConcreteTypes) else: tt
  #echo "#maptyp2", t.kind ,c.typeToYaml(tt)
  if t.isNil: return vtNone
  case t.kind:
  of tyEnum:
    result = vtI8
    if t.size > 1: c.internalError("# mapType: enum size > 1 byte: " & $t.size)
  of tyBool, tyChar, tyInt8, tyUInt8:
    result = vtI8
  #TODO:
  of tyInt16, tyUInt16:
    result = vtI16
  of tyInt, tyInt32, tyUInt, tyUInt32,
    tyString, tyPtr, tyRef, tyPointer, tyVar, tyObject, tyTuple, tySet,
    tySequence, tyArray, tyProc:
    result = vtI32
  of tyFloat32:
    result = vtF32
  of tyFloat, tyFloat64:
    result = vtF64
  else:
    c.internalError("mapType: unmapped type kind " & $t.kind)

proc mapStoreKind*(c: ConfigRef, tt:PType): WasmOpKind =
  case c.mapType(tt):
  of vtI8: result = memStore8_I32
  of vtI16: result = memStore16_I32
  of vtI32: result = memStoreI32
  of vtI64: 
    echo "# WASM not sure about i64S"
    result = memStoreI64 # no 64 bit in wasm
  of vtF32: result = memStoreF32
  of vtF64: result = memStoreF64
  else:
    c.internalError("unmapped store for type: " & $tt.kind)

proc mapLoadKind*(c: ConfigRef, tt:PType): WasmOpKind =
  case c.mapType(tt):
  of vtI8: result = memLoad8U_I32 # CHECK: U or S
  of vtI16: result = memLoad16S_I32
  of vtI32: result = memLoadI32
  of vtI64: 
    echo "# WASM not sure about i64L"
    result = memLoadI64
  of vtF32: result = memLoadF32
  of vtF64: result = memLoadF64
  else:
    c.internalError("unmapped load " & $(c.mapType(tt)) & " for type: " & $tt.kind)

proc isPtrLike*(t:TTypeKind): bool =
  t in {tyObject, tyArray, tyVar, tyPtr, tyString, tySequence}

proc hasResult*(prc:PSym): bool = 
  #assert(prc.kind == skProc skFunc)
  prc.ast.len > 6

proc alignTo4*(n:Natural): Natural = (n + 3) and not(0x03)
  # Next multiple of 4 or return n if n is already a multiple of 4

proc mangle*(name: string): string =
  result = newStringOfCap(name.len)
  var start = 0
  if name[0] in Digits:
    result.add("X" & name[0])
    start = 1
  var requiresUnderscore = false
  template special(x) =
    result.add x
    requiresUnderscore = true
  for i in start..(name.len-1):
    let c = name[i]
    case c
    of 'a'..'z', '0'..'9', 'A'..'Z':
      add(result, c)
    of '_':
      # we generate names like 'foo_9' for scope disambiguations and so
      # disallow this here:
      if i > 0 and i < name.len-1 and name[i+1] in Digits:
        discard
      else:
        add(result, c)
    of '$': special "dollar"
    of '%': special "percent"
    of '&': special "amp"
    of '^': special "roof"
    of '!': special "emark"
    of '?': special "qmark"
    of '*': special "star"
    of '+': special "plus"
    of '-': special "minus"
    of '/': special "slash"
    of '=': special "eq"
    of '<': special "lt"
    of '>': special "gt"
    of '~': special "tilde"
    of ':': special "colon"
    of '.': special "dot"
    of '@': special "at"
    of '|': special "bar"
    else:
      add(result, "X" & toHex(ord(c), 2))
      requiresUnderscore = true
  if requiresUnderscore:
    result.add "_"

proc mangleName*(s:PSym):string = 
  echo "# mangleName ", s.name.s, " " , s.kind # ,"\n",typeToyaml s.typ
  result = (s.name.s & $s.hashProc).mangle
  #result = (s.name.s & "_" & s.typ.typeToString).mangle
  #[case s.kind:
  of skType:
    result = s.name.s.mangle & $s.typ.kind
  of skProc:
    result = s.name.s.mangle
    for s in s.typ.n:
  else:
    result = s.name.s.mangle
    for tson in s.typ.sons:
      if not tson.isNil:
        result.add("_" & $tson.kind)]#