import
  ast, astalgo, options, msgs, idents, types, passes,
  ropes, wordrecg, modulepaths, transf, hashes,
  tables, os, strutils, pathutils,
  wasm/[wasmast, wasmstructure, wasmencode, wasmnode, wasmleb128, wasmrender], wasmutils,
  renderer

from math import ceil,log2

from modulegraphs import ModuleGraph, PPassContext

# TODO: more flexibility in glue, maybe save it as config in context

type
  WasmGen = ref object of PPassContext
    s: PSym # symbol of the current module, taken from myOpen
    graph: ModuleGraph
    config: ConfigRef
    #sigConflicts: CountTable[SigHash]
  
  Backend = ref object of RootRef
    nimInitBody: seq[WasmNode] # sequence of initializer expressions. for use in start sec
    nextImportIdx: Natural # function index space ( doesn't account for hoisting of imported procs )
    nextFuncIdx: Natural # the function index space (only for non-imported funcs)
    nextGlobalIdx: Natural # the global index space
    nextMemIdx: Natural # the linear memory index space
    nextTableIdx: Natural # the table index space
    m : WAsmModule #current module
    generatedProcs: Table[PSym,tuple[id:int,imported:bool]] # name, funcIdx
    generatedTypeInfos: Table[string, int32] # name, location in memory
    locs: tuple[stack,heap:int32] # stack pointers location, used in procs? stack is Used as compile time stack ptr


const
  irrelevantForBackend = {tyGenericBody, tyGenericInst, tyGenericInvocation,
                          tyDistinct, tyRange, tyStatic, tyAlias, tySink,
                          tyInferred, tyOwned}

#proc typeName(typ: PType): Rope =
#  let typ = typ.skipTypes(irrelevantForBackend)

proc newBackend(modulename:string): Backend =
  result = Backend(
    generatedProcs: initTable[PSym,tuple[id:int,imported:bool]](),
    generatedTypeInfos: initTable[string,int32](),
    )
  
  result.nextFuncIdx = 0
  result.nextImportIdx = 0
  result.nextGlobalIdx = 0
  result.nextTableIdx = 0
  # 4 byte aligned, reserve 8 bytes to store the stack pointer
  # This mean effective address start at 12?
  result.nextMemIdx = 0
  result.nimInitBody = newSeq[WasmNode]()
  # this will be updated since the first module name is not the main one
  result.m = newModule(modulename) 
  #initialize the module's sections
  result.m.memory = newMemory()
  add result.m.exports, newExport(0, ekMemory, "$memory")
  result.locs = (12'i32, 0'i32)

proc updateBackendName(b: Backend, name:string) = b.m.name = name
proc moveStackPtrBy(b:Backend, bytes:BiggestInt) =
  b.locs.stack += bytes.int32

proc stackptr(b:Backend): int = b.locs.stack

proc updateLoc(s: PSym, loc: int, kind: TLocKind) =
  s.loc.k = kind
  s.loc.pos = loc
  s.loc.r = loc.rope # for debug purposes

proc getLoc(s: PNode): int =
  # TODO: if sym is a param, this should be:
  # result = newGet(woGetLocal, s.position) or something like that
  if s.sym.loc.k == locGlobalVar:
    result = s.sym.loc.pos
  else:
    echo "#getloc: TODO: other than global"

proc hash(s:PSym): Hash = hash(s.mangleName)

proc symLoc(s: PNode): WasmNode =
  # TODO: if sym is a param, this should be:
  # result = newGet(woGetLocal, s.position) or something like that
  if s.kind == nkSym:
    if s.sym.kind == skParam:
        result = newGet(woGetLocal, s.sym.position)
    elif s.sym.loc.k == locGlobalVar:
      result = newGet(woGetGlobal, s.sym.loc.pos)
    else:
      echo "#symloc: TODO: other than global"
  else:
    echo "#NOT A SYM for Symloc"

proc hasProc(b: Backend, sym: PSym): bool =
  sym in b.generatedProcs

proc getProc(b: Backend, sym: PSym): tuple[id: int, imported: bool] =
  b.generatedProcs[sym]

# this is to persist the backend between modules, 
# otherwise it would get reinited at every myOpen of a new module
# TODO: move logic for this  in open...
var backend: Backend = newBackend("main")

proc newWasmGen(s:PSym, g: ModuleGraph): WasmGen =
  result = WasmGen(s: s, graph:g, config: g.config)

proc storeLit(b: Backend, n: PNode, conf: ConfigRef): WasmNode {.deprecated.} =
  # n0: sym / n1: typ|empty / n2: val
  #echo "#STORE ", conf.treeToYaml(n)
  var typ = n.sons[1].typ
  if typ.isNil: typ = n.sons[0].sym.typ
  echo "#STORE type ", typ.kind
  # a var section stores its data in `data` or has an
  # initialization expr, so no node is returned.
  var dataseg: seq[byte] = newSeq[byte]()
  result = newOpList() # FIXME: remove since it's not used? May be useful for str/array etc
  if not(typ.kind notin ConcreteTypes):
    # get a concrete type we can use to decide how to store data
    typ = typ.skipTypes(abstractInst)
  
  case typ.kind:
  of tyBool, tyChar, tyEnum, tyInt..tyInt32: # TODO: fix store size when size < 4bytes
    # for tyEnum, n[2] can be nkSym kind skEnumField
    if n.sons[2].kind == nkSym and n.sons[2].sym.kind == skEnumField:
      # in this case, the ordinal value of the enum is in sym.position
      dataseg = n.sons[2].sym.position.int32.toBytes
    else:
      dataseg = n.sons[2].getInt.toInt32.toBytes
  of tyString, tyCString, tyPtr, tyRef, tyVar, tyProc, tyPointer:
    echo "#STORE unhandled type: ", $typ.kind
  of tyFloat32:
    dataseg = n.sons[2].getFloat.float32.toBytes
  of tyFloat, tyFloat64:
    dataseg = n.sons[2].getFloat.float64.toBytes
  of tyUInt..tyUInt32:
    dataseg = n.sons[2].getInt.toUInt32.toBytes
  of tyArray, tyOpenArray, tyObject, tySet, tyTuple, tyRange, 
    tyLent, tySequence, tyInt64, tyUInt64, tyFloat128:
    echo "#STORE shouldn't be possible: illegal ", $typ.kind
  else:
    echo "#STORE unhandled type: ", $typ.kind
  
  b.m.data.add(newData(b.stackptr, dataseg, n.sons[0].sym.name.s))
  b.moveStackPtrBy(dataseg.len) # TODO: alignTo4 ??? 

const nkGenSkippedKinds = { nkCommentStmt, nkPragma, nkEmpty, 
                            nkTemplateDef, nkFuncDef, nkProcDef, nkMethodDef, 
                            nkIteratorDef, nkMacroDef, nkIncludeStmt, 
                            nkImportStmt, nkExportStmt, nkExportExceptStmt, 
                            nkImportExceptStmt, nkImportAs, nkConverterDef,
                            nkIncludeStmt, nkTypeSection}#, nkWhenStmt, nkWhenExpr }

const nkSectionKinds = {nkVarSection, nkConstSection, nkLetSection}

proc gen(w: WasmGen, n: PNode, conf: ConfigRef, parentKind: TNodeKind=nkNone): WasmNode

#[
    nkCommand,            # a call like ``p 2, 4`` without parenthesis
    nkCall,               # a call like p(x, y) or an operation like +(a, b)
    nkCallStrLit,         # a call with a string literal
                          # x"abc" has two sons: nkIdent, nkRStrLit
                          # x"""abc""" has two sons: nkIdent, nkTripleStrLit
    nkInfix,              # a call like (a + b)
    nkPrefix,             # a call like !a
    nkPostfix,            # something like a! (also used for visibility)
    nkHiddenCallConv,     # an implicit type conversion via a type converter

    nkExprEqExpr,         # a named parameter with equals: ''expr = expr''
    nkExprColonExpr,      # a named parameter with colon: ''expr: expr''
    nkIdentDefs,          # a definition like `a, b: typeDesc = expr`
                          # either typeDesc or expr may be nil; used in
                          # formal parameters, var statements, etc.
    nkVarTuple,           # a ``var (a, b) = expr`` construct
    nkPar,                # syntactic (); may be a tuple constructor
    nkObjConstr,          # object constructor: T(a: 1, b: 2)
    nkCurly,              # syntactic {}
    nkCurlyExpr,          # an expression like a{i}
    nkBracket,            # syntactic []
    nkBracketExpr,        # an expression like a[i..j, k]
    nkPragmaExpr,         # an expression like a{.pragmas.}
    nkRange,              # an expression like i..j
    nkDotExpr,            # a.b
    nkCheckedFieldExpr,   # a.b, but b is a field that needs to be checked
    nkDerefExpr,          # a^
    nkIfExpr,             # if as an expression
    nkElifExpr,
    nkElseExpr,
    nkLambda,             # lambda expression
    nkDo,                 # lambda block appering as trailing proc param
    nkAccQuoted,          # `a` as a node

    nkTableConstr,        # a table constructor {expr: expr}
    nkBind,               # ``bind expr`` node
    nkClosedSymChoice,    # symbol choice node; a list of nkSyms (closed)
    nkOpenSymChoice,      # symbol choice node; a list of nkSyms (open)
    nkHiddenStdConv,      # an implicit standard type conversion
    nkHiddenSubConv,      # an implicit type conversion from a subtype
                          # to a supertype
    nkConv,               # a type conversion
    nkCast,               # a type cast
    nkStaticExpr,         # a static expr
    nkAddr,               # a addr expression
    nkHiddenAddr,         # implicit address operator
    nkHiddenDeref,        # implicit ^ operator
    nkObjDownConv,        # down conversion between object types
    nkObjUpConv,          # up conversion between object types
    nkChckRangeF,         # range check for floats
    nkChckRange64,        # range check for 64 bit ints
    nkChckRange,          # range check for ints
    nkStringToCString,    # string to cstring
    nkCStringToString,    # cstring to string
                          # end of expressions

    nkAsgn,               # a = b
    nkFastAsgn,           # internal node for a fast ``a = b``
                          # (no string copy)
    nkGenericParams,      # generic parameters
    nkFormalParams,       # formal parameters
    nkOfInherit,          # inherited from symbol

    nkImportAs,           # a 'as' b in an import statement
    nkProcDef,            # a proc
    nkMethodDef,          # a method
    nkConverterDef,       # a converter
    nkMacroDef,           # a macro
    nkTemplateDef,        # a template
    nkIteratorDef,        # an iterator

    nkOfBranch,           # used inside case statements
                          # for (cond, action)-pairs
    nkElifBranch,         # used in if statements
    nkExceptBranch,       # an except section
    nkElse,               # an else part
    nkAsmStmt,            # an assembler block
    nkPragma,             # a pragma statement
    nkPragmaBlock,        # a pragma with a block
    nkIfStmt,             # an if statement
    nkWhenStmt,           # a when expression or statement
    nkForStmt,            # a for statement
    nkParForStmt,         # a parallel for statement
    nkWhileStmt,          # a while statement
    nkCaseStmt,           # a case statement
    nkTypeSection,        # a type section (consists of type definitions)
    nkVarSection,         # a var section
    nkLetSection,         # a let section
    nkConstSection,       # a const section
    nkConstDef,           # a const definition
    nkTypeDef,            # a type definition
    nkYieldStmt,          # the yield statement as a tree
    nkDefer,              # the 'defer' statement
    nkTryStmt,            # a try statement
    nkFinally,            # a finally section
    nkRaiseStmt,          # a raise statement
    nkReturnStmt,         # a return statement
    nkBreakStmt,          # a break statement
    nkContinueStmt,       # a continue statement
    nkBlockStmt,          # a block statement
    nkStaticStmt,         # a static statement
    nkDiscardStmt,        # a discard statement
    nkStmtList,           # a list of statements
    nkImportStmt,         # an import statement
    nkImportExceptStmt,   # an import x except a statement
    nkExportStmt,         # an export statement
    nkExportExceptStmt,   # an 'export except' statement
    nkFromStmt,           # a from * import statement
    nkIncludeStmt,        # an include statement
    nkBindStmt,           # a bind statement
    nkMixinStmt,          # a mixin statement
    nkUsingStmt,          # an using statement
    nkCommentStmt,        # a comment statement
    nkStmtListExpr,       # a statement list followed by an expr; this is used
                          # to allow powerful multi-line templates
    nkBlockExpr,          # a statement block ending in an expr; this is used
                          # to allow powerful multi-line templates that open a
                          # temporary scope
    nkStmtListType,       # a statement list ending in a type; for macros
    nkBlockType,          # a statement block ending in a type; for macros
                          # types as syntactic trees:

    nkWith,               # distinct with `foo`
    nkWithout,            # distinct without `foo`

    nkTypeOfExpr,         # type(1+2)
    nkObjectTy,           # object body
    nkTupleTy,            # tuple body
    nkTupleClassTy,       # tuple type class
    nkTypeClassTy,        # user-defined type class
    nkStaticTy,           # ``static[T]``
    nkRecList,            # list of object parts
    nkRecCase,            # case section of object
    nkRecWhen,            # when section of object
    nkRefTy,              # ``ref T``
    nkPtrTy,              # ``ptr T``
    nkVarTy,              # ``var T``
    nkConstTy,            # ``const T``
    nkMutableTy,          # ``mutable T``
    nkDistinctTy,         # distinct type
    nkProcTy,             # proc type
    nkIteratorTy,         # iterator type
    nkSharedTy,           # 'shared T'
                          # we use 'nkPostFix' for the 'not nil' addition
    nkEnumTy,             # enum body
    nkEnumFieldDef,       # `ident = expr` in an enumeration
    nkArgList,            # argument list
    nkPattern,            # a special pattern; used for matching
    nkHiddenTryStmt,      # a hidden try statement
    nkClosure,            # (prc, env)-pair (internally used for code gen)
    nkGotoState,          # used for the state machine (for iterators)
    nkState,              # give a label to a code section (for iterators)
    nkBreakState,         # special break statement for easier code generation
    nkFuncDef,            # a func
    nkTupleConstr         # a tuple constructor

]#
proc exportOrUsed(s: PSym): bool =
  ( s.flags.contains(sfExported) and 
    s.skipGenericOwner.flags.contains(sfMainModule)
  ) or s.flags.contains(sfUsed)
proc wasmConstToBytes(conf:ConfigRef, w: WasmNode, seqlen = BiggestInt(-1)): seq[byte] =
  result = @[] 
  case w.kind
  of constI32, constI64:
    result.add(w.intVal.int32.signedLEB128)
  of constUI32, constUI64:
    result.add(w.uintVal.uint32.unsignedLEB128)
  of constF32:
    result.add(w.floatVal.float32.toBytes)
  of constF64:
    result.add(w.floatVal.float64.toBytes)
  else:
    conf.internalError("Not a const for constToBytes: " & $w.kind)
  if seqlen != -1: #
    result.setLen(seqlen)

  #echo "size wasmconst ", result.len, " exp ", seqlen
proc getMagicOp(c: ConfigRef, m: TMagic): WasmOpKind =
  result = case m:
  of mAddI, mAddU, mSucc: ibAdd32
  of mSubI, mSubU, mPred: ibSub32
  of mMulI, mMulU: ibMul32
  of mDivI: ibDivS32
  of mDivU: ibDivU32
  of mModI: ibRemS32
  of mModU: ibRemU32
  of mAnd, mBitandI: ibAnd32
  of mOr, mBitorI: ibOr32
  of mXor, mBitxorI: ibXor32
  of mShlI: ibShl32
  of mShrI: ibShrS32
  of mNot: itEqz32
  of mEqI, mEqEnum, mEqCh, mEqB,
    mEqRef, mEqStr, mEqSet: irEq32  
    # If addr strA == addr strB, they are the same string
  of mLtU: irLtU32
  of mLtI, mLtEnum, mLtStr, mLtCh, mLtSet, mLtB, mLtPtr: irLtS32
  of mLeU: irLeU32
  of mLeI, mLeEnum, mLeStr, mLeCh, mLeSet, mLeB, mLePtr: irLeS32
  of mEqF64: frEq64
  of mLeF64: frLe64
  of mLtF64: frLt64
  of mAddF64: fbAdd64
  of mSubF64: fbSub64
  of mMulF64: fbMul64
  of mDivF64: fbDiv64
  else: woNop
  if result == woNop:
    c.internalError("unmapped magic op: " & $m)

proc getFloat32Magic(c: ConfigRef, m:TMagic):WasmOpKind =
  result = case m:
  of mEqF64: frEq32
  of mLeF64: frLe32
  of mLtF64: frLt32
  of mAddF64: fbAdd32
  of mSubF64: fbSub32
  of mMulF64: fbMul32
  of mDivF64: fbDiv32
  else: woNop
  if result == woNop: c.internalError("unmapped float magic: " & $m) 

const UnaryMagic = {mNot}    
const BinaryMagic = {mAddI,mAddU,mSubI,mSubU,mMulI,mMulU,mDivI,mDivU,mSucc,mPred,
  mModI,mModU, mAnd, mOr, mXor, mShlI, mShrI, mLtU, mLeU,
  mEqI, mEqEnum, mEqCh, mEqB, mEqRef, mEqStr, mEqSet,
  mLtI, mLtEnum, mLtStr, mLtCh, mLtSet, mLtB, mLtPtr,
  mLeI, mLeEnum, mLeStr, mLeCh, mLeSet, mLeB, mLePtr,
  mBitandI, mBitorI, mBitxorI}
const FloatsMagic = {mEqF64, mLeF64, mLtF64, mAddF64, mSubF64, mMulF64, mDivF64}

proc callMagic(w:WasmGen, n: PNode, magic:TMagic): WasmNode =
  echo "#MAGIC: ", magic
  let b = w.graph.backend.Backend
  case magic:
  #[# the idea for string conversion of numbers:
    # push values to the memory, then give the pointer to that memory to echo
    let vallen = if magic==mIntToStr: 4'i32 else: 8'i32
    let storekind = if magic==mIntToStr: memStoreI32 else: memStoreF64
    result = newOpList(
      newLoad(memLoadI32, 0, 1, newConst(4'i32)),
      newStore(
        memStoreI32, 
        newConst(vallen), 
        0, newLoad(memLoadI32, 0, 1, newConst(4'i32))
      ),
      newStore(
        storekind, w.gen(n.sons[1],w.config), 0, 
        newAdd32(
          newLoad(memLoadI32, 0, 1, newConst(4'i32)),
          newConst(4'i32)
        ), # stack base
        # 4 bytes offset since that's the len of the ptr
        
      ), # TODO: move stackptr
      
    )]#
    #result = w.gen(n.sons[1],w.config) # js echo doesn't care
  of mArrToSeq:
    result = newConst(b.stackptr)
    let sq = n[1].len.int32.toBytes & n[1].len.int32.toBytes 
    b.m.data.add(
      newData(
        b.stackptr, sq, "seq"
      )
    )
    b.moveStackPtrBy(sq.len)

    for son in n[1]:
      if son.kind in nkLiterals:  
        let bytes = w.config.wasmConstToBytes(w.gen(son, w.config, n.kind), w.config.getSize(n[1].typ.lastSon))
        b.m.data.add(
          newData(
            b.stackptr, 
            bytes, "val"
          )
        )
        b.moveStackPtrBy(bytes.len)
      else:
        # it's some pointer indirection, store it and move by 4bytes
        # TODO:should make copies of non shallow types
        # FIXME: the store happens too soon. How can I sync it with the program?
        if son.typ == nil:
          w.config.internalError("Nil type for son in arrtoseq")
        b.nimInitBody.add(
          newStore(
            w.config.mapStoreKind(son.typ), w.gen(son, w.config, n.kind), 0, newConst(b.stackptr)
          )
        )
        b.moveStackPtrBy(son.typ.size) #size of a pointer TODO: read it from conf?
  of UnaryMagic:
    result = newUnaryOp(w.config.getMagicOp(magic), w.gen(n[1], w.config))
  of BinaryMagic:
    result = newBinaryOp(w.config.getMagicOp(magic), w.gen(n[1], w.config), w.gen(n[2], w.config))
  of FloatsMagic:
    if n.typ.kind == tyFloat32: #CHECK: why did I have this comment?
      # or (n.typ.kind == tyBool and n[1].typ.kind == tyFloat32): 
      # the bool part is because otherwise 1'f32+2.0 would use f32 arithm
      result = newBinaryOp(w.config.getFloat32Magic(magic), w.gen(n[1], w.config), w.gen(n[2], w.config))
    else:
      result = newBinaryOp(w.config.getMagicOp(magic), w.gen(n[1], w.config), w.gen(n[2], w.config))
  else: 
    echo w.config.treeToYaml(n)
    w.config.internalError("# callMagic unhandled magic: " & $magic)
  #[
  of mAddr:
    #echo $(s.magic), w.config.treeToYaml(n[1], 0, 1)
    #echo $(s.magic), w.config.symToYaml(n[1].sym)
    return newConst(n[1].sym.offset)
  of mBitnotI:
    return newBinaryOp(ibXor32, w.gen(n[1]), newConst(-1.int32))
  of mNew:
    if w.generatedProcs.hasKey(s.mangleName):
      return newCall(w.generatedProcs[s.mangleName].id, w.genSymLoc(n[1].sym), false)

    # new gets passed a ref, so local 0 is the location of the ref to the
    # object to initialize.
    #echo treeToYaml n[1]
    let size = w.config.getSize(n[1].typ.lastSon).alignTo4
    var magicbody = newOpList()
    magicbody.sons.add([
      # heap ptr points to next free byte in memory. Use it to
      # move the pointed-to location of the ref to somewhere free
      newStore(
        memStoreI32, newLoad(memLoadI32, 0, 1, newConst(heapPtrLoc)), 
        0, newGet(woGetLocal, 0)
      ),
      # move heap ptr by `size` bytes.
      # the assumption is that everything after heap ptr is free to take
      newStore(
        memStoreI32, newBinaryOp(
          ibAdd32, newLoad(memLoadI32, 0, 1, newConst(heapPtrLoc)), newConst(size.int32)
        ),  
        0, newConst(heapPtrLoc)
      )
    ])
    
    w.m.functions.add(
      newFunction(
        w.nextFuncIdx, newType(vtNone, vtI32), magicbody, @[], s.mangleName,
        s.flags.contains(sfExported)
      )
    )
    result = newCall(w.nextFuncIdx, w.genSymLoc(n[1].sym), false)
    w.generatedProcs.add(s.mangleName, (w.nextFuncIdx,false)) 
    inc w.nextFuncIdx
  of mReset:
    if w.generatedProcs.hasKey(s.mangleName):
      return newCall(w.generatedProcs[s.mangleName].id, w.genSymLoc(n[1].sym), false)
    var loopBody = newWANode(opList)

    loopBody.sons.add(
      newStore(
        memStoreI32,
        newConst(0'i32),
        0'i32,
        newGet(woGetLocal, 1)
      )
    )
    loopBody.sons.add(
      newSet(
        woSetLocal, 1'i32,
        newBinaryOp(
          ibAdd32,
          newGet(woGetLocal, 1),
          # FUTURE FIXME: when some types have size <4, this needs to be reworked too
          newConst(4'i32)
        )
      )
    )

    var magicbody = newWhileLoop(
          newBinaryOp(
            irLtU32,
            newGet(woGetLocal, 1),
            newBinaryOp(
              ibAdd32,
              newGet(woGetLocal, 0),
              newConst(w.config.getSize(n[0].typ).alignTo4.int32)
            )
          ),
          loopBody
        )
        
    w.m.functions.add(
      newFunction(
        w.nextFuncIdx, newType(vtNone, vtI32), magicbody, @[vtI32], s.mangleName,
        s.flags.contains(sfExported)
      )
    )
    
    result = newCall(w.nextFuncIdx, w.genSymLoc(n[1].sym), false)
    
    w.generatedProcs.add(s.mangleName,(w.nextFuncIdx.int,false))
    inc w.nextFuncIdx

  of mDotDot:
    let t = n[1].typ.skipTypes(abstractVarRange)
    if n.len > 2:
      result = newOpList(
        newStore(
          w.config.mapStoreKind(t),
          w.gen(n[1]), 0'i32, newConst(w.nextMemIdx.int32)
        ),
        newStore(
          w.config.mapStoreKind(t),
          w.gen(n[2]), 0'i32, newConst((w.nextMemIdx+w.config.getSize(t).alignTo4).int32)
        ),
        newLoad(w.config.mapLoadKind(t), 0, 1, newConst(w.nextMemIdx.int32))  # FIXME: this shouldn't be necessary
                                                                    # basically, load and store in itself       
      )
    else:
      result = newOpList(
        newStore(
          w.config.mapStoreKind(t),
          w.gen(n[1]), 0'i32, newConst((w.nextMemIdx+w.config.getSize(t).alignTo4).int32)
        ),
        newLoad(w.config.mapLoadKind(t), 0, 1, newConst(w.nextMemIdx.int32))
      )
  of mSizeOf:
    result = newConst(w.config.getSize(n[1].typ).alignTo4.int32)
  of mInc, mDec:
    result = newOpList(
      newStore(
        memStoreI32, 
        newBinaryOp(
          if s.magic == mInc: ibAdd32 else: ibSub32,
          w.gen(n[1]), w.gen(n[2])
        ), 0, 
        w.genSymLoc(n[1].sym)        
      )     
    )
  of mNewSeq:
    #echo "# mNewSeq"
    #echo treeToYaml n
    # we receive the index to a ptr.We then need to reserve a block of memory for the
    # len+data of the seq. Since a default len is always know, we can store it.
    # remember to return the pointer you initially got
    if not w.generatedProcs.hasKey(s.mangleName):      
      var magicbody = newOpList(
        newStore( # store len at pointed to
          memStoreI32,
          newGet(woGetLocal, 1),
          0, # offset
          newGet(woGetLocal, 0)
        ),
        newStore( # move heap ptr
          memStoreI32,
          newAdd32(
            newLoad(memLoadI32, 0, 1, newConst(heapPtrLoc.int32)),
            newAdd32(
              newConst(wasmPtrSize.int32),
              newMul32(
                newConst(w.config.getSize(n[1].sym.typ.lastSon).alignTo4.int32),
                newGet(woGetLocal, 1)
              )
            )
          ),
          0, newConst(heapPtrLoc.int32)
        )
      )
      
      w.m.functions.add(
        newFunction(
          w.nextFuncIdx, newType(vtNone, vtI32, vtI32), magicbody, @[], s.mangleName,
          s.flags.contains(sfExported)
        )
      )
      w.generatedProcs.add(s.mangleName, (w.nextFuncIdx,false)) 
      inc w.nextFuncIdx
    
    # echo "n1: ",treeToYaml n[1]
    # I don't like special casing here.
    if n[1].kind == nkSym and n[1].sym.offset>0:
      result = newCall(w.generatedProcs[s.mangleName].id, 
        newLoad(memLoadI32, 0,1, w.genSymLoc(n[1].sym)), 
        w.gen(n[2]), false
      )
    else:
      result = newCall(w.generatedProcs[s.mangleName].id, 
        newLoad(memLoadI32, 0,1, newConst(heapPtrLoc)), # this is not really ideal, it works because we assume
                                                        # newseq(len):res and so result is at local #1
        w.gen(n[2]), false
      )
    
  of mNewSeqOfCap:
    #echo "# mNewSeqOfCap"
    #echo w.config.treeToYaml(n)
    w.config.internalError("# TODO: mNewSeqOfCap")
    # we receive the len of the block to reserve.
    # Since this proc is completely a magic, we can do everything here.
    # remember to return the pointer you initially got
    result = newOpList(
      newLoad(memLoadI32, 0, 1, newConst(heapPtrLoc.int32)), # this is the returned loc
      newStore( # move heap ptr
        memStoreI32,
        newAdd32(
          newLoad(memLoadI32, 0, 1, newConst(heapPtrLoc.int32)),
          newAdd32(
            newConst(wasmPtrSize.int32),
            newMul32(
              newConst(w.config.getSize(n.typ).alignTo4.int32),
              w.gen(n[1])
            )
          )
        ),
        0, newConst(heapPtrLoc.int32)
      )
    )
  of mLengthSeq, mLengthStr:
    result = newLoad(memLoadI32, 0, 1, w.gen(n[1]))
  of mChr:
    result = w.gen(n[1][0]) # skip nkChckRange for now... FIXME: 
  ]#
######################
proc genProc(w: WasmGen, n: PNode, conf: ConfigRef) =
  echo "#GNP: ", $n.kind, " module: ", conf.toFilename(n.info.fileIndex)
  #echo conf.treeToYaml(n)
  #echo conf.symToYaml(n.sym)
  let procDef = n.sym.ast
  #echo conf.typeToYaml(n.sym.typ)
  assert(procDef.kind == nkProcDef)
  let b = Backend(w.graph.backend)
  # Build the type signature of this proc in wasm land
  # note that for type sign purposes, the prc.sym.typ.sons are better than using formalparams of ast
  let procparams = n.sym.typ.sons # the list of types for params

    # body = s.getBody() TODO:
  
  var proctype : WasmType #= newType(rs=res) # The complete type of the proc in wasm land
    
  for i, par in procparams:
    if i == 0:
      proctype = newType(rs=conf.mapType(par)) # instantiate the proc type with the result type
      continue # move to next par
    proctype.params.add(conf.mapType(par))

  if n.sym.flags.contains(sfImportc):
    # an imported proc (from wasmglue.cfg)
    let pragmas = procDef[pragmasPos]
    let 
      glueImport = pragmas.getPragmaStmt(wHeader) # get the header (glue) from which to import
      procImport = pragmas.getPragmaStmt(wImportc) # name of the proc to import from js
    #echo conf.treeToYaml(glueImport)
    #echo conf.treeToYaml(procImport)
    let
      headername = glueImport[1].getStr
      importcname = procImport[1].getStr
    
    b.m.imports.add(
      newImport(
        b.nextImportIdx, ekFunction, headername, importcname, n.sym.name.s, proctype, n.sym.flags.contains(sfExported)
      )
    )
    # the id of the proc is the import id, because we can then hoist it in a later phase
    # by simply having non-imports start from last(importId), eg id = nextImportIdx+nextFuncIdx
    b.generatedProcs[n.sym] = (b.nextImportIdx, true)
    inc b.nextImportIdx
  else:
    echo "#GNP: nim proc aren't really generated yet, proc: ", n.sym.name.s, " module: ", conf.toFilename(n.info.fileIndex)
    # TODO:
    var wasmProcBody: WasmNode
    var transfBody = transformBody(w.graph, procDef[namePos].sym, cache=false)
    echo "#working on transfbody:"#, conf.treeToYaml(transfBody)
    echo renderTree(transfBody)
    wasmProcBody = w.gen(transfBody, conf)
    b.m.functions.add(
      newFunction(
        b.nextFuncIdx, proctype,
        wasmProcBody, @[proctype.res]#[params?]#, procDef[namePos].sym.name.s, 
        procDef[namePos].sym.flags.contains(sfExported)
      )
    )
    
    b.generatedProcs[n.sym] = (b.nextFuncIdx, false)
    inc b.nextFuncIdx
    
    #echo conf.treeToYaml(transfBody) 

proc genLit(w: WasmGen, n: PNode, conf: ConfigRef, parentKind: TNodeKind): WasmNode =
  # General idea: if it's a numeral(int, float, bool...) use const and pass
  # it directly, otherwise store it in data and pass a pointer to the beginning
  echo "#GNL literal of kind ", n.kind
  let b = Backend(w.graph.backend)  
  var typ = n.typ
  echo "#LOAD type ", typ.kind
  case n.kind:
  of nkLiterals-(nkFloatLiterals+nkStrKinds):
    # Integer like
    if n.typ.kind in tyUInt..tyUInt64:
      result = newConst(n.getInt.toUInt32)
    else:
      result = newConst(n.getInt.toInt32) # TODO: differnt int / kinds
  of nkFloatLiterals:
    # Floats
    if n.typ.kind == tyFloat32:
      result = newConst(n.getFloat.float32)
    else:
      result = newConst(n.getFloat.float64) # float 128??
    # a string literal is basically an array of bytes? TODO:
  of nkStrKinds:
    # strings are a pointer to len+reservered+data
    # so pointer is returned as result, the rest is put in data
    result = newConst(b.stackptr)
    let str = n.getStr.len.int32.toBytes & n.getStr.len.int32.toBytes & (n.getStr).toBytes
    b.m.data.add(
      newData(
        b.stackptr, str, n.getStr
      )
    )
    b.moveStackPtrBy(str.len)
  else:
    conf.internalError "#GNL TODO other literals"

proc genAsgn(w: WasmGen, lhs, rhs: PNode, conf: ConfigRef,): WasmNode =
  #TODO:,
  echo conf.treeToYaml(lhs)
  echo conf.treeToYaml(rhs)
  var ns = lhs.skipHidden()
  
  if ns.kind != nkSym: 
    conf.internalError("# asgn not to a sym but " & $ns.kind)
  # TODO: use loc.k to know how to store
  if ns.sym.owner.kind == skModule: # globals
    if ns.sym.typ.kind == tyVar:
      # need to treat it as a pointer
      result = newStore(conf.mapStoreKind(ns.sym.typ.skipTypes({tyVar})),w.gen(rhs, conf, nkAsgn), 0, ns.symLoc)
    else:
      result = newSet(woSetGlobal, ns.getLoc, w.gen(rhs, conf, nkAsgn))
  elif ns.sym.owner.kind == skProc: # locals
    if ns.sym.typ.kind == tyVar:
      # need to treat it as a pointer
      result = newStore(conf.mapStoreKind(ns.sym.typ.skipTypes({tyVar})),w.gen(rhs, conf, nkAsgn), 0, ns.symLoc)
    elif ns.sym.kind == skResult:
      result = w.gen(rhs, conf, nkAsgn)
    else:
      result = newSet(woSetLocal, ns.getLoc, w.gen(rhs, conf, nkAsgn))
  else:
    conf.internalError("# asgn: owner.kind not proc or module " & $ns.sym.owner.kind)


proc genCall(w: WasmGen, n: PNode, conf: ConfigRef, parentKind: TNodeKind=nkNone): WasmNode =
  # 0-> proc sym, 1..->arg(s)
  echo "#GCL call kind ", n.kind
  let b = Backend(w.graph.backend)

  if n.sons[0].sym.magic != mNone:
    return callMagic(w, n, n.sons[0].sym.magic)
    

  # TODO: inlined procs??
  #[
    if n.sons[0].sym.typ.callConv == ccInline: # means this is an inlined proc?
    let transfbody = transformBody(w.graph, n.sons[0].sym, true)
    echo "#working on inlined proc"
    echo renderTree(transfbody)
    echo "# AN INLINED PROC? \n", conf.treeToYaml(n.sons[0].sym.transformedBody)
    # problem: in inlined procs, skparam shouldn't be used
    return w.gen(transfbody, conf, n.sons[0].kind)
  ]#

  if not b.hasProc(n.sons[0].sym) :
    #FIXME: generate proc for non imported procs
    w.genProc(n.sons[0], conf)
  
  let (id, isImport) = b.getProc(n.sons[0].sym)
  
  var args : seq[WasmNode] = @[]
  #if n.sons[0].sym.ast[resultPos].kind != nkEmpty:
  #  args.add(newConst(0'i32)) # the return
  var toUpdate: seq[PNode] = @[]
  # we may need to generate a set global after execution to update var types params 
  if n.sons.len > 1: # at least 1 argument
    for i, arg in n.sons:
      if i == 0: continue # skip first arg (should be nkSym of the proc)
      echo "#ARGtyp: ", arg.typ.kind
      #echo conf.typeToYaml(arg.typ)
      if arg.typ.kind == tyVar and not arg.typ[0].kind.isPtrLike : toUpdate.add(arg.skipHidden)
      args.add(w.gen(arg, conf, n.kind))
  if toUpdate.len == 0:
    result=newCall(id, args, isImport)
  else:
    result.sons.add(newCall(id, args, isImport))
    # update var params
    for node in toUpdate:
      if node.kind == nkSym: # updating a sym
        let sym = node.sym
        result.sons.add(
          newSet( # FIXME: wrong wrong wrong, need to move the stackpointer
            woSetGlobal, 
            sym.loc.pos, 
            newLoad( # just loading the stackptr here, TODO: move to a proc?
              conf.mapLoadKind(sym.typ.skipTypes({tyVar})), 0, 1, 
              newLoad(memLoadI32,0,1, newConst(4'i32))
            )
          )
        )
      else: 
        echo "# NOT MODIFYING A STRAIGHT VAR"

proc gen(w: WasmGen, n: PNode, conf: ConfigRef, parentKind: TNodeKind=nkNone): WasmNode =
  # TODO: go through https://nim-lang.org/docs/macros.html#statements for inspirationn
  result = newOpList() # try to fix crashes due to nil
  if n.kind in nkGenSkippedKinds: return
  echo "# working on: ", n.kind
  if not (n.kind == nkStmtList):
    echo renderTree(n)
  let b = Backend(w.graph.backend)
  echo "#GTL: ", $n.kind, " parent: ", parentKind, " module: ", conf.toFilename(n.info.fileIndex)
  case n.kind:
  of nkGenSkippedKinds: discard
  of nkCallKinds: 
    # TODO: prepare args on stack
    result = w.genCall(n, conf, parentKind)
  of nkSectionKinds:
    # sons: identdefs
    for son in n.sons:
      result = w.gen(son, conf, n.kind)
    #echo conf.treeToYaml(n)
  of nkConv, nkHiddenStdConv:
    echo "# " & $n.kind
    #echo conf.treeToYaml(n)
    var convOP: WasmOpKind
    case w.config.mapType(n[1].typ):
    of vtI32:
      case w.config.mapType(n.typ):
      of vtI32: convOP = woNop
      of vtF32: convOP = cvConvertF32S_I32
      of vtF64: convOP = cvConvertF64S_I32
      of vtI64: convOP = cvExtendI64S_I32
      else: w.config.internalError("#nkHiddenStdConv2")
    of vtF32:
      case w.config.mapType(n.typ):
      of vtI32: convOP = cvTruncI32S_F32
      of vtF32: convOP = woNop
      of vtF64: convOP = cvPromoteF64_F32
      of vtI64: convOP = cvTruncI64S_F32
      else: w.config.internalError("#nkHiddenStdConv2")
    of vtF64:
      case w.config.mapType(n.typ):
      of vtI32: convOP = cvTruncI32S_F64
      of vtF32: convOP = cvDemoteF32_F64
      of vtF64: convOP = woNop
      of vtI64: convOP = cvTruncI64S_F64
      else: w.config.internalError("#nkHiddenStdConv2")
    of vtI64:
      case w.config.mapType(n.typ):
      of vtI32: convOP = cvWrapI32_I64
      of vtF32: convOP = cvConvertF32S_I64
      of vtF64: convOP = cvConvertF64S_I64
      of vtI64: convOP = woNop
      else: w.config.internalError("#nkHiddenStdConv2")
    else: w.config.internalError("#nkHiddenStdConv2")
    if convOP == woNop:
      result = w.gen(n[1], conf) 
    else:
      result = newUnaryOp(convOP, w.gen(n[1], conf))
    # echo w.config.treeToYaml(n)
    # result = # FIXME: does this work for every symbol?
    #   newStore(
    #     w.config.mapStoreKind(n.typ),
    #     w.gen(n),
    #     0'i32, newConst(memIndex)
    #   )
  of nkIdentDefs, nkConstDef:
    # sons: 0->symbol, 1->type, 2->val
    # usually, sym.typ is more reliable than n.sons[1] for type
    # this should be handed to a store proc?
    # note that if symbol doesnt have sfUsed+sfMainModule or sfExported, we should be allowed to skip codegen
    # TODO: this will start to fail once we deal with procs, as they are the owners of the inner syms.
    #       hopefully they will still have sfUsed?
    let s = n.sons[0].sym

    if s.exportOrUsed:
      
      s.updateLoc(b.nextGlobalIdx, locGlobalVar) # TODO: consider non globals/stack/heap?
      let 
        mut = parentKind == nkVarSection
        exp = s.owner.flags.contains(sfMainModule) and s.flags.contains(sfExported)

      # if sons[2](aka val) is nkEmpty, we can skip the generation by just moving 
      # the stack pointer by size(type), otherwise we actually have to perform the store
      if n.sons[2].kind in {nkEmpty, nkNilLit} :
        # TODO: match the type and value type
        # TODO: only export some globals
        b.m.globals.add(newGlobal(b.nextGlobalIdx, conf.mapType(s.typ), newConst(0'i32),exp, mut, n[0].sym.name.s))  
        
      #  echo "#GTL elided store due to empty val ", s.name.s
      #  b.moveStackPtrBy(s.typ.size)
      elif n.sons[2].kind in nkLiterals-nkStrKinds:
        # for numericals, just store in the global
        b.m.globals.add(newGlobal(b.nextGlobalIdx, conf.mapType(s.typ), w.genLit(n.sons[2],conf, n.kind), exp, mut, n[0].sym.name.s))  
                                              # TODO: nimInitBody part is useless for literals?
                                              # it may be useful for arrays? I doubt it.
      #elif n.sons[2].kind in {nkCurly,nkBracket,nkObjConstr}:
      #  #TODO: non-literal store
      #  echo "#GTL non literal store ", n.sons[2].kind, " for ", s.name.s
      #  #FIXME: 
      #  b.m.globals.add(newGlobal(
      #    b.nextGlobalIdx, 
      #    conf.mapType(s.typ), 
      #    newConst(b.stackptr.int32), 
      #    true,
      #    mut, 
      #    n[0].sym.name.s)
      #  )
      elif n.sons[2].kind == nkSym:
        echo "#GTL RHS is nkSym for ", s.name.s
        #echo conf.symToYaml(n.sons[2].sym)
        if n.sons[2].sym.kind == skEnumField:
          # for skEnumField, sym.position is the ordinal value of the enum.
          # TODO: enum with holes?
          b.m.globals.add(
            newGlobal(
              b.nextGlobalIdx, conf.mapType(s.typ), 
              newConst(n.sons[2].sym.position.int32), 
              exp, mut, n[0].sym.name.s
            )
          )  
        else:
          echo "#GTL RHS nkSym kind :" & $n.sons[2].sym.kind
          # initialize the global and update it after
          b.m.globals.add(
            newGlobal(
              b.nextGlobalIdx, conf.mapType(s.typ), 
              #w.gen(n.sons[2], conf, n.kind),
              newNop(), 
              exp, mut, n[0].sym.name.s
            )
          )
          result = w.genAsgn(n[0], n[2], conf)
      else:
        echo "#GTL non literal RHS ", n.sons[2].kind, " for ", s.name.s
        # FIXME:
        b.m.globals.add(newGlobal(
          b.nextGlobalIdx, 
          conf.mapType(s.typ), 
          w.gen(n.sons[2], conf, n.kind), 
          exp,
          mut, 
          n[0].sym.name.s)
        )  
        #TODO: b.nimInitBody.add(w.gen(n.sons[2], conf, n.kind))
      inc b.nextGlobalIdx
      echo "#nextglobalidx ", b.nextGlobalIdx
      echo "#globals", b.m.globals.len
      #echo conf.symToYaml(n.sons[0].sym)
      #echo conf.typeToYaml(s.typ)
      #echo "#GTL: \n", conf.treeToYaml(n)
    #else:
    #  echo "#GTL skipped unused sym ", n.sons[0].sym.name.s 
    #echo conf.treeToYaml(n)
  of nkSym:
    echo "#GTL loading from sym ", n.sym.name.s
    #echo conf.symToYaml(n.sym)
    result = n.symLoc
  of nkLiterals: #TODO: other literals
    result = w.genLit(n, conf, parentKind)
  of nkStmtList:
    result = newOpList()
    for son in n.sons:
      let tmp = w.gen(son, conf, n.kind)
      if not tmp.isNil and not(tmp.kind == opList and tmp.sons.len == 0): 
        # since some nkKinds are skipped, we produce nil nodes. 
        #TODO: fix that instead of using this workaround
        result.sons.add(tmp)
  of nkAsgn:
    result = w.genAsgn(n[0], n[1], conf)
  of nkReturnStmt:
    result = newReturn(w.gen(n.sons[0],conf))
  of nkHiddenAddr:
    # to generate:
    # get global
    # store 
    # load index stored to
    # todo: some types can maybe skip this??
    if n.skipHidden.kind == nkSym:
      result = newOpList(
        newStore(
          conf.mapStoreKind(n.skipHidden.sym.typ), 
          n.skipHidden.symLoc, 
          0, 
          newLoad(memLoadI32, 0, 1, newConst(4'i32) )
        ), #load where to store from the stackptr
        newLoad(memLoadI32, 0, 1, newConst(4'i32))
      )
    else:
      result = newOpList(
        newStore(
          conf.mapStoreKind(n.skipHidden[1].sym.typ), 
          n.skipHidden.symLoc, 
          0, 
          newLoad(memLoadI32, 0, 1, newConst(4'i32) )
        ), #load where to store from the stackptr
        newLoad(memLoadI32, 0, 1, newConst(4'i32))
      )
  of nkHiddenDeref:
    result = newLoad(conf.mapLoadKind(n.skipHidden.sym.typ.skipTypes({tyVar})), 0, 1, n.skipHidden.symLoc)
  of nkBracket:
    if n.typ.flags.contains(tfVarargs):
      result = newOpList()
      echo conf.treeToYaml(n)
      # put pointers to sons in an array and return that adress
      for son in n.sons:
        result.sons.add(
          [newStore(
            memStoreI32, 
            w.gen(son, conf),
            0,
            newLoad(memLoadI32, 0, 1, newConst(4'i32))
          ),
          newStore(
            memStoreI32, 
            newAdd32( # move stackptr by 4
              newLoad(memLoadI32, 0, 1, newConst(4'i32)),
              newConst(4'i32)
            ),
            0,
            newConst(4'i32)
          )]
        )
        #result.sons.add(w.gen(son, conf))
        result.sons.add(newLoad(memLoadI32, 0, 1, newConst(4'i32)))
    else:
      #conf.internalError("Missing 0th kind for nkBracket " & $n[0].kind)
      echo "# Non varargs nkBracket: inside: ", n.typ.lastSon.kind
      #echo renderTree(n)
      #echo conf.treeToYaml(n)
      # TODO: copy part about non-numeral from objectconstr
      if n.typ.kind notin {tyArray, tySequence}:
        conf.internalError("Not an array literal or seq @[] lit ")
      result = newConst(b.stackptr)
      
      # in case this is a seq, seq are a pointer to len+reservered+data
      # so pointer is returned as result, the rest is put in data
      if n.typ.kind == tySequence:
        #echo conf.treeToYaml(n)
        # for literals, len and cap == with the number of initial elems in the brackets @[a,...]
        let sq = n.len.int32.toBytes & n.len.int32.toBytes 
        b.m.data.add(
          newData(
            b.stackptr, sq, "seq"
          )
        )
        b.moveStackPtrBy(sq.len)

      for son in n:
        if son.kind in nkLiterals:  
          let bytes = conf.wasmConstToBytes(w.gen(son, conf, n.kind), conf.getSize(n.typ.lastSon))
          b.m.data.add(
            newData(
              b.stackptr, 
              bytes, "val"
            )
          )
          b.moveStackPtrBy(bytes.len)
        else:
          # it's some pointer indirection, store it and move by 4bytes
          # TODO:should make copies of non shallow types
          result = newStore(
              memStoreI32, w.gen(son, conf, n.kind), 0, newConst(b.stackptr)
          )
          b.moveStackPtrBy(4) #size of a pointer TODO: read it from conf?
  of nkExprColonExpr:
    result = w.gen(n[1], conf, n.kind)
  of nkObjConstr:
      echo "# An object constructor"
      #echo renderTree(n)
      #echo conf.treeToYaml(n)
      if n.typ.kind != tyObject:
        conf.internalError("Not an object construction")
      result = newConst(b.stackptr)
      for i, son in n:
        if i==0: continue # skip the typedef
        if son[1].isNil or son[1].kind == nkEmpty: 
          conf.internalError("FIXME: empty object field")
        if son[1].kind in nkLiterals:
          let bytes = conf.wasmConstToBytes(w.gen(son, conf, n.kind), son[1].typ.size)
          b.m.data.add(
            newData(
              b.stackptr, 
              bytes, n[0].sym.name.s & "." & son[0].sym.name.s
            )
          )
          b.moveStackPtrBy(bytes.len)
        else:
          # it's some pointer indirection, store it and move by 4bytes
          # TODO:should make copies of non shallow types
          result = newStore(
              memStoreI32, w.gen(son, conf, n.kind), 0, newConst(b.stackptr)
          )
          
          b.moveStackPtrBy(4) #size of a pointer TODO: read it from conf?
  of nkTupleConstr:
      echo "# A tuple constructor"
      #echo renderTree(n)
      echo conf.treeToYaml(n)
      if n.typ.kind != tyTuple:
        conf.internalError("Not a tuple construction")
      result = newConst(b.stackptr)
      for i, son in n:
        if son.kind in nkLiterals:
          let bytes = conf.wasmConstToBytes(w.gen(son, conf, n.kind), son.typ.size)
          b.m.data.add(
            newData(
              b.stackptr, 
              bytes, n.typ.sym.name.s & "." & n.typ.n[i].sym.name.s
            )
          )
          b.moveStackPtrBy(bytes.len)
        else:
          # it's some pointer indirection, store it and move by 4bytes
          # TODO:should make copies of non shallow types
          result = newStore(
              memStoreI32, w.gen(son, conf, n.kind), 0, newConst(b.stackptr)
          )
          
          b.moveStackPtrBy(4) #size of a pointer TODO: read it from conf?
  of nkDotExpr:
    #echo conf.treeToYaml(n[1])
    result = newLoad(
      conf.mapLoadKind(n[1].sym.typ), 0, 1,
      newAdd32(
        w.gen(n[0], conf, n.kind), # base object loc
        newConst(n[1].sym.offset) # field offset
      )
    )
  of nkBracketExpr:
    echo conf.treeToYaml(n)
    var baseoffset = 0'i32
    if n[0].typ.kind in {tySequence, tyString}:
      baseoffset = 2*4 # len, cap * sizeof(pointer)
    result = newLoad(
      conf.mapLoadKind(n[0].sym.typ.lastSon), 0, 1,
      # symloc + basepos + pos*sizetype
      newAdd32(
        w.gen(n[0], conf, n.kind), # base array/strin/seq loc
        newAdd32(
          newMul32(
            w.gen(n[1], conf, n.kind),
            newConst(n[0].typ.lastSon.size.toInt128.toInt32)
          ), # element offset
          newConst(baseoffset)
        )
        
      )
    )
  else:
    echo "# Missing kind ", n.kind
    echo renderTree(n)
    echo conf.treeToYaml(n)
    conf.internalError("#GTL is missing kind: " & $n.kind)

proc genNimInit(b: Backend) =
  # Generate the init expression
  if b.nimInitBody.len<1: 
    echo "# Empty nimInitBody"
  # FALSE: return # no expression, no need for a init proc
  b.m.functions.add(
    newFunction(
      b.nextFuncIdx, newType(vtNone),  newOpList(b.nimInitBody), @[], "nimInit", true
    )
  )
  echo "#generated initfunc at index init: ", b.nextFuncIdx
  inc b.nextFuncIdx

proc wasmMoveStackPtr(by:int32): WasmNode =
  newStore( memStoreI32, newAdd32(newLoad(memLoadI32,0,1,newConst(4'i32)), newConst(by)),
    0, newConst(4'i32)    
  )

proc putHeapPtr(b:Backend) =
  # store location of next free adress in memory (after all the static data that was stored during compile time)
  # problem: where is the heap??
  echo "#PHP add heap ptr"
  b.m.data.add(
    newData( # store at ptr=4 the stack bottom ptr
      4'i32, b.stackptr.toBytes, "stackptr"
    )
  )

#------------------myPass------------------------------#
proc myProcess(b: PPassContext, n: PNode): PNode =
  # nodes that I saw passing through here:
  # nkVarSection, nkStmtList, nkProcDef, nkEmpty
  var w = WasmGen(b)  
  result = n
  if passes.skipCodegen(w.config, n): return
  var backend = Backend(w.graph.backend)
  if backend.m.name notin toFilename(w.config, n.info): return # FIXME: this skippes everything not coming from test.nim
  var transfN = transformStmt(w.graph,w.s,n)
  if transfN.kind in nkGenSkippedKinds: return

  echo "#WASM#>P ", $n.kind, " from ", w.config.toFilename(n.info.fileIndex)  

  for son in transfN:
    # we dont call gen on transfN directly to avoid the whole module being processed at once, which fould screw up
    # with order of execution of load/stores when they are inserted by us, eg in callMagic
    let tmp = w.gen(son, w.config)
    
    # reduces useless empty opLists
    if not tmp.isNil and not(tmp.kind == opList and tmp.sons.len == 0): 
      backend.nimInitBody.add(tmp)
      #echo son.kind
      #echo tmp.render
  #if w.s.flags.contains(sfMainModule):
  #  echo w.config.treeToYaml(n)
  #  let generated = w.gen(n)
  #  if not generated.isNil: w.nimInitBody.add(generated)
  
  echo "#WASM#<P ", $n.kind


proc myClose(graph: ModuleGraph; b: PPassContext, n: PNode): PNode =
  if passes.skipCodegen(graph.config, n): return n
  echo "#WASM#C ", $n.kind, " from ", graph.config.toFilename(n.info.fileIndex)
  result = myProcess(b, n)
  var w = WasmGen(b)
  if w.s.flags.contains(sfMainModule):
    # finalize the module
    var backend = Backend(graph.backend)
    backend.genNimInit()
    backend.putHeapPtr()
    #echo "#BackendNAME: ", Backend(graph.backend).m.name
    let outfile = w.config.prepareToWriteOutput

    if optRun in w.config.globalOptions or w.config.isDefined("testing"):
      # -d:testing is set by testament when running tests

      # generate a js file suitable to be run by node
      writeFile($outfile.changeFileExt("js"), w.config.getConfigVar("glue.loaderNode") % [w.s.name.s, w.config.getConfigVar("glue.jsHelpers") % [w.s.name.s]])
      # TODO: removeme
      writeFile($outfile.changeFileExt("html"), w.config.getConfigVar("glue.loader") % [w.s.name.s, w.config.getConfigVar("glue.jsHelpers") % [w.s.name.s]])
    else:
      writeFile($outfile.changeFileExt("html"), w.config.getConfigVar("glue.loader") % [w.s.name.s, w.config.getConfigVar("glue.jsHelpers") % [w.s.name.s]])
    if w.config.isDefined("debug"):
      writeFile($outfile.changeFileExt("json"), render(backend.m))

    # encode is the last step since the json is more forgiving
    writeFile($outfile, encode(backend.m))
    
  echo "#WASM#C ", $n.kind
  
    
proc myOpen(graph: ModuleGraph; s: PSym): PPassContext =
  echo "#WASM#>O ",graph.config.toFilename(s.info.fileIndex)," s.name: ",$s.name.s
  
  var w = newWasmGen(s, graph)
  w.s = s
  w.graph.backend = backend
  if s.flags.contains(sfMainModule):
    backend.updateBackendName(s.name.s)
  result = w
  echo "#WASM#<O ",graph.config.toFilename(s.info.fileIndex)," s.name: ",$s.name.s

const WasmGenPass* = makePass(myOpen, myProcess, myClose)
