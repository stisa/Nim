import
  ast, astalgo, options, msgs, idents, types, passes,
  ropes, wordrecg, modulepaths, transf, hashes, magicsys,
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
    nimInit: WAsmFunction # a sequence of operations that make up the top-level of the program
    nextImportIdx: Natural # function index space ( doesn't account for hoisting of imported procs )
    nextFuncIdx: Natural # the function index space (only for non-imported funcs)
    nextGlobalIdx: Natural # the global index space
    nextMemIdx: Natural # the linear memory index space
    nextTableIdx: Natural # the table index space
    m : WAsmModule #current wasm module
    generatedProcs: Table[PSym,tuple[id:int,imported:bool]] # name, funcIdx
    generatedTypeInfos: Table[PSym, int32] # name, location in memory TODO:
    locs: tuple[stack,heap:int32] # stack is Used as compile time stack ptr


const
  irrelevantForBackend = {tyGenericBody, tyGenericInst, tyGenericInvocation,
                          tyDistinct, tyRange, tyStatic, tyAlias, tySink,
                          tyInferred, tyOwned}

#proc typeName(typ: PType): Rope =
#  let typ = typ.skipTypes(irrelevantForBackend)

proc newBackend(modulename:string): Backend =
  result = Backend(
    generatedProcs: initTable[PSym,tuple[id:int,imported:bool]](),
    generatedTypeInfos: initTable[PSym,int32](),
    )
  
  result.nextFuncIdx = 0
  result.nextImportIdx = 0
  result.nextGlobalIdx = 0
  result.nextTableIdx = 0
  # 4 byte aligned, reserve 8 bytes to store the stack pointer
  # This mean effective address start at 12?
  result.nextMemIdx = 0
  result.nimInit = newFunction(
      result.nextFuncIdx, newType(rs=vtNone), newOpList(), @[], "nimInit", true
  )
  inc result.nextFuncIdx
  # this will be updated since the first module name is not the main one
  result.m = newModule(modulename) 
  #initialize the module's sections
  result.m.memory = newMemory()
  add result.m.exports, newExport(0, ekMemory, "$memory")

  result.m.functions.add(result.nimInit)

  result.locs = (12'i32, 0'i32)

proc updateBackendName(b: Backend, name:string) = b.m.name = name

proc moveStackPtrBy(b:Backend, bytes:BiggestInt) =
  b.locs.stack += bytes.int32

proc stackptr(b:Backend): int = b.locs.stack

proc updateLoc(s: PSym, loc: int, kind: TLocKind, skind: TStorageLoc) =
  s.loc.k = kind
  s.loc.storage = skind
  s.loc.pos = loc
  s.loc.r = loc.rope # for debug purposes

proc getLoc(s: PSym): int =
  result = s.loc.pos  
  if s.loc.k != locGlobalVar:
    echo "#getloc: CHECK: other than global" & s.name.s & " " & $s.loc.k & " " & $s.loc.storage

proc hash(s:PSym): Hash = hash(s.mangleName)

proc backendAddr(w: WasmGen, s: PSym): int = 
  # TODO: study var params
  if s.kind == skParam:
      result = s.position
  else:
      result = s.loc.pos
  if not(s.kind == skParam) and (s.loc.k == locNone or s.loc.storage == OnUnknown):
    echo w.config.symToYaml(s)
    w.config.internalError "#bAddr" & $s.name.s & " " & $s.loc.k & " " & $s.loc.storage

proc backendDerefNode(w: WasmGen, s: PSym): WasmNode =
  # TODO: study var params
  if s.kind == skParam:
      result = newGet(woGetLocal, s.position)
  elif s.loc.k == locLocalVar:
      result = newGet(woGetLocal, s.loc.pos)
  elif s.loc.storage == OnStatic:
    result = newGet(woGetGlobal, s.loc.pos)
  elif s.loc.storage == OnHeap:
    result = newLoad(w.config.mapLoadKind(s.typ), 0, 1, newConst(s.loc.pos))
  else:
    echo w.config.symToYaml(s)
    w.config.internalError "#bDeref" & $s.name.s & " " & $s.loc.k & " " & $s.loc.storage

proc symLoc(conf: ConfigRef, n: PNode): WasmNode =
  # TODO: splitme backendDeref , backendAddr
  # TODO: study var params
  if n.kind == nkSym:
    if n.sym.kind == skParam:
        result = newGet(woGetLocal, n.sym.position)
    elif n.sym.loc.k == locLocalVar:
        result = newGet(woGetLocal, n.sym.loc.pos)
    elif n.sym.loc.storage == OnStatic:
      result = newGet(woGetGlobal, n.sym.loc.pos)
    elif n.sym.loc.storage == OnHeap:
      result = newLoad(conf.mapLoadKind(n.sym.typ), 0, 1, newConst(n.sym.loc.pos))
    else:
      echo conf.symToYaml(n.sym)
      conf.internalError "#symloc: TODO: other than global" & $n.sym.loc.k & " " & $n.sym.loc.storage
  else:
    conf.internalError "#NOT A SYM for Symloc" & $n.kind

proc hasProc(b: Backend, sym: PSym): bool =
  sym in b.generatedProcs

proc hasTypeInfo(b: Backend, sym: PSym): bool =
  sym in b.generatedTypeInfos

const nkGenSkippedKinds = { nkCommentStmt, nkPragma, nkEmpty, 
                            nkTemplateDef, nkFuncDef, nkProcDef, nkMethodDef, 
                            nkIteratorDef, nkMacroDef, nkIncludeStmt, 
                            nkImportStmt, nkExportStmt, nkExportExceptStmt, 
                            nkImportExceptStmt, nkImportAs, nkConverterDef,
                            nkIncludeStmt, nkTypeSection}#, nkWhenStmt, nkWhenExpr }

const nkSectionKinds = {nkVarSection, nkConstSection, nkLetSection}

proc gen(w: WasmGen, n: PNode, wasmproc: var WAsmFunction, parentKind: TNodeKind=nkNone): WasmNode

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

proc genMagicCall(w: WasmGen, n:PNode, magic:TMagic, wasmProc: var WAsmFunction, parentKind: TNodeKind=nkNone): WasmNode =
  echo "#MAGIC: ", magic
  let b = w.graph.backend.Backend
  case magic:
  #[# the new idea for string conversion of numbers:
    # call a js side intToStr that takes a number and writes out the string to memory with TextEncoder
    # return the ptr to wasm, then wasm can just use that ptr.
    # in future, this would be similar to how c does it, just need to override c_sprintf
    # that is used in formatfloat with a js one
    of mIntToStr, nimFloatToStr:
      if not b.hasProc(n[0].sym):
        w.genImportedProc(n[0].sym) # params type and return type can be gotten from the ast of the procdef, maybe name too to make it super generic? And glue is hardcoded anyway
      let idx, imported = b.generatedProcs[n[0].sym]
      result = newCall(idx, w.gen(n[1], conf, imported))
    # old vvv
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
        let bytes = w.config.wasmConstToBytes(w.gen(son, wasmProc, n.kind), w.config.getSize(n[1].typ.lastSon))
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
        wasmProc.body.sons.add(
          newStore(
            w.config.mapStoreKind(son.typ), w.gen(son, wasmProc, n.kind), 0, newConst(b.stackptr)
          )
        )
        b.moveStackPtrBy(son.typ.size) #size of a pointer TODO: read it from conf?
  of UnaryMagic:
    result = newUnaryOp(w.config.getMagicOp(magic), w.gen(n[1], wasmProc))
  of BinaryMagic:
    result = newBinaryOp(w.config.getMagicOp(magic), w.gen(n[1], wasmProc), w.gen(n[2], wasmProc))
  of FloatsMagic:
    if n.typ.kind == tyFloat32: #CHECK: why did I have this comment?
      # or (n.typ.kind == tyBool and n[1].typ.kind == tyFloat32): 
      # the bool part is because otherwise 1'f32+2.0 would use f32 arithm
      result = newBinaryOp(w.config.getFloat32Magic(magic), w.gen(n[1], wasmProc), w.gen(n[2], wasmProc))
    else:
      result = newBinaryOp(w.config.getMagicOp(magic), w.gen(n[1], wasmProc), w.gen(n[2], wasmProc))
  of mInc:
    echo w.config.treeToYaml(n)
    let s = if n[1].kind == nkSym: n[1].sym else: n[1][0].sym
    result =  newStore(
      w.config.mapStoreKind(s.typ),
      newBinaryOp(ibAdd32, w.gen(n[1], wasmProc), w.gen(n[2], wasmProc)),
      0,
      newConst(s.getLoc), # TODO: proper fix
    )
  of mDec:
    let s = if n[1].kind == nkSym: n[1].sym else: n[1][0].sym
    result =  newStore(
      w.config.mapStoreKind(s.typ),
      newBinaryOp(ibSub32, w.gen(n[1], wasmProc), w.gen(n[2], wasmProc)),
      0,
      newConst(s.getLoc), # TODO: proper fix
    )
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
proc genProc(w: WasmGen, prc: PSym, conf: ConfigRef) =
  echo "#GNP: ", $prc.kind, " module: ", prc.owner.name.s #conf.toFilename(n.info.fileIndex)
  #echo conf.treeToYaml(n)
  #echo conf.symToYaml(n.sym)
  let procDef = prc.ast
  #echo conf.typeToYaml(n.sym.typ)
  assert(procDef.kind == nkProcDef)
  let b = Backend(w.graph.backend)
  # Build the type signature of this proc in wasm land
  # note that for type sign purposes, the prc.sym.typ.sons are better than using formalparams of ast
  let procparams = prc.typ.sons # the list of types for params
  var proctype : WasmType #= newType(rs=res) # The complete type of the proc in wasm land
    
    # body = s.getBody() TODO:
  for i, par in procparams:
    if i == 0:
      proctype = newType(rs=conf.mapType(par)) # instantiate the proc type with the result type
      continue # move to next par
    proctype.params.add(conf.mapType(par))

  if prc.flags.contains(sfImportc):
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
        b.nextImportIdx, ekFunction, headername, importcname, prc.name.s, proctype, prc.flags.contains(sfExported)
      )
    )
    # the id of the proc is the import id, because we can then hoist it in a later phase
    # by simply having non-imports start from last(importId), eg id = nextImportIdx+nextFuncIdx
    b.generatedProcs[prc] = (b.nextImportIdx, true)
    inc b.nextImportIdx
  else:
    echo "#GNP: generating nim proc: ", prc.name.s," module: ", prc.owner.name.s #conf.toFilename(n.info.fileIndex)
    #echo conf.treeToYaml(procDef)
    #echo renderTree(procDef)
    var wasmproc =  newFunction(
        0, proctype,
        newOpList(), @[], prc.name.s, 
        prc.flags.contains(sfExported)
      )
    
    # update the loc of result symbol if present
    # would'nt be needed if result was injected, see notes on compiler
    # improvement
    if proctype.res != vtNone:
      procDef[resultPos].sym.updateLoc(wasmproc.typ.params.len+wasmproc.locals.len, locLocalVar, OnHeap)
      wasmproc.locals.add(wasmproc.typ.res)
  
    var transfBody = transformBody(w.graph, prc, cache=false)
    echo "#working on transfbody:", conf.treeToYaml(transfBody)
    echo renderTree(transfBody)
    
    if transfBody.kind == nkStmtList:
      for son in transfBody:
        # we dont call gen on transfBody directly to avoid the whole proc being processed at once, which would screw
        # with order of execution of load/stores when they are inserted by us, eg in callMagic
        let tmp = w.gen(son, wasmproc, transfBody.kind)
        # reduces useless empty opLists
        if not tmp.isNil and not(tmp.kind == opList and tmp.sons.len == 0): 
          wasmproc.body.sons.add(tmp)
    else:
      let tmp = w.gen(transfBody, wasmproc, transfBody.kind)
      # reduces useless empty opLists
      if not tmp.isNil and not(tmp.kind == opList and tmp.sons.len == 0): 
        wasmproc.body.sons.add(tmp)
    
    # inject a return stmt
    # would'nt be needed if result was injected, see notes on compiler
    # improvement
    if proctype.res != vtNone:
      wasmproc.body.sons.add(
        newReturn(w.gen(procDef[resultPos], wasmproc, transfBody.kind))
      )
    
    wasmproc.idx = b.nextFuncIdx
    b.m.functions.add(wasmproc)
    inc b.nextFuncIdx
    echo "#CHECK: id: ", wasmproc.id, "next: ", b.nextFuncIdx
    b.generatedProcs[prc] = (wasmproc.id, false)
    

proc genLit(w: WasmGen, n: PNode, parentKind: TNodeKind): WasmNode =
  # General idea: if it's a numeral(int, float, bool...) use const and pass
  # it directly, otherwise store it in data and pass a pointer to the beginning
  echo "#GNL literal of kind ", n.kind
  let b = Backend(w.graph.backend)  
  let conf = w.config
  var typ = n.typ
  echo "#LOAD type ", typ.kind
  case n.kind:
  of nkNilLit:
    result = newConst(0'u32)
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

proc genAsgn(w: WasmGen, lhs, rhs: PNode, wasmproc: var WAsmFunction): WasmNode =
  #TODO:,
  #
  #echo conf.treeToYaml(rhs)
  let conf = w.config
  var ns = lhs.skipHidden()
  #echo conf.treeToYaml(lhs)
  if ns.kind != nkSym: 
    conf.internalError("# asgn not to a sym but " & $ns.kind)
  let loc = ns.sym.loc
  if ns.sym.kind == skParam:
    if not (ns.sym.typ.kind == tyVar):
      w.config.internalError("# Assigning to a non-var param?")
    result = newStore(conf.mapStoreKind(ns.sym.typ.skipTypes({tyVar})),w.gen(rhs, wasmproc, nkAsgn), 0, w.backendDerefNode(ns.sym))
  elif loc.k == locLocalVar:
    result = newSet(
      woSetLocal, w.backendAddr(ns.sym),
      w.gen(rhs, wasmproc, nkAsgn)
    )
  elif loc.k == locGlobalVar:
    if loc.storage == OnHeap:
      result = newStore(conf.mapStoreKind(ns.sym.typ), w.gen(rhs, wasmproc, nkAsgn), 0, newConst(w.backendAddr(ns.sym)))
    elif loc.storage == OnStatic:
      # This should only trigger when updating a let with the runtime value
      result = newSet(woSetGlobal, w.backendAddr(ns.sym), w.gen(rhs, wasmproc, nkAsgn))
    else:
      echo w.config.treeToYaml(ns)
      w.config.internalError("#genAsgn: unrecognized storage " & $loc.storage)
  else:
    echo w.config.treeToYaml(ns)
    w.config.internalError("#genAsgn: unrecognized kind " & $loc.k)

  #[if ns.sym.owner.kind == skModule: # globals
    if ns.sym.typ.kind == tyVar:
      # need to treat it as a pointer
      result = newStore(conf.mapStoreKind(ns.sym.typ.skipTypes({tyVar})),w.gen(rhs, wasmproc, nkAsgn), 0, w.backendDerefNode(ns.sym))
    else:
      result = newStore(conf.mapStoreKind(ns.sym.typ), w.gen(rhs, wasmproc, nkAsgn), 0, newConst(w.backendAddr(ns.sym)))
  elif ns.sym.owner.kind == skProc: # locals
    if ns.sym.typ.kind == tyVar:
      # need to treat it as a pointer
      result = newStore(conf.mapStoreKind(ns.sym.typ.skipTypes({tyVar})),w.gen(rhs, wasmproc, nkAsgn), 0, w.backendDerefNode(ns.sym))
    elif ns.sym.loc.k == locLocalVar:
      result = newSet(woSetLocal, w.backendAddr(ns.sym), w.gen(rhs, wasmproc, nkAsgn))
    else:
      result = newStore(conf.mapStoreKind(ns.sym.typ), w.gen(rhs, wasmproc, nkAsgn), 0, newConst(w.backendAddr(ns.sym)))
      #result = newSet(woSetLocal, ns.sym.getLoc, w.gen(rhs, conf, nkAsgn))
  else:
    conf.internalError("# asgn: owner.kind not proc or module " & $ns.sym.owner.kind)]#


proc genCall(w: WasmGen, n: PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
  # 0-> proc sym, 1..->arg(s)
  echo "#GCL call kind ", n.kind
  let b = Backend(w.graph.backend)
  let conf = w.config

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
    w.genProc(n.sons[0].sym, conf)
  
  let (id, isImport) = b.generatedProcs[n.sons[0].sym]
  
  var args : seq[WasmNode] = @[]
  #if n.sons[0].sym.ast[resultPos].kind != nkEmpty:
  #  args.add(newConst(0'i32)) # the return
  var toUpdate: seq[PNode] = @[]
  result = newOpList()
  # we may need to generate a set global after execution to update var types params 
  if n.sons.len > 1: # at least 1 argument
    for i, arg in n.sons:
      if i == 0: continue # skip first arg (should be nkSym of the proc)
      echo "#ARGtyp: ", arg.typ.kind
      #echo conf.typeToYaml(arg.typ)
      if arg.typ.kind == tyVar and not arg.typ[0].kind.isPtrLike : toUpdate.add(arg.skipHidden)
      args.add(w.gen(arg, wasmproc, n.kind))
  result=newCall(id, args, isImport)
  #[
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
  ]#

proc genConv(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
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
    else: w.config.internalError("#nkHiddenStdConv1")
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
    else: w.config.internalError("#nkHiddenStdConv3")
  of vtI64:
    case w.config.mapType(n.typ):
    of vtI32: convOP = cvWrapI32_I64
    of vtF32: convOP = cvConvertF32S_I64
    of vtF64: convOP = cvConvertF64S_I64
    of vtI64: convOP = woNop
    else: w.config.internalError("#nkHiddenStdConv4")
  else: w.config.internalError("#nkHiddenStdConv5")
  if convOP == woNop:
    result = w.gen(n[1], wasmproc) 
  else:
    result = newUnaryOp(convOP, w.gen(n[1], wasmproc))

proc genLocal(w: WasmGen, n:PNode, wasmproc: var WAsmFunction): WasmNode =
  let s = n.sons[0].sym
  
  if n.sons[2].kind in {nkEmpty, nkNilLit} :
    result = newSet(woSetLocal, w.backendAddr(s), newConst(0'i32))
  elif n.sons[2].kind in nkLiterals-nkStrKinds:
    # for numericals, just store in the local
    result = newSet(woSetLocal, w.backendAddr(s),  w.genLit(n.sons[2], n.kind))
  elif n.sons[2].kind == nkSym:
    echo "#GL RHS is nkSym for ", s.name.s
    #echo conf.symToYaml(n.sons[2].sym)
    if n.sons[2].sym.kind == skEnumField:
      # for skEnumField, sym.position is the ordinal value of the enum.
      # TODO: enum with holes?
      result = newSet(woSetLocal, w.backendAddr(s), newConst(n.sons[2].sym.position.int32))
    else:
      echo "#GL RHS nkSym kind :" & $n.sons[2].sym.kind
      result = newSet(woSetLocal, w.backendAddr(s), w.gen(n[2], wasmproc, nkAsgn))
  else:
    echo "#GL non literal RHS ", n.sons[2].kind, " for ", s.name.s
    result = newSet(woSetLocal, w.backendAddr(s), w.gen(n[2], wasmproc, nkAsgn))
  
proc genGlobal(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, mut, exp: bool): WasmNode =
  let conf = w.config
  let b = w.graph.backend.Backend

  let s = n.sons[0].sym
  
  if n.sons[2].kind in {nkEmpty, nkNilLit} :
    b.m.globals.add(newGlobal(w.backendAddr(s), conf.mapType(s.typ), newConst(0'i32),exp, mut, n[0].sym.name.s))  
  elif n.sons[2].kind in nkLiterals-nkStrKinds:
    # for numericals, just store in the global
    b.m.globals.add(newGlobal(w.backendAddr(s), conf.mapType(s.typ), w.genLit(n.sons[2], n.kind), exp, mut, n[0].sym.name.s))  
  elif n.sons[2].kind == nkSym:
    echo "#GTL RHS is nkSym for ", s.name.s
    #echo conf.symToYaml(n.sons[2].sym)
    if n.sons[2].sym.kind == skEnumField:
      # for skEnumField, sym.position is the ordinal value of the enum.
      # TODO: enum with holes?
      b.m.globals.add(
        newGlobal(
          w.backendAddr(s), conf.mapType(s.typ), 
          newConst(n.sons[2].sym.position.int32), 
          exp, mut, n[0].sym.name.s
        )
      )  
    else:
      echo "#GTL RHS nkSym kind :" & $n.sons[2].sym.kind
      # initialize the global and update it after
      b.m.globals.add(
        newGlobal(
          w.backendAddr(s), conf.mapType(s.typ), 
          newNop(), 
          #w.gen(n[2], conf, n.kind),
          exp, mut, n[0].sym.name.s
        )
      )
      result = newSet(woSetGlobal, w.backendAddr(s), w.gen(n[2], wasmproc, nkAsgn))
      
  else:
    echo "#GTL non literal RHS ", n.sons[2].kind, " for ", s.name.s
    b.m.globals.add(
      newGlobal(
        w.backendAddr(s), conf.mapType(s.typ), 
        w.gen(n[2], wasmproc, n.kind),
        exp, mut, n[0].sym.name.s
      )
    )
    #result = newSet(woSetGlobal, n[0].sym.getLoc, w.gen(n[2], wasmproc, nkAsgn))
  inc b.nextGlobalIdx
  #echo "#nextglobalidx ", b.nextGlobalIdx
  #echo "#globals", b.m.globals.len

proc genVar(w: WasmGen, n: PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
  # sons: 0->symbol, 1->type, 2->val
  # usually, sym.typ is more reliable than n.sons[1] for type
  # this should be handed to a store proc?
  # note that if symbol doesnt have sfUsed+sfMainModule or sfExported, we should be allowed to skip codegen
  # TODO: this will start to fail once we deal with procs, as they are the owners of the inner syms.
  #       hopefully they will still have sfUsed?
  let s = n.sons[0].sym
  let b = Backend(w.graph.backend)
  let conf = w.config

  if s.exportOrUsed:
    
    let 
      mut = parentKind == nkVarSection
      exp = s.owner.flags.contains(sfMainModule) and s.flags.contains(sfExported)
    if not mut: conf.internalError("let/const went through the wrong codegen path")
    let lockind = if s.owner.kind == skModule: locGlobalVar else: locLocalVar
    
    if lockind == locGlobalVar:
      s.updateLoc(b.stackptr, lockind, OnHeap) # OnHeap => on the linear memory
    else:
      s.updateLoc(wasmproc.typ.params.len+wasmproc.locals.len, lockind, OnStatic)
      wasmproc.locals.add(conf.mapType(s.typ))
    
    # TODO: differntiate between OnHeap(refs)/OnStack(rest)
    
    # if sons[2](aka val) is nkEmpty, we can skip the generation by just moving 
    # the stack pointer by size(type), otherwise we actually have to perform the store
    if n.sons[2].kind in {nkEmpty, nkNilLit} :
      echo "#GTL elided store due to empty val ", s.name.s
      if not (s.loc.k == locGlobalVar):
        result = newSet(woSetLocal, w.backendAddr(s), newConst(0'u32))  
    elif n.sons[2].kind in nkLiterals-nkStrKinds:
      # for numericals, just store in the global
      if lockind == locGlobalVar:
        result = newStore(conf.mapStoreKind(s.typ), w.genLit(n.sons[2], n.kind), 0, newConst(b.stackptr))  
      else:
        result = newSet(woSetLocal, w.backendAddr(s), w.genLit(n.sons[2], n.kind))  
    elif n.sons[2].kind == nkSym:
      echo "#GTL RHS is nkSym for ", s.name.s
      #echo conf.symToYaml(n.sons[2].sym)
      if n.sons[2].sym.kind == skEnumField:
        # for skEnumField, sym.position is the ordinal value of the enum.
        # TODO: enum with holes?
        if lockind == locGlobalVar:
          result = newStore(conf.mapStoreKind(s.typ), newConst(n.sons[2].sym.position.int32), 0, newConst(b.stackptr))  
        else:
          result = newSet(woSetLocal, w.backendAddr(s), newConst(n.sons[2].sym.position.int32))
      else:
        echo "#GTL RHS nkSym kind :" & $n.sons[2].sym.kind
        # move stackptr size typ, update it after
        result = w.genAsgn(n[0], n[2], wasmproc)
    else:
      echo "#GTL non literal RHS ", n.sons[2].kind, " for ", s.name.s
      # move stackptr size typ, update it after
      result = w.genAsgn(n[0], n[2], wasmproc)
    b.moveStackPtrBy(s.typ.size)


proc genIdentDef(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
  # sons: 0->symbol, 1->type, 2->val
  # usually, sym.typ is more reliable than n.sons[1] for type
  # this should be handed to a store proc?
  # note that if symbol doesnt have sfUsed+sfMainModule or sfExported, we should be allowed to skip codegen
  # TODO: this will start to fail once we deal with procs, as they are the owners of the inner syms.
  #       hopefully they will still have sfUsed?
  
  let conf = w.config
  let b = w.graph.backend.Backend

  let s = n.sons[0].sym

  if s.exportOrUsed:
    # TODO: if s.owner.kind == skProc: use locals (locals don't need to be created)   
    let 
      mut = parentKind == nkLetSection # let section may need to be updated at runtime
      exp = s.owner.flags.contains(sfMainModule) and s.flags.contains(sfExported)
    if parentKind == nkVarSection: conf.internalError("var identdef went through the wrong codegen path")
    let lockind = if s.owner.kind == skModule: locGlobalVar else: locLocalVar
    
    if lockind == locGlobalVar:
        s.updateLoc(b.nextGlobalIdx, lockind, OnStatic) # OnStatic means let/const are in a wasm global/local
        result = w.genGlobal(n, wasmproc, mut, exp)
    else:
      s.updateLoc(wasmproc.typ.params.len+wasmproc.locals.len, lockind, OnStatic)
      wasmproc.locals.add(conf.mapType(s.typ))
      result = w.genLocal(n, wasmproc)

proc genCurly(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
  let conf = w.config
  let b = w.graph.backend.Backend
  #echo conf.treeToYaml(n)
  #echo conf.typeToYaml(n[0].typ)
  #conf.internalError("nkCurly not implemented")
  result = newConst(b.stackptr)
  for son in n:
    if son.kind in nkLiterals:  
      let bytes = conf.wasmConstToBytes(w.gen(son, wasmproc, n.kind), conf.getSize(n.typ.lastSon))
      b.m.data.add(
        newData(
          b.stackptr, 
          bytes, "curlyelemnt"
        )
      )
      b.moveStackPtrBy(bytes.len)
    else:
      # it's some pointer indirection, store it and move by 4bytes
      # TODO:should make copies of non shallow types
      wasmproc.body.sons.add(newStore(
          memStoreI32, w.gen(son, wasmproc, n.kind), 0, newConst(b.stackptr)
      ))
      b.moveStackPtrBy(4) #size of a pointer TODO: read it from conf?

proc genBracket(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
  let conf = w.config
  let b = w.graph.backend.Backend
  if n.typ.flags.contains(tfVarargs): # FIXME: does this even work?
    result = newOpList()
    #echo conf.treeToYaml(n)
    # put pointers to sons in an array and return that adress
    for son in n.sons:
      result.sons.add(
        [newStore(
          memStoreI32, 
          w.gen(son, wasmproc),
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
        let bytes = conf.wasmConstToBytes(w.gen(son, wasmproc, n.kind), conf.getSize(n.typ.lastSon))
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
        # TODO: in result or in nimInitBody?
        result.sons.add newStore(
            memStoreI32, w.gen(son, wasmproc, n.kind), 0, newConst(b.stackptr)
        )
        b.moveStackPtrBy(4) #size of a pointer TODO: read it from conf?

proc genObjConstr(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
  #echo "# An object constructor"
  #echo renderTree(n)
  #echo conf.treeToYaml(n)
  let conf = w.config
  let b = w.graph.backend.Backend
  if n.typ.kind notin {tyObject, tyRef}:
    conf.internalError("Not an object construction " & $n.typ.kind)
  if n.typ.kind == tyRef: 
    echo "#WARN: support for ref object is very limited"
  var debugname = ""
  
  if n[0].kind == nkSym:
      debugname = n[0].sym.name.s
  elif n[0].kind == nkPar and n[0][0].kind == nkRefTy:
      # FIXME: OMG ugly
      debugname = n[0][0][0].sym.name.s

  result = newConst(b.stackptr)
  for i, son in n:
    if i==0: continue # skip the typedef
    if son[1].isNil or son[1].kind == nkEmpty: 
      conf.internalError("FIXME: empty object field")
    if son[1].kind in nkLiterals+{nkNilLit}:
      let bytes = conf.wasmConstToBytes(w.gen(son, wasmproc, n.kind), son[1].typ.size)
      b.m.data.add(
        newData(
          b.stackptr, 
          bytes, debugname & "." & son[0].sym.name.s
        )
      )
      b.moveStackPtrBy(bytes.len)
    else:
      # it's some pointer indirection, store it and move by 4bytes
      # TODO:should make copies of non shallow types
      wasmproc.body.sons.add(newStore(
          memStoreI32, w.gen(son, wasmproc, n.kind), 0, newConst(b.stackptr)
      ))
      
      b.moveStackPtrBy(4) #size of a pointer TODO: read it from conf?

proc genTupleConstr(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
  #echo "# A tuple constructor"
  #echo renderTree(n)
  #echo conf.treeToYaml(n)
  let conf = w.config
  let b = w.graph.backend.Backend

  if n.typ.kind != tyTuple:
    conf.internalError("Not a tuple construction")
  result = newConst(b.stackptr)
  for i, son in n:
    if son.kind in nkLiterals:
      let bytes = conf.wasmConstToBytes(w.gen(son, wasmproc, n.kind), son.typ.size)
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
      wasmproc.body.sons.add(newStore(
          memStoreI32, w.gen(son, wasmproc, n.kind), 0, newConst(b.stackptr)
      ))
      
      b.moveStackPtrBy(4) #size of a pointer TODO: read it from conf?

proc genDotExpr(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
  let conf = w.config
  echo conf.treeToYaml(n[0])
  echo "offs ", n[1].sym.name.s, " ", n[1].sym.offset, " ", n[1].sym.position
  echo conf.treeToYaml(n[1])
  if n[0].kind == nkSym:
    result = newLoad(
      conf.mapLoadKind(n[1].sym.typ), 0, 1,
      newAdd32(
        w.gen(n[0], wasmproc, n.kind), # base object loc
        newConst(n[1].sym.offset) # field offset
      )
    )
  else:
    echo "#TODO: dotexpr on non sym ", n[0].kind
    result = newLoad(
      conf.mapLoadKind(n[1].sym.typ), 0, 1,
      newAdd32(
        w.gen(n[0], wasmproc, n.kind), # base object loc
        newConst(n[1].sym.offset) # field offset
      )
    )

proc genBracketExpr(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, 
  parentKind: TNodeKind=nkNone): WasmNode =
  let conf = w.config
  #echo conf.treeToYaml(n)
  var baseoffset = 0'i32
  if n[0].typ.kind in {tySequence, tyString}:
    baseoffset = 2*4 # len, cap * sizeof(pointer)
  result = newLoad(
    conf.mapLoadKind(n[0].sym.typ.lastSon), 0, 1,
    # symloc + basepos + pos*sizetype
    newAdd32(
      w.gen(n[0], wasmproc, n.kind), # base array/strin/seq loc
      newAdd32(
        newMul32(
          w.gen(n[1], wasmproc, n.kind),
          newConst(n[0].typ.lastSon.size.toInt128.toInt32)
        ), # element offset
        newConst(baseoffset)
      )
      
    )
  )

proc genIfStmt(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, parentKind: TNodeKind=nkNone): WasmNode =
  #echo "nkIfstmt",treeToYaml n
  # ifstmt are recursive for now
  result = newNop()
  
  for bidx in countdown(n.len-1,0):
    #result = gen else1
    #result2 = gen if1 else result1
    #result3 = gen if2 else result2
    if n[bidx].kind == nkElse:
      result = w.gen(n[bidx][0], wasmproc, n.kind)
    else:
      result = newIfElse(w.gen(n[bidx][0], wasmproc, n.kind), w.gen(n[bidx][1], wasmproc, n.kind), result)

proc genRaise(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, parentKind: TNodeKind=nkNone): WasmNode =
  let sym = w.graph.getCompilerProc("nimRaise")
  let b = w.graph.backend.Backend
  if not b.hasProc(sym):
    w.genProc(sym, w.config)
  let (id, imported) = b.generatedProcs[sym]
  echo "#genRaise"
  echo w.config.treeToYaml(n)
  result = newCall(id, w.gen(n[0][1], wasmproc, n.kind), imported) # CHECK: is n[0][1] always correct?

proc genTypeInfo(w: WasmGen, typ: PSym, wasmproc: var WAsmFunction, parentKind: TNodeKind=nkNone) =
  # want: name, maybe size, align, subfields?
  let conf = w.config
  let b = w.graph.backend.Backend
  #let n = typ.ast  
  #var son = n[0]
  b.m.globals.add(
    newGlobal(b.nextGlobalIdx, vtI32, newConst(b.stackptr), false, false, typ.name.s)
  )
  typ.updateLoc(b.nextGlobalIdx, locGlobalVar, OnStatic)
  inc b.nextGlobalIdx
  let bytes = typ.name.s.len.int32.toBytes & typ.name.s.len.int32.toBytes & (typ.name.s).toBytes
  b.m.data.add(newData(b.stackptr, typ.name.s.toBytes, typ.name.s & " :name"))
  b.moveStackPtrBy(bytes.len)
  
proc gen(w: WasmGen, n:PNode, wasmproc: var WAsmFunction, parentKind: TNodeKind=nkNone): WasmNode =
  # TODO: go through https://nim-lang.org/docs/macros.html#statements for inspirationn

  result = newOpList() # try to fix crashes due to nil
  if n.kind in nkGenSkippedKinds: return
  let conf = w.config
  let b = Backend(w.graph.backend)
  
  echo "#GTL: ", $n.kind, " parent: ", parentKind, " module: ", conf.toFilename(n.info.fileIndex)
  echo "# working on: ", n.kind
  if not (n.kind == nkStmtList):
    echo renderTree(n)
    
  case n.kind:
  of nkGenSkippedKinds: discard
  of nkCallKinds: 
    # TODO: prepare args on stack?
    if n.sons[0].sym.magic != mNone:
      result = genMagicCall(w, n, n.sons[0].sym.magic, wasmproc, parentKind)
    else: 
      result = w.genCall(n, wasmproc, parentKind)
  of nkLetSection, nkConstSection:
    # sons: identdefs
    for son in n.sons:
      result.sons.add(w.genIdentDef(son, wasmproc, n.kind))
    #echo conf.treeToYaml(n)
  of nkVarSection:
    # special treatment since it probably needs to go in linear memory (unless it's a local)
    for son in n.sons:
      result.sons.add(w.genVar(son, wasmproc, n.kind))
  of nkConv, nkHiddenStdConv:
    result = w.genConv(n, wasmproc, n.kind)
  of nkSym:
    echo "#GTL loading from sym ", n.sym.name.s
    #echo conf.symToYaml(n.sym)
    if n.sym.kind == skType:
      if not b.hasTypeInfo(n.sym):
        w.genTypeInfo(n.sym, wasmproc, n.kind)
    result = w.backendDerefNode(n.sym)
  of nkCurly:
    result = w.genCurly(n, wasmproc, n.kind)
  of nkBlockStmt:
    #echo conf.treeToYaml(n)
    # CHECK: is the outer block any use?
    # n[0]: blockname, n[1] the body
    # TODO: with proc newBlock(name, body): WasmNode
    # result = newBlock(n[0].tobytes, w.gen(n[1], wasmproc, n.kind))
    result = w.gen(n[1], wasmproc, n.kind)
  of nkWhileStmt:
    # echo conf.treeToYaml(n)
    result = newWhileLoop(
      w.gen(n[0], wasmproc, n.kind), # condition
      w.gen(n[1], wasmproc, n.kind)  # body
    )
  of nkLiterals: #TODO: other literals
    result = w.genLit(n, parentKind)
  of nkNilLit: #TODO: other literals
    result = w.genLit(n, parentKind)
  of nkStmtList, nkStmtListExpr:
    for son in n.sons:
      let tmp = w.gen(son, wasmproc, n.kind)
      if not tmp.isNil and not(tmp.kind == opList and tmp.sons.len == 0): 
        # since some nkKinds are skipped, we may produce nil nodes. 
        #TODO: fix that instead of using this workaround
        result.sons.add(tmp)
  of nkAsgn, nkFastAsgn:
    result = w.genAsgn(n[0], n[1], wasmproc)
  of nkReturnStmt:
    result = newReturn(w.gen(n.sons[0],wasmproc, n.kind))
  of nkHiddenAddr: # CHECK: can I marge with nkAddr?
    # to generate:
    # get global
    # store 
    # load index stored to
    # todo: some types can maybe skip this??
    if n.skipHidden.kind == nkSym:
      result = newOpList(
        newStore(
          conf.mapStoreKind(n.skipHidden.sym.typ), 
          conf.symLoc(n.skipHidden),
          0, 
          newLoad(memLoadI32, 0, 1, newConst(4'i32) )
        ), #load where to store from the stackptr
        newLoad(memLoadI32, 0, 1, newConst(4'i32))
      )
    else:
      result = newOpList(
        newStore(
          conf.mapStoreKind(n.skipHidden[1].sym.typ), 
          conf.symLoc(n.skipHidden),
          0, 
          newLoad(memLoadI32, 0, 1, newConst(4'i32) )
        ), #load where to store from the stackptr
        newLoad(memLoadI32, 0, 1, newConst(4'i32))
      )
  of nkAddr:
    # return the ptr value 
    result = newConst(n[0].sym.getLoc)    
  of nkHiddenDeref: # CHECK: can merge with nkDeref
    result = newLoad(
      conf.mapLoadKind(n.skipHidden.sym.typ.skipTypes({tyVar})), 0, 1, 
      conf.symLoc(n.skipHidden))
  of nkDerefExpr:
    result = newLoad(conf.mapLoadKind(n.typ), 0, 1, conf.symLoc(n[0]))
  of nkBracket:
    result = w.genBracket(n, wasmproc, n.kind)
  of nkExprColonExpr:
    result = w.gen(n[1], wasmproc, n.kind)
  of nkObjConstr:
    result = w.genObjConstr(n, wasmproc, n.kind)
  of nkTupleConstr:
    result = w.genTupleConstr(n, wasmproc, n.kind)
  of nkDotExpr:
    result = w.genDotExpr(n, wasmproc, n.kind)
  of nkBracketExpr:
    result = w.genBracketExpr(n, wasmproc, n.kind)
  of nkIfStmt:
    result = w.genIfStmt(n, wasmproc, n.kind)    
  of nkPragmaBlock:
    result = w.gen(n.lastSon, wasmproc, n.kind)
  of nkRaiseStmt:
    result = w.genRaise(n, wasmproc, n.kind)
  #TODO: nkCast, nkCaseStmt, nkIfExpr, nkCurlyExpr(same as bracketexpr)...
  else:
    echo "# Missing kind ", n.kind
    echo renderTree(n)
    echo conf.treeToYaml(n)
    conf.internalError("#GTL is missing kind: " & $n.kind)

proc updateNimInit(b: Backend) =
  # Update the init expression
  if b.nimInit.body.sons.len<1: 
    echo "# Empty nimInitBody"
  #b.m.functions.add(b.nimInit)
  b.m.functions[0].typ = b.nimInit.typ
  b.m.functions[0].body = b.nimInit.body
  b.m.functions[0].locals = b.nimInit.locals
  echo "#updated nimInit at index init: ", b.nimInit.id

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
  if backend.m.name notin toFilename(w.config, n.info): return # FIXME: this skippes everything not coming from mainmodule
  var transfN = transformStmt(w.graph,w.s,n)
  if transfN.kind in nkGenSkippedKinds: return

  echo "#WASM#>P ", $n.kind, " transfKind: ", transfN.kind, " from ", w.config.toFilename(n.info.fileIndex)  
  #echo renderTree(transfN)
  
  if transfN.kind == nkStmtList: 
    for son in transfN:
      # we dont call gen on transfN directly to avoid the whole module being processed at once, which would screw up
      # with order of execution of load/stores when they are inserted by us, eg in callMagic
      let tmp = w.gen(son, backend.nimInit, transfN.kind)
      
      # reduces useless empty opLists
      if not tmp.isNil and not(tmp.kind == opList and tmp.sons.len == 0): 
        backend.nimInit.body.sons.add(tmp)
  else:
    let tmp = w.gen(transfN, backend.nimInit, transfN.kind)
    # reduces useless empty opLists
    if not tmp.isNil and not(tmp.kind == opList and tmp.sons.len == 0): 
      backend.nimInit.body.sons.add(tmp)
    
  echo "#WASM#<P ", $n.kind


proc myClose(graph: ModuleGraph; b: PPassContext, n: PNode): PNode =
  if passes.skipCodegen(graph.config, n): return n
  echo "#WASM#C ", $n.kind, " from ", graph.config.toFilename(n.info.fileIndex)
  result = myProcess(b, n)
  var w = WasmGen(b)
  if w.s.flags.contains(sfMainModule):
    # finalize the module
    var backend = Backend(graph.backend)
    backend.updateNimInit()
    backend.putHeapPtr()
    #echo "#BackendNAME: ", Backend(graph.backend).m.name
    let outfile = w.config.prepareToWriteOutput

    if optRun in w.config.globalOptions or w.config.isDefined("testing"):
      # -d:testing is set by testament when running tests

      # generate a js file suitable to be run by node
      writeFile($outfile.changeFileExt("js"), w.config.getConfigVar("glue.loaderNode") % [w.s.name.s, w.config.getConfigVar("glue.jsHelpers") % [w.s.name.s]])
      # TODO: remove this, no need for the html version if it's for nodejs
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
  
  var w = WasmGen(s: s, graph:graph, config: graph.config)

  w.s = s
  # this is to persist the backend between modules, 
  # otherwise it would get reinited at every myOpen of a new module
  if w.graph.backend.isNil:
    w.graph.backend = newBackend("main") # main is a placeholder, will get updated later
  if s.flags.contains(sfMainModule):
    Backend(w.graph.backend).updateBackendName(s.name.s)
  result = w
  echo "#WASM#<O ",graph.config.toFilename(s.info.fileIndex)," s.name: ",$s.name.s

const WasmGenPass* = makePass(myOpen, myProcess, myClose)
