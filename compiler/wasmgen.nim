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
    nimInitBody: seq[WasmNode] # sequence of operations that make up the top-level of the program
    nextImportIdx: Natural # function index space ( doesn't account for hoisting of imported procs )
    nextFuncIdx: Natural # the function index space (only for non-imported funcs)
    nextGlobalIdx: Natural # the global index space
    nextMemIdx: Natural # the linear memory index space
    nextTableIdx: Natural # the table index space
    m : WAsmModule #current wasm module
    generatedProcs: Table[PSym,tuple[id:int,imported:bool]] # name, funcIdx
    generatedTypeInfos: Table[string, int32] # name, location in memory TODO:
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

proc updateLoc(s: PSym, loc: int, kind: TLocKind, skind: TStorageLoc) =
  s.loc.k = kind
  s.loc.storage = skind
  s.loc.pos = loc
  s.loc.r = loc.rope # for debug purposes

proc getLoc(s: PSym): int =
  result = s.loc.pos  
  if s.loc.k != locGlobalVar:
    echo "#getloc: TODO: other than global"

proc hash(s:PSym): Hash = hash(s.mangleName)

proc symLoc(conf: ConfigRef, n: PNode): WasmNode =
  # TODO: study var params
  if n.kind == nkSym:
    if n.sym.kind == skParam:
        result = newGet(woGetLocal, n.sym.position)
    elif n.sym.loc.storage == OnStatic:
      result = newGet(woGetGlobal, n.sym.loc.pos)
    elif n.sym.loc.storage == OnHeap:
      result = newLoad(conf.mapLoadKind(n.sym.typ), 0, 1, newConst(n.sym.loc.pos))
    else:
      conf.internalError "#symloc: TODO: other than global"
  else:
    conf.internalError "#NOT A SYM for Symloc"

proc hasProc(b: Backend, sym: PSym): bool =
  sym in b.generatedProcs

const nkGenSkippedKinds = { nkCommentStmt, nkPragma, nkEmpty, 
                            nkTemplateDef, nkFuncDef, nkProcDef, nkMethodDef, 
                            nkIteratorDef, nkMacroDef, nkIncludeStmt, 
                            nkImportStmt, nkExportStmt, nkExportExceptStmt, 
                            nkImportExceptStmt, nkImportAs, nkConverterDef,
                            nkIncludeStmt, nkTypeSection}#, nkWhenStmt, nkWhenExpr }

const nkSectionKinds = {nkVarSection, nkConstSection, nkLetSection}

proc gen(w: WasmGen, n: PNode, conf: ConfigRef, parentKind: TNodeKind=nkNone): WasmNode

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
  of mInc:
    echo w.config.treeToYaml(n)
    let s = if n[1].kind == nkSym: n[1].sym else: n[1][0].sym
    result =  newStore(
      w.config.mapStoreKind(s.typ),
      newBinaryOp(ibAdd32, w.gen(n[1], w.config), w.gen(n[2], w.config)),
      0,
      newConst(s.getLoc), # TODO: proper fix
    )
  of mDec:
    let s = if n[1].kind == nkSym: n[1].sym else: n[1][0].sym
    result =  newStore(
      w.config.mapStoreKind(s.typ),
      newBinaryOp(ibSub32, w.gen(n[1], w.config), w.gen(n[2], w.config)),
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
    var lc = if proctype.res != vtNone: @[proctype.res] else: @[]
    b.m.functions.add(
      newFunction(
        b.nextFuncIdx, proctype,
        wasmProcBody, lc#[params?]#, procDef[namePos].sym.name.s, 
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
  #echo conf.treeToYaml(lhs)
  #echo conf.treeToYaml(rhs)
  var ns = lhs.skipHidden()
  
  if ns.kind != nkSym: 
    conf.internalError("# asgn not to a sym but " & $ns.kind)
  # TODO: use loc.k to know how to store
  if ns.sym.owner.kind == skModule: # globals
    if ns.sym.typ.kind == tyVar:
      # need to treat it as a pointer
      result = newStore(conf.mapStoreKind(ns.sym.typ.skipTypes({tyVar})),w.gen(rhs, conf, nkAsgn), 0, conf.symLoc(ns))
    else:
      result = newStore(conf.mapStoreKind(ns.sym.typ), w.gen(rhs, conf, nkAsgn), 0, newConst(ns.sym.getLoc))
  elif ns.sym.owner.kind == skProc: # locals
    if ns.sym.typ.kind == tyVar:
      # need to treat it as a pointer
      result = newStore(conf.mapStoreKind(ns.sym.typ.skipTypes({tyVar})),w.gen(rhs, conf, nkAsgn), 0, conf.symLoc(ns))
    elif ns.sym.kind == skResult:
      result = w.gen(rhs, conf, nkAsgn)
    else:
      result = newStore(conf.mapStoreKind(ns.sym.typ), w.gen(rhs, conf, nkAsgn), 0, newConst(ns.sym.getLoc))
      #result = newSet(woSetLocal, ns.sym.getLoc, w.gen(rhs, conf, nkAsgn))
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
      args.add(w.gen(arg, conf, n.kind))
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
proc genVar(w: WasmGen, n: PNode, conf: ConfigRef, parentKind: TNodeKind=nkNone): WasmNode =
  # sons: 0->symbol, 1->type, 2->val
    # usually, sym.typ is more reliable than n.sons[1] for type
    # this should be handed to a store proc?
    # note that if symbol doesnt have sfUsed+sfMainModule or sfExported, we should be allowed to skip codegen
    # TODO: this will start to fail once we deal with procs, as they are the owners of the inner syms.
    #       hopefully they will still have sfUsed?
    let s = n.sons[0].sym
    let b = Backend(w.graph.backend)

    if s.exportOrUsed:
      
      let 
        mut = parentKind == nkVarSection
        exp = s.owner.flags.contains(sfMainModule) and s.flags.contains(sfExported)
      if not mut: conf.internalError("let/const went through the wrong codegen path")
      let lockind = if s.owner.kind == skModule: locGlobalVar
                    else: locLocalVar
      s.updateLoc(b.stackptr, lockind, OnHeap) # OnHeap => on the linear memory
      # TODO: differntiate between OnHeap(refs)/OnStack(rest)
      
      # if sons[2](aka val) is nkEmpty, we can skip the generation by just moving 
      # the stack pointer by size(type), otherwise we actually have to perform the store
      if n.sons[2].kind in {nkEmpty, nkNilLit} :
        echo "#GTL elided store due to empty val ", s.name.s
      elif n.sons[2].kind in nkLiterals-nkStrKinds:
        # for numericals, just store in the global
        result = newStore(conf.mapStoreKind(s.typ), w.genLit(n.sons[2],conf, n.kind), 0, newConst(b.stackptr))  
      elif n.sons[2].kind == nkSym:
        echo "#GTL RHS is nkSym for ", s.name.s
        #echo conf.symToYaml(n.sons[2].sym)
        if n.sons[2].sym.kind == skEnumField:
          # for skEnumField, sym.position is the ordinal value of the enum.
          # TODO: enum with holes?
          result = newStore(conf.mapStoreKind(s.typ), newConst(n.sons[2].sym.position.int32), 0, newConst(b.stackptr))    
        else:
          echo "#GTL RHS nkSym kind :" & $n.sons[2].sym.kind
          # move stackptr size typ, update it after
          result = w.genAsgn(n[0], n[2], conf)
      else:
        echo "#GTL non literal RHS ", n.sons[2].kind, " for ", s.name.s
        # move stackptr size typ, update it after
        result = w.genAsgn(n[0], n[2], conf)
      b.moveStackPtrBy(s.typ.size)

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
  of nkLetSection, nkConstSection:
    # sons: identdefs
    for son in n.sons:
      result.sons.add(w.gen(son, conf, n.kind))
    #echo conf.treeToYaml(n)
  of nkVarSection:
    # special treatment since it needs to go in linear memory
    for son in n.sons:
      result.sons.add(w.genVar(son, conf, n.kind))
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
      # TODO: if s.owner.kind == skProc: use locals (locals don't need to be created)   
      let 
        mut = parentKind == nkLetSection # let section may need to be updated at runtime
        exp = s.owner.flags.contains(sfMainModule) and s.flags.contains(sfExported)
      if parentKind == nkVarSection: conf.internalError("var identdef went through the wrong codegen path")
      let lockind = locGlobalVar # TODO: if s.owner.kind == skModule: locGlobalVar
                    #else: locLocalVar
      s.updateLoc(b.nextGlobalIdx, lockind, OnStatic) # OnStatic means let/const are in a wasm global/local
      
      
      if n.sons[2].kind in {nkEmpty, nkNilLit} :
        b.m.globals.add(newGlobal(b.nextGlobalIdx, conf.mapType(s.typ), newConst(0'i32),exp, mut, n[0].sym.name.s))  
      elif n.sons[2].kind in nkLiterals-nkStrKinds:
        # for numericals, just store in the global
        b.m.globals.add(newGlobal(b.nextGlobalIdx, conf.mapType(s.typ), w.genLit(n.sons[2],conf, n.kind), exp, mut, n[0].sym.name.s))  
                    
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
              newNop(), 
              #w.gen(n[2], conf, n.kind),
              exp, mut, n[0].sym.name.s
            )
          )
          result = newSet(woSetGlobal, n[0].sym.getLoc, w.gen(n[2], conf, nkAsgn))
          
      else:
        echo "#GTL non literal RHS ", n.sons[2].kind, " for ", s.name.s
        b.m.globals.add(
          newGlobal(
            b.nextGlobalIdx, conf.mapType(s.typ), 
            newNop(), #w.gen(n[2], conf, n.kind),# 
            exp, mut, n[0].sym.name.s
          )
        )
        result = newSet(woSetGlobal, n[0].sym.getLoc, w.gen(n[2], conf, nkAsgn))
      inc b.nextGlobalIdx
      echo "#nextglobalidx ", b.nextGlobalIdx
      echo "#globals", b.m.globals.len
  
  of nkSym:
    echo "#GTL loading from sym ", n.sym.name.s
    #echo conf.symToYaml(n.sym)
    result = conf.symLoc(n)
  of nkCurly:
    #echo conf.treeToYaml(n)
    echo conf.typeToYaml(n[0].typ)
    #conf.internalError("nkCurly not implemented")
    result = newConst(b.stackptr)
    for son in n:
      if son.kind in nkLiterals:  
        let bytes = conf.wasmConstToBytes(w.gen(son, conf, n.kind), conf.getSize(n.typ.lastSon))
        b.m.data.add(
          newData(
            b.stackptr, 
            bytes, "setelemnt"
          )
        )
        b.moveStackPtrBy(bytes.len)
      else:
        # it's some pointer indirection, store it and move by 4bytes
        # TODO:should make copies of non shallow types
        b.nimInitBody.add(newStore(
            memStoreI32, w.gen(son, conf, n.kind), 0, newConst(b.stackptr)
        ))
        b.moveStackPtrBy(4) #size of a pointer TODO: read it from conf?
  of nkBlockStmt:
    #echo conf.treeToYaml(n)
    # TODO: is the outer block any use?
    # n[0]: blockname, n[1] the body
    result = w.gen(n[1], conf, n.kind)
  of nkWhileStmt:
    # echo conf.treeToYaml(n)
    result = newWhileLoop(
      w.gen(n[0], conf, n.kind), # condition
      w.gen(n[1], conf, n.kind)  # body
    )
  of nkLiterals: #TODO: other literals
    result = w.genLit(n, conf, parentKind)
  of nkStmtList, nkStmtListExpr:
    result = newOpList()
    for son in n.sons:
      let tmp = w.gen(son, conf, n.kind)
      if not tmp.isNil and not(tmp.kind == opList and tmp.sons.len == 0): 
        # since some nkKinds are skipped, we produce nil nodes. 
        #TODO: fix that instead of using this workaround
        result.sons.add(tmp)
  of nkAsgn, nkFastAsgn:
    result = w.genAsgn(n[0], n[1], conf)
  of nkReturnStmt:
    result = newReturn(w.gen(n.sons[0],conf))
  of nkHiddenAddr: # TODO: nkAddr
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
  of nkAddr: # TODO: nkAddr
    # to generate:
    # get global
    # store 
    # load index stored to
    # TODO: some types can maybe skip this??
    # This kinda works but the global and the ptr are not in sync are they?
    # Maybe just disallow this for stuff that lives in wasm globals/locals?
    # Eg. if typ in {tyIntegerLike, tyFloatLike}: internalerror
    #echo conf.treeToYaml(n)
    # could i instead pass around the index of the global?
    # that would allow the value to be changed if I figure
    # how deref would work...
    #option 1:
    # return the ptr value 
    result = newConst(n[0].sym.getLoc)
    
    #[b.nimInitBody.add(
      newStore(
        conf.mapStoreKind(n[0].sym.typ), 
        conf.symLoc(n[0]),
        0, 
        #load where to store from the stackptr
        newConst(b.stackptr) 
      )
    )
    b.moveStackPtrBy(4)]#
    # option 2: with globals index
    #result = newConst(n[0].getLoc)
    
    # TODO: need to move the stackptr?
  of nkHiddenDeref:
    result = newLoad(conf.mapLoadKind(n.skipHidden.sym.typ.skipTypes({tyVar})), 0, 1, conf.symLoc(n.skipHidden))
  of nkDerefExpr:
    result = newLoad(
      conf.mapLoadKind(n.typ), 0, 1, 
      conf.symLoc(n[0])
    )
    
    # option2 with global index
    # can't index with nodes? Is my ast limitation or wasm's?
    # TODO: what about locals
    # result = newGet(woGetGlobal, w.gen(n[0], conf, n.kind))
  of nkBracket:
    if n.typ.flags.contains(tfVarargs):
      result = newOpList()
      #echo conf.treeToYaml(n)
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
          # TODO: in result or in nimInitBody?
          result.sons.add newStore(
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
      #echo conf.treeToYaml(n)
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
    #echo conf.treeToYaml(n)
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
  of nkIfStmt:
    #echo "nkIfstmt",treeToYaml n
    # ifstmt are recursive for now
    result = newNop()
    
    for bidx in countdown(n.len-1,0):
      #result = gen else1
      #result2 = gen if1 else result1
      #result3 = gen if2 else result2
      if n[bidx].kind == nkElse:
        result = w.gen(n[bidx][0], conf, n.kind)
      else:
        result = newIfElse(w.gen(n[bidx][0], conf, n.kind), w.gen(n[bidx][1], conf, n.kind), result)
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
  if backend.m.name notin toFilename(w.config, n.info): return # FIXME: this skippes everything not coming from mainmodule
  var transfN = transformStmt(w.graph,w.s,n)
  if transfN.kind in nkGenSkippedKinds: return

  echo "#WASM#>P ", $n.kind, " transfKind: ", transfN.kind, " from ", w.config.toFilename(n.info.fileIndex)  
  if transfN.kind == nkBlockStmt: transfN = transfN[1] # FIXME: a proper fix instead of skipping the outer block
  #echo renderTree(transfN)
  for son in transfN:
    # we dont call gen on transfN directly to avoid the whole module being processed at once, which would screw up
    # with order of execution of load/stores when they are inserted by us, eg in callMagic
    let tmp = w.gen(son, w.config)
    
    # reduces useless empty opLists
    if not tmp.isNil and not(tmp.kind == opList and tmp.sons.len == 0): 
      backend.nimInitBody.add(tmp)
      #echo son.kind
      #echo tmp.render
  
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