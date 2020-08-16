import
  ast, astalgo, options, msgs, idents, types, passes,
  ropes, wordrecg, modulepaths, transf,
  tables, os, strutils, pathutils,
  wasm/[wasmast, wasmstructure, wasmencode, wasmnode, wasmleb128, wasmrender], wasmutils

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
    initExprs: seq[WasmNode] # sequence of initializer expressions. for use in start sec
    nextImportIdx: Natural # function index space ( doesn't account for hoisting of imported procs )
    nextFuncIdx: Natural # the function index space (only for non-imported funcs)
    nextGlobalIdx: Natural # the global index space
    nextMemIdx: Natural # the linear memory index space
    nextTableIdx: Natural # the table index space
    m : WAsmModule #current module
    generatedProcs: Table[string,tuple[id:int,imported:bool]] # name, funcIdx
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
    generatedProcs: initTable[string,tuple[id:int,imported:bool]](),
    generatedTypeInfos: initTable[string,int32](),
    )
  
  result.nextFuncIdx = 0
  result.nextImportIdx = 0
  result.nextGlobalIdx = 0
  result.nextTableIdx = 0
  # 4 byte aligned, reserve 8 bytes to store the stack pointer
  # This mean effective address start at 12?
  result.nextMemIdx = 0
  result.initExprs = newSeq[WasmNode]()
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


proc symLoc(s: PNode): WasmNode =
  # TODO: if sym is a param, this should be:
  # result = newGet(woGetLocal, s.position) or something like that
  if s.sym.kind == skParam:
      result = newGet(woGetLocal, s.sym.position)
  elif s.sym.loc.k == locGlobalVar:
    result = newGet(woGetGlobal, s.sym.loc.pos)
  else:
    echo "#symloc: TODO: other than global"

proc hasProc(b: Backend, sym: PSym): bool =
  sym.mangleName in b.generatedProcs

proc getProc(b: Backend, sym: PSym): tuple[id: int, imported: bool] =
  b.generatedProcs[sym.mangleName]

# this is to persist the backend between modules, 
# otherwise it would get reinited at every myOpen of a new module
# TODO: move logic for this  in open...
var backend: Backend = newBackend("main")

proc newWasmGen(s:PSym, g: ModuleGraph): WasmGen =
  result = WasmGen(s: s, graph:g, config: g.config)

proc storeLit(b: Backend, n: PNode, conf: ConfigRef): WasmNode =
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

proc callMagic(w:WasmGen, n: PNode, magic:TMagic): WasmNode =
  echo "#MAGIC: ", magic
  echo w.config.treeToYaml(n)
  case magic:
  of mAddF64: result = newBinaryOp(fbAdd64, w.gen(n.sons[1],w.config), w.gen(n.sons[2],w.config))
  of mAddI: result = newBinaryOp(ibAdd32, w.gen(n.sons[1],w.config), w.gen(n.sons[2],w.config))
  else:
    echo "TODO magic", magic
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
        b.nextImportIdx, ekFunction, headername, importcname, n.sym.mangleName, proctype, n.sym.flags.contains(sfExported)
      )
    )
    # the id of the proc is the import id, because we can then hoist it in a later phase
    # by simply having non-imports start from last(importId), eg id = nextImportIdx+nextFuncIdx
    b.generatedProcs[n.sym.mangleName] = (b.nextImportIdx, true)
    inc b.nextImportIdx
  else:
    echo "#GNP: nim proc aren't really generated yet, proc: ", n.sym.name.s, " module: ", conf.toFilename(n.info.fileIndex)
    # TODO:
    var wasmProcBody: WasmNode
    var transfBody = transformBody(w.graph, procDef[namePos].sym, cache=false)
    echo "#tbd\n", conf.treeToYaml(transfBody)
    wasmProcBody = w.gen(transfBody, conf)
    b.m.functions.add(
      newFunction(
        b.nextFuncIdx, proctype,
        wasmProcBody, @[]#[params?]#, procDef[namePos].sym.name.s, 
        procDef[namePos].sym.flags.contains(sfExported)
      )
    )
    
    b.generatedProcs[n.sym.mangleName] = (b.nextFuncIdx, false)
    inc b.nextFuncIdx
    
    #echo conf.treeToYaml(transfBody) 
    

proc genLit(w: WasmGen, n: PNode, conf: ConfigRef, parentKind: TNodeKind): WasmNode =
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
    result = newConst(b.stackptr)
    # TODO: also store rest of stuff in initexprs
  else:
    echo "#GNL TODO other literals"

proc genAsgn(w: WasmGen, n: PNode, conf: ConfigRef,): WasmNode =
  #TODO:
  echo conf.treeToYaml(n)
  var ns = n.sons[0].skipHidden()
  
  if ns.kind != nkSym: 
    echo "# asgn not a sym but ", ns.kind
  if ns.sym.owner.kind == skModule: # globals
    if ns.sym.typ.kind == tyVar:
      # need to treat it as a pointer
      result = newStore(conf.mapStoreKind(ns.sym.typ.skipTypes({tyVar})),w.gen(n.sons[1], conf, n.kind), 0, ns.symLoc)
    else:
      result = newSet(woSetGlobal, ns.getLoc, w.gen(n.sons[1], conf, n.kind))
  elif ns.sym.owner.kind == skProc: # locals
    if ns.sym.typ.kind == tyVar:
      # need to treat it as a pointer
      result = newStore(conf.mapStoreKind(ns.sym.typ.skipTypes({tyVar})),w.gen(n.sons[1], conf, n.kind), 0, ns.symLoc)
    elif ns.sym.kind == skResult:
      result = w.gen(n.sons[1], conf, n.kind)
    else:
      result = newSet(woSetLocal, ns.getLoc, w.gen(n.sons[1], conf, n.kind))
proc gen(w: WasmGen, n: PNode, conf: ConfigRef, parentKind: TNodeKind=nkNone): WasmNode =
  # TODO: go through https://nim-lang.org/docs/macros.html#statements for inspirationn
  result = newOpList() # try to fix crashes due to nil
  if n.kind in nkGenSkippedKinds: return
  let b = Backend(w.graph.backend)
  echo "#GTL: ", $n.kind, " parent: ", parentKind, " module: ", conf.toFilename(n.info.fileIndex)
  case n.kind:
  of nkGenSkippedKinds: discard
  of nkCallKinds: # may be missing some kinds, TODO: check
    # 0-> proc sym, 1..->arg(s)
    echo "#GTL call kind ", n.kind

    if n.sons[0].sym.magic != mNone:
      return callMagic(w, n, n.sons[0].sym.magic)
    #if n.sons[0].sym.typ.callConv == ccInline: # means this is an inlined proc?
    #  let transfbody = transformBody(w.graph, n.sons[0].sym, true)
    #  echo "# AN INLINED PROC? \n", conf.treeToYaml(n.sons[0].sym.transformedBody)
    #  # problem: in inlined procs, skparam shouldn't be used
    #  return w.gen(transfbody, conf, n.sons[0].kind)
    if not b.hasProc(n.sons[0].sym) :
      #TODO: generate proc for non imported procs
      w.genProc(n.sons[0], conf)
    let (id, isImport) = b.getProc(n.sons[0].sym)
    var args : seq[WasmNode] = @[]
    #if n.sons[0].sym.ast[resultPos].kind != nkEmpty:
    #  args.add(newConst(0'i32)) # the return
    var toUpdate: seq[PSym] = @[]
    # we may need to generate a set global after execution to update var types params 
    if n.sons.len > 1: # at least 1 argument
      for i, arg in n.sons:
        if i == 0: continue # skip first arg (should be nkSym of the proc)
        echo "#ARG: \n", conf.treeToYaml(arg)
        if arg.typ.kind == tyVar: toUpdate.add(arg.skipHidden.sym)
        args.add(w.gen(arg, conf, n.kind))
    if toUpdate.len == 0:
      result=newCall(id, args, isImport)
    else:
      result.sons.add(newCall(id, args, isImport))
      # update var params
      for sym in toUpdate:
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
  of nkSectionKinds:
    # sons: identdefs
    for son in n.sons:
      # discard since this goes directly in the globals part of the module
      discard w.gen(son, conf, n.kind)
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
      let mut = if parentKind == nkVarSection: true else: false

      # if sons[2](aka val) is nkEmpty, we can skip the generation by just moving 
      # the stack pointer by size(type), otherwise we actually have to perform the store
      if n.sons[2].kind in {nkEmpty, nkNilLit} :
        # TODO: match the type and value type
        # TODO: only export some globals
        b.m.globals.add(newGlobal(b.nextGlobalIdx, conf.mapType(s.typ), newConst(0'i32),true, mut, n[0].sym.mangleName))  
        
      #  echo "#GTL elided store due to empty val ", s.name.s
      #  b.moveStackPtrBy(s.typ.size)
      elif n.sons[2].kind in nkLiterals-nkStrKinds:
        # for numericals, just store in the global
        b.m.globals.add(newGlobal(b.nextGlobalIdx, conf.mapType(s.typ), w.genLit(n.sons[2],conf, n.kind), true, mut, n[0].sym.mangleName))  
                                              # TODO: initexprs part is useless for literals?
                                              # it may be useful for arrays? I doubt it.
      elif n.sons[2].kind in {nkCurly,nkBracket,nkObjConstr}:
        #TODO: non-literal store
        echo "#GTL non literal store ", n.sons[2].kind, " for ", s.name.s
        #FIXME: 
        b.m.globals.add(newGlobal(
          b.nextGlobalIdx, 
          conf.mapType(s.typ), 
          newConst(b.stackptr.int32), 
          true,
          mut, 
          n[0].sym.mangleName)
        )
      elif n.sons[2].kind == nkSym:
        echo "#GTL RHS is nkSym for ", s.name.s
        #echo conf.symToYaml(n.sons[2].sym)
        if n.sons[2].sym.kind == skEnumField:
          # for skEnumField, sym.position is the ordinal value of the enum.
          # TODO: enum with holes?
          b.m.globals.add(newGlobal(b.nextGlobalIdx, conf.mapType(s.typ), newConst(n.sons[2].sym.position.int32), true, mut, n[0].sym.mangleName))  
        else:
          echo "#GTL RHS nkSym missing kind :", n.sons[2].sym.kind
      else:
        echo "#GTL non literal RHS ", n.sons[2].kind, " for ", s.name.s
        # FIXME:
        b.m.globals.add(newGlobal(
          b.nextGlobalIdx, 
          conf.mapType(s.typ), 
          newConst(b.stackptr.int32), 
          true,
          mut, 
          n[0].sym.mangleName)
        )  
        #TODO: b.initExprs.add(w.gen(n.sons[2], conf, n.kind))
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
    result = w.genAsgn(n, conf)
  of nkReturnStmt:
    result = newReturn(w.gen(n.sons[0],conf))
  of nkHiddenAddr:
    # to generate:
    # get global
    # store 
    # load index stored to
    # todo: some types can maybe skip this??
    result = newOpList(
      newStore(
        conf.mapStoreKind(n.skipHidden.sym.typ), 
        n.skipHidden.symLoc, 
        0, 
        newLoad(memLoadI32, 0, 1, newConst(4'i32) )
      ), #load where to store from the stackptr
      newLoad(memLoadI32, 0, 1, newConst(4'i32))
    )
  of nkHiddenDeref:
    result = newLoad(conf.mapLoadKind(n.skipHidden.sym.typ.skipTypes({tyVar})), 0, 1, n.skipHidden.symLoc)
  else:
    echo "#GTL is missing kind: ", n.kind

proc genInitFunc(b: Backend) =
  # Generate the init expression
  if b.initExprs.len<1: 
    echo "# Empty InitExprs"
    return # no expression, no need for a init proc
  b.m.functions.add(
    newFunction(
      b.nextFuncIdx, newType(vtNone),  newOpList(b.initExprs), @[], "nimInit", true
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
  var transfN = transformStmt(w.graph,w.s,n)
  if transfN.kind in nkGenSkippedKinds: return

  echo "#WASM#>P ", $n.kind, " from ", w.config.toFilename(n.info.fileIndex)  
  let tmp = w.gen(transfN, w.config)
  #TODO: this may be wrong if for example n is nkCallKind and the owner of n is a skProc? Can that even go through myProcess?
  if not tmp.isNil:
    if not(tmp.kind == opList and tmp.sons.len == 0):
      # TODO: fix useless empty opLists, need a recursive check that at least a leaf node is not empty?
      backend.initExprs.add(tmp)
  #if w.s.flags.contains(sfMainModule):
  #  echo w.config.treeToYaml(n)
  #  let generated = w.gen(n)
  #  if not generated.isNil: w.initExprs.add(generated)
  
  #echo "#WASM#<P ", $n.kind


proc myClose(graph: ModuleGraph; b: PPassContext, n: PNode): PNode =
  if passes.skipCodegen(graph.config, n): return n
  echo "#WASM#C ", $n.kind, " from ", graph.config.toFilename(n.info.fileIndex)
  result = myProcess(b, n)
  var w = WasmGen(b)
  if w.s.flags.contains(sfMainModule):
    # finalize the module
    var backend = Backend(graph.backend)
    backend.genInitFunc() #TODO: fixme
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
