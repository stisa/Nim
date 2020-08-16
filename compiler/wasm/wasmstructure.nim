from wasmast import WasmNode, WasmExternalKind, WasmValueType, Consts

type
  WAsmModule* = ref object
    name*: string
    imports*: seq[WAsmImport]
    functions*: seq[WAsmFunction]
    exports*: seq[WAsmExport]
    memory*: WAsmMemory
    data*: seq[WAsmData]
    globals*: seq[WAsmGlobal]
  
  WasmType* = ref object
    params*: seq[WasmValueType]
    res*: WasmValueType
  
  WAsmImport* = ref object
    module,name: string
    mangledName*: string
    kind: WasmExternalKind
    idx: Natural
    typ*: WasmType
    exported*: bool
  
  WAsmExport* = ref object
    name: string
    kind: WasmExternalKind
    idx: Natural
  
  WAsmFunction* = ref object
    idx: Natural
    hoistedIndex*: int
    name*: string
    typ*: WasmType
    body*: WasmNode
    locals*: seq[WasmValueType]
    exported*: bool

  WAsmMemory* = ref object
    idx, pages: Natural

  WAsmData* = ref object
    idx: Natural
    payload*: seq[byte]
    name*: string # optional, used for debug
    # kind: WasmValueType

  WAsmGlobal* = ref object
    idx: Natural
    typ*: WasmValueType
    mut*: bool
    val*: WasmNode
    name*: string # optional, used for debug
    exported*: bool
    # kind: WasmValueType


proc newType*(rs: WasmValueType,
  prs: varargs[WasmValueType]): WasmType = WasmType(params: @prs, res: rs)

proc newImport*(id: Natural, kd: WasmExternalKind, 
  module, name:string, mangledName:string, typ: WasmType, exported:bool = false): WAsmImport =
  WAsmImport( module: module, name: name, mangledName: mangledName, kind: kd,
    idx: id, typ: typ, exported: exported)
proc id*(i: WAsmImport): Natural = i.idx
proc module*(i: WAsmImport): string = i.module
proc kind*(i: WAsmImport): WasmExternalKind = i.kind
proc name*(i: WAsmImport): string = i.name


proc newExport*(id: Natural, kd: WasmExternalKind, name:string): WAsmExport =
  WAsmExport(name: name, kind: kd, idx: id)
proc id*(e: WAsmExport): Natural = e.idx
proc kind*(e: WAsmExport): WasmExternalKind = e.kind
proc name*(e: WAsmExport): string = e.name

proc newFunction*(idx: Natural, typ: WasmType, code: WasmNode, 
  lc: seq[WasmValueType] = @[], name: string = "unknownFn",  
  exported:bool = false): WAsmFunction =
  WAsmFunction(idx: idx, hoistedIndex: -1, name: name,
    typ: typ, body: code, locals: lc, exported:exported)
proc id*(f: WAsmFunction): Natural = f.idx

proc newMemory*(pages: Natural = 1): WAsmMemory = 
  WAsmMemory(idx: 1, pages: pages)
proc id*(m: WAsmMemory): Natural = m.idx
proc pages*(m: WAsmMemory): Natural = m.pages

proc newData*(id: Natural, payload: openArray[byte], name:string = ""): WAsmData = #, kind: WasmValueType
  WAsmData(idx: id, payload: @payload, name: name) #, kind: kind)
proc index*(d: WAsmData): Natural = d.idx

proc newGlobal*(id: Natural, typ: WasmValueType, val: WasmNode, exp: bool = true, mut: bool = false, name:string = ""): WAsmGlobal = #, kind: WasmValueType
  # val is the value of the global as a wasmnode. the node should be a const[typ] value.
  assert val.kind in Consts
  WAsmGlobal(idx: id, typ: typ, val: val, exported: exp, mut:mut, name: name)
proc index*(d: WAsmGlobal): Natural = d.idx

proc newModule*(nm: string=""): WAsmModule = 
  result = WAsmModule(name: nm)
  result.imports = @[]
  result.exports = @[]
  result.functions = @[]
  result.data = @[]
  result.memory = newMemory(0)
  
#proc name*(m: WAsmModule): string = m.name
