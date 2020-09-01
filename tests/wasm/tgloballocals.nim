discard """
  targets:  "wasm"
  action:   "run"
  timeout:  60.0
  exitcode: 0
"""

let a = 12
let b = 12.2
let c = true
var aa = 12
var bb = 12.2
var cc = true
const aaa = 12
const bbb = 12.2
const ccc = true

doAssert a == 12
doAssert aa == 12
doAssert aaa == 12
doAssert b == 12.2
doAssert bb == 12.2
doAssert bbb == 12.2
doAssert c
doAssert cc
doAssert ccc

proc lc() =
  var s = "# locals:"
  let a = 12
  let b = 12.2
  let c = true
  var aa = 12
  var bb = 12.2
  var cc = true
  const aaa = 12
  const bbb = 12.2
  const ccc = true
  #log s
  doAssert a == 12
  doAssert aa == 12
  doAssert aaa == 12
  doAssert b == 12.2
  doAssert bb == 12.2
  doAssert bbb == 12.2
  doAssert c
  doAssert cc
  doAssert ccc
lc()
