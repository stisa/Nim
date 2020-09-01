discard """
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""

var sl = 1..12
doAssert(sl.a == 1)
doAssert(sl.b == 12)
var sl2 = ..4
doAssert(sl2.b == 4)

var ar  = [0.0'f32,1,2]
var b = 1..12
type R = object
  a: range[1..12]
doAssert ar is array
doAssert ar[1] is float32
doAssert 10 in b
doAssert(not(-1 in b))
var r = R(a:3)
doAssert r.a == 3