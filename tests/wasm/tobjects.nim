discard """
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""

type A = object
  b: int
  c: float32

var x = A(c: 1.2)

var y = A(b:13, c: 1.4)

doAssert(x.c - 1.2 < 0.01) # due to imprecision in promoting f32 to f64
doAssert(y.b == 13)