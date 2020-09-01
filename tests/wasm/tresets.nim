discard """
  targets:  "wasm"
  action:   "run"
  timeout:  60.0
  exitcode: 0
"""

type A = ref object
  id: int
  f: float32

var 
  b : A
new b
doAssert(b.id == 0)
b.id = 13
b.f = 3.14'f32
doAssert(b.id == 13)
doAssert(b.f == 3.14'f32)
reset b
doAssert(b.id == 0)
doAssert(b.f == 0.0'f32)
