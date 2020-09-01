discard """
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""

type A = ref object
  id: int
  f: float32
  #s: string

var 
  b : A
  c : A
new b
doAssert(b.id==0)
b.id = 13
doAssert(b.id == 13)
new c
c = b
c.f = 3.14'f32
doAssert(c.id == 13)
doAssert(c.f == 3.14'f32)
