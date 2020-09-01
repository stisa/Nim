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
doAssert(high(b.id) == 2147483647)
doAssert(low(b.id) == -2147483648 )

var ar  = [1.0'f32,2,3]

doAssert(low(ar)==0) # 0
doAssert(high(ar)==2) # 2

doAssert(ar[low(ar)] == 1.0) # 1.0
doAssert(ar[high(ar)] == 3.0) # 3.0