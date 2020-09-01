discard """
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""

type A = enum
  aa, ab, ac

var 
  a = ab
  b = aa
doAssert(not(a <= b))
doAssert(a <= ab)

var
  pa = addr a
  pb = addr b
doAssert(pa <= pb)

var
  sa = "hello"
  sb = "world"
doAssert(sa <= sb)

var
  ca = 'x'
  cb = 'y'
doAssert(ca <= cb)

var
  ba = true
  bb = false
doAssert(not(ba <= bb))

var 
  ta = {aa,ab}
  tb = {ac}
doAssert(not(ta == tb))

var
  ra : ref int
  rb : ref int
new ra
new rb
doAssert(ra <= rb)
ra = rb
doAssert(not(ra < rb))

#[Mising: EqProc]#
type R = object
  a: range[1..12]

var 
  ar  = [0.0'f32,1,2]
  r = R(a:2)
doAssert(cmp(r.a, high(ar))==0)