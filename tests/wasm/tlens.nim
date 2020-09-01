discard """
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""

var c = newSeq[int](3)
c[1] = 123
c[2] = 456
var d : seq[float]
newSeq(d, 4)
d[1] = 12.3
d[2] = 45.6

var e = [1,2,3]

var f = "hell"

doAssert len(c) == 3
doAssert len(d) == 4
doAssert len(e) == 3
doAssert len(f) == 4