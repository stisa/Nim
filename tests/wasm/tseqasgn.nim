discard """
  targets:  "wasm"
  action:   "run"
  timeout:  60.0
  exitcode: 0
"""

var c = newSeq[int](3)
doAssert(c[1] == 0)
c[1] = 123
doAssert(c[1] == 123)