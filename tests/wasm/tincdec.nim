discard """
  targets:  "wasm"
  action:   "run"
  timeout:  60.0
  exitcode: 0
"""

var c = 1234
var d = succ c
doAssert d == 1235
var e = pred c 
doAssert e == 1233
inc(d)
doAssert d == 1236
dec(e)
doAssert e == 1232
