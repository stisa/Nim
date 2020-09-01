discard """
  targets:  "wasm"
  action:   "run"
  timeout:  60.0
  exitcode: 0
"""

var t* = true
var w* = false
#inc t
doAssert((not t) == false)
doAssert((t and w) == false)
doAssert((t or w) == true)
doAssert((t xor w) == true)