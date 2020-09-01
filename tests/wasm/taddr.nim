discard """
  targets:  "wasm"
  action:   "run"
  timeout:  60.0
"""
var x = 123.4

let px = addr x

doAssert x==123.4

var z = px[]

doAssert z==x

px[] += 432.1

doAssert x==555.5

doAssert z==123.4