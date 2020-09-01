discard """
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""

proc a(x:int, b: float): float =
  result = x.float+b

var x = a(1,2.2)

doAssert x == 3.2