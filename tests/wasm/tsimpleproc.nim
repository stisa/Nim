discard """
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""


proc a(x:int, b: float) =
  doAssert(x.float+b == 3.2)

a(1,2.2)