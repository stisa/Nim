discard """
  targets:  "wasm"
  action:   "run"
  timeout:  60.0
  exitcode: 0
"""


type
  Enum1 = enum
    Field1 = 3, Field2
  Enum2 = enum
    Place1, Place2 = 3
var
  e1 = Field1
  e2 = Enum1(Place2)
doAssert(e1 == e2)