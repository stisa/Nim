discard """
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""

proc log(x:bool) {.header:"glue", importc:"echoBool".}
var 
  i = 30
  t = i<=10
  x = i == 30
  b = true
log t
log x
log b