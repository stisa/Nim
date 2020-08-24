discard """
  targets:  "wasm"
  action:   "run"
  timeout:  60.0
"""

proc check(x:bool) {.header:"glue", importc:"assert".}
proc log[T](x:T) {.header:"glue", importc:"log".}
proc log(x:SomeFloat) {.header:"glue", importc:"echoFloat".}
proc log(x:SomeOrdinal) {.header:"glue", importc:"echoInt".}
proc log(x:bool) {.header:"glue", importc:"echoBool".}
proc log(x:string) {.header:"glue", importc:"echoString".}

var x = 123.4

let px = addr x

check x==123.4

log px

var z = px[]

check z==x

px[] += 432.1

check x==555.5

log px

check z==123.4