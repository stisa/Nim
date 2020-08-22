discard """
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""
proc log(x:SomeOrdinal) {.header:"glue", importc:"echoInt".}
proc log(x:string) {.header:"glue", importc:"echoString".}

for i in 1..100:
  if i mod 15==0:
    log "FizzBuzz"
  elif i mod 5==0:
    log "Buzz"
  elif i mod 3==0:
    log "Fizz"
  else:
    log i