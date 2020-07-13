discard """
  output: '''asdas
processClient end
false
MEMORY 0
'''
  cmd: '''nim c --gc:arc $file'''
"""

type
  PAsyncHttpServer = ref object
    value: string
  PFutureBase {.acyclic.} = ref object
    callback: proc () {.closure.}
    value: string
    failed: bool

proc accept(server: PAsyncHttpServer): PFutureBase =
  new(result)
  result.callback = proc () =
    discard
  server.value = "hahaha"

proc processClient(): PFutureBase =
  new(result)

proc serve(server: PAsyncHttpServer): PFutureBase =
  iterator serveIter(): PFutureBase {.closure.} =
    echo server.value
    while true:
      var acceptAddrFut = server.accept()
      yield acceptAddrFut
      var fut = acceptAddrFut.value

      # with the new scope based destruction, this cannot
      # possibly work:
      var f {.cursor.} = processClient()
      # It also seems to be the wrong way how to avoid the
      # cycle. The cycle is caused by capturing the 'env'
      # part from 'env.f'.
      when true:
        f.callback =
          proc () =
            echo("processClient end")
            echo(f.failed)
      yield f
  var x = serveIter
  for i in 0 .. 1:
    result = x()
    if result.callback != nil:
      result.callback()

let mem = getOccupiedMem()

proc main =
  discard serve(PAsyncHttpServer(value: "asdas"))

main()
echo "MEMORY ", getOccupiedMem() - mem
