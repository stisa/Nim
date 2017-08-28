import jsasync, times

proc test1() {.async.} =
  let t = epochTime()
  await sleepAsync(2000)
  let dt = epochTime()-t

  doassert(dt >= 2.0)

test1()

proc resolveAfter2Seconds(i: int): Future[int] {.async.} =
  new result
  await sleepAsync(2000)
  result.complete(i)

proc add1(x: int): Future[int] {.async.}=
  new result
  let a = resolveAfter2Seconds(29)
  result.complete( x + await a)

proc test2(): Future[void] {.async.} =
  let 
    t = epochTime()
    val = await add1(12)
    dt = epochTime() - t
  
  doAssert(dt >= 2.0)
  doAssert(val == 41)

asyncCheck test2()
