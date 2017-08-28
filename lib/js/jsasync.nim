import macros

type 
  Promise {.importc.} [T] = object of RootObj
  Future* [T] = ref Promise[T]
  FutureError* = object of Exception

proc newFuture*[T](executor: proc(resolve: proc(val: T), reject: proc(reason: auto))): Future[T] {.importcpp: "new Promise(#)".}
proc newFuture*(executor: proc(resolve: proc(), reject: proc(reason: auto))): Future[void] {.importcpp: "new Promise(#)".}

proc resolve*[T](val: T): Future[T] {.importcpp: "Promise.resolve(#)",discardable.}
proc reject*[T](reason: T): Future[T] {.importcpp: "Promise.reject(#)",discardable.}
proc race*[T](iterable: openarray[T]): Future[T] {.importcpp: "Promise.race(#)",discardable.}
proc all*[T](iterable: openarray[Future[T]]): Future[seq[T]] {.importcpp: "Promise.all(#)",discardable.}

{.push importcpp, discardable.}
proc then*[T](p: Future[T], onFulfilled: proc(val: T)):auto
proc then*[T](p: Future[T], onFulfilled: proc(val: T), onRejected: proc(reason: auto)): auto
proc catch*[T](p: Future[T], onRejected: proc(reason: auto)): auto
{.pop.}

macro async*(prc: untyped): untyped =
  prc.addPragma(newIdentNode("jsasync"))
  result = prc

proc await*[T](whatever: T): T {.importcpp: "await #", discardable.}
proc await*[T](whatever: Future[T]): T {.importcpp: "await #", discardable.}

proc complete*[T](future: var Future[T], val: T) = 
  future = resolve(val)

proc setTimeout(cb: proc, ms: int){.importc.}

proc sleepAsync*(ms: int): Future[void] {.discardable.}=
  newFuture(
    proc(resolve: proc(), reject: proc(reason: string)) =
      setTimeout(resolve, ms)
  )

proc asyncCheck*[T](future: Future[T]) =
  future.catch(proc (reason: string) =
    var err = newException(FutureError, reason)
    raise err
  )

proc `$`*[T](p: Future[T]): string =
  result = ""
  p.then(proc(val: T) =
    result = $val
  )
