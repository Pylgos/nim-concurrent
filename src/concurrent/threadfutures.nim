import chronos
import ./smartptrs
import std/[tables]


type
  ThreadFutureObj*[T] = object
  ThreadFuture*[T] = SharedPtr[ThreadFutureObj[T]]


var wakers: Table[int, ]
