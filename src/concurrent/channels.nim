import std/[deques, locks, isolation]


type
  ChanData[T] = object
    guard: Lock
    spaceAvailable: Cond
    dataAvailable: Cond
    buffer: Deque[Isolated[T]]

  Chan*[T] = object
    size: Natural
    data: ptr ChanData[T]

proc `=copy`[T](dest: var Chan[T], src: Chan[T]) {.error.}

proc `=destroy`[T](self: Chan[T]) =
  if self.data != nil:
    deinitLock self.data.guard
    deinitCond self.data.spaceAvailable
    deinitCond self.data.dataAvailable
    `=destroy`(self.data.buffer)
    deallocShared self.data

proc initChan*(T: typedesc, size = -1): Chan[T] = 
  result.data = createShared(ChanData[T])
  initLock result.data.guard
  initCond result.data.spaceAvailable
  initCond result.data.dataAvailable
  if size == -1:
    result.size = Natural.high
  else:
    result.size = size
    result.data.buffer = initDeque[Isolated[T]](size)

proc send*[T](self: var Chan[T], item: sink Isolated[T]) =
  withLock self.data.guard:
    if self.data.buffer.len == self.size:
      wait self.data.spaceAvailable, self.data.guard
    
    self.data.buffer.addFirst item
    
    signal self.data.dataAvailable

proc trySend*[T](self: var Chan[T], item: sink Isolated[T]): bool =
  withLock self.data.guard:
    if self.data.buffer.len == self.size:
      return false
    
    self.data.buffer.addFirst item
    
    signal self.data.dataAvailable
  return true

proc recvIso*[T](self: var Chan[T]): Isolated[T] =
  withLock self.data.guard:
    while self.data.buffer.len == 0:
      wait self.data.dataAvailable, self.data.guard
    
    result = self.data.buffer.popLast()

    if self.data.buffer.len == self.size - 1:
      signal self.data.spaceAvailable

proc tryRecvIso*[T](self: var Chan[T], dest: var Isolated[T]): bool =
  withLock self.data.guard:
    if self.data.buffer.len == 0:
      return false

    dest = self.data.buffer.popLast()

    if self.data.buffer.len == self.size - 1:
      signal self.data.spaceAvailable
  return true

proc recv*[T](self: var Chan[T]): T =
  var tmp = self.recvIso()
  tmp.extract()

proc tryRecv*[T](self: var Chan[T], dest: var T): bool =
  var tmp: Isolated[T]
  result = self.tryRecvIso(tmp)
  if result:
    dest = tmp.extract()

template send*[T](self: var Chan[T], item: sink T) =
  send(self, isolate(item))

template trySend*[T](self: var Chan[T], item: sink T): bool =
  trySend(self, isolate(item))

proc size*(self: Chan): Natural =
  self.size
