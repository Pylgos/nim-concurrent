import std/[deques, locks, isolation]


type
  Chan*[T] = object
    initialized: bool
    size: Natural
    guard: Lock
    buffer {.guard: guard.}: Deque[Isolated[T]]
    spaceAvailable: Cond
    dataAvailable: Cond

proc `=copy`[T](dest: var Chan[T], src: Chan[T]) {.error.}

proc `=destroy`[T](self: var Chan[T]) =
  if self.initialized:
    deinitLock self.guard
    deinitCond self.spaceAvailable
    deinitCond self.dataAvailable
    self.initialized = false
  {.locks: [self.guard]}:
    `=destroy`(self.buffer)


proc initChan*(T: typedesc, size = -1): Chan[T] = 
  if size == -1:
    result.size = Natural.high
  else:
    result.size = size
    {.locks: [result.guard]}:
      result.buffer = initDeque[Isolated[T]](size)
  initLock result.guard
  initCond result.spaceAvailable
  initCond result.dataAvailable
  result.initialized = true

proc send*[T](self: var Chan[T], item: sink Isolated[T]) =
  withLock self.guard:
    if self.buffer.len == self.size:
      wait self.spaceAvailable, self.guard
    
    self.buffer.addFirst item
    
    if self.buffer.len == 1:
      signal self.dataAvailable

proc trySend*[T](self: var Chan[T], item: sink Isolated[T]): bool =
  withLock self.guard:
    if self.buffer.len == self.size:
      return false
    
    self.buffer.addFirst item
    
    if self.buffer.len == 1:
      signal self.dataAvailable
  return true

proc recvIso*[T](self: var Chan[T]): Isolated[T] =
  withLock self.guard:
    if self.buffer.len == 0:
      wait self.dataAvailable, self.guard
    
    result = self.buffer.popLast()
    
    if self.buffer.len - 1 == self.size:
      signal self.spaceAvailable

proc tryRecvIso*[T](self: var Chan[T], dest: var Isolated[T]): bool =
  withLock self.guard:
    if self.buffer.len == 0:
      return false
    
    dest = self.buffer.popLast()
    
    if self.buffer.len - 1 == self.size:
      signal self.spaceAvailable
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
