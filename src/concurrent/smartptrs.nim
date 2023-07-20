import std/[isolation, macros, typetraits, strformat]
import threading/atomics

proc raiseNilAccess() {.noinline.} =
  raise newException(NilAccessDefect, "dereferencing nil smart pointer")

const
  debug {.booldefine: "concurrent.smartptrs.debug".}: bool = false
  leakCheck {.booldefine: "concurrent.smartptrs.leakCheck".}: bool = false

type
  ReferrerId = int

  Destructor = proc(self: pointer) {.nimcall, raises: [].}

  Inner[T] = object
    strong: Atomic[int]
    weak: Atomic[int]
    destructor: Destructor
    val: T

  SharedPtr*[T] = object
    p: ptr Inner[T]
    when debug:
      id: ReferrerId

when debug or leakCheck:
  const logHeader = "concurrent/smartptrs: "

  func debugLog(s: varargs[string, `$`]) =
    {.cast(noSideEffect).}:
      stdout.write logHeader
      for ss in s:
        stdout.write ss
      stdout.write '\n'

  var
    allocCount: Atomic[int]
    freeCount: Atomic[int]

when debug:
  import std/[tables, rlocks, strutils, hashes]

  type
    ReferrerInfo = object
      stackTrace: string

    PtrInfo = object
      typeName: string
      referrers: Table[ReferrerId, ReferrerInfo]

  var
    refCount: int
    unrefCount: int
    referrerIdCounter = 1
    ptrInfoStorage = createShared(Table[pointer, PtrInfo])
    refLocationLock: RLock
  
  initRLock refLocationLock

  proc newId(): ReferrerId =
    result = referrerIdCounter
    inc referrerIdCounter

  addQuitProc() do() {.noconv.}:
    debugLog "new count: ", allocCount.load(Relaxed)
    debugLog "free count: ", freeCount.load(Relaxed)
    debugLog "reference count: ", refCount
    debugLog "unreference count: ", unrefCount
    withRLock refLocationLock:
      for (address, info) in ptrInfoStorage[].pairs:
        debugLog "Still referenced: "
        debugLog "  address: ", repr address
        debugLog "  typeName: ", info.typeName
        debugLog "  refCount: ", cast[ptr Inner[void]](address).strong.load()
        debugLog "  referrers:"
        for (id, referrerInfo) in info.referrers.pairs:
          debugLog "    id=", id, " stackTrace:"
          for line in referrerInfo.stackTrace.indent(6).splitLines():
            debugLog line

  proc `==`*[T](a, b: SharedPtr[T]): bool =
    a.p == b.p
  
  proc hash*[T](a: SharedPtr[T]): Hash =
    hash(a.p)

when leakCheck:
  addQuitProc() do() {.noconv.}:
    if allocCount.load(Relaxed) != freeCount.load(Relaxed):
      debugLog "@@@@@@@@ MEMORY LEAK @@@@@@@@"
      when not debug:
        debugLog "new count: ", allocCount.load(Relaxed)
        debugLog "free count: ", freeCount.load(Relaxed)
      quit(1)

proc repr[T](p: SharedPtr[T]): string =
  const typName = $T
  fmt"SmartPtr[{typName}]({repr cast[pointer](p.p)})"

template traceNew[T](sp: SharedPtr[T]) =
  when debug or leakCheck:
    allocCount.atomicInc()
  when debug:
    withRLock refLocationLock:
      inc refCount
      let id = newId()
      ptrInfoStorage[][sp.p] = PtrInfo(
        typeName: $typeof(sp.p.val),
        referrers: toTable({id: ReferrerInfo(stackTrace: getStackTrace())})
      )
      sp.id = id
    debugLog "created: ", repr(sp)

template traceReference[T](dest: var SharedPtr[T], src: SharedPtr[T]) =
  when debug:
    withRLock refLocationLock:
      inc refCount
      let id = newId()
      ptrInfoStorage[][src.p].referrers[id] = ReferrerInfo(stackTrace: getStackTrace())
      dest.id = id
    debugLog "referenced: ", repr(src)

template traceDestroy[T](sp: SharedPtr[T]) =
  when debug or leakCheck:
    freeCount.atomicInc()
  when debug:
    inc unrefCount
    withRLock refLocationLock:
      ptrInfoStorage[].del sp.p
    debugLog "destroyed: ", repr(sp)

template traceUnreference[T](sp: SharedPtr[T]) =
  when debug:
    withRLock refLocationLock:
      doAssert sp.id != 0
      inc unrefCount
      ptrInfoStorage[][sp.p].referrers.del sp.id
    debugLog "unreferenced: ", repr(sp)

template traceSink[T](dest: SharedPtr[T], src: SharedPtr[T]) =
  when debug:
    dest.id = src.id
    if src.p != nil and src.id != 0:
      withRLock refLocationLock:
        ptrInfoStorage[][src.p].referrers[src.id].stackTrace = getStackTrace()

proc `=destroy`*[T](sp: SharedPtr[T]) =
  if sp.p != nil:
    if sp.p.strong.fetchSub(1, AcqRel) == 1:
      sp.p.destructor(addr sp.p.val)
      traceDestroy sp
      if fetchSub(sp.p.weak, 1, AcqRel) == 1:
        deallocShared(sp.p)
    else:
      traceUnreference(sp)

proc `=copy`*[T](dest: var SharedPtr[T], src: SharedPtr[T]) =
  `=destroy`(dest)
  if src.p != nil:
    discard fetchAdd(src.p.strong, 1, Relaxed)
    traceReference dest, src
  dest.p = src.p

when declared(system.`=dup`):
  proc `=dup`*[T](src: SharedPtr[T]): SharedPtr[T] =
    if src.p != nil:
      discard fetchAdd(src.p.strong, 1, Relaxed)
      traceReference result, src
    result.p = src.p

proc `=sink`*[T](dest: var SharedPtr[T], src: SharedPtr[T]) =
  `=destroy`(dest)
  dest.p = src.p
  traceSink(dest, src)

proc getDefaultDestructor(T: typedesc): Destructor =
  proc destructor(p: pointer) {.nimcall, raises: [].} =
    {.cast(raises: []).}:
      # HACK: compiler bug workaround
      var v = cast[ptr T](p)
      `=destroy`(v[])
  result = destructor

proc newSharedPtr*[T](val: sink Isolated[T], destructor: Destructor = getDefaultDestructor(T)): SharedPtr[T] {.nodestroy.} =
  ## Returns a shared pointer which shares
  ## ownership of the object by reference counting.
  result.p = cast[typeof(result.p)](allocShared(sizeof(result.p[])))
  result.p.destructor = destructor
  result.p.strong.store(1)
  result.p.weak.store(1)
  result.p.destructor = destructor
  result.p.val = extract val
  traceNew result

template newSharedPtr*[T](val: T): SharedPtr[T] =
  newSharedPtr(isolate(val))

proc newSharedPtr*[T](t: typedesc[T], destructor: Destructor = getDefaultDestructor(T)): SharedPtr[T] =
  ## Returns a shared pointer. It is not initialized,
  ## so reading from it before writing to it is undefined behavior!
  when not supportsCopyMem(T):
    result.p = cast[typeof(result.p)](allocShared0(sizeof(result.p[])))
  else:
    result.p = cast[typeof(result.p)](allocShared(sizeof(result.p[])))
  result.p.strong.store(1)
  result.p.weak.store(1)
  result.p.destructor = destructor
  traceNew result

type
  WeakPtr*[T] = object
    p: ptr Inner[T]

proc `=destroy`*[T](wp: WeakPtr[T]) =
  if wp.p != nil:
    if fetchSub(wp.p.weak, 1, AcqRel) == 1:
      deallocShared(wp.p)

proc `=copy`*[T](dest: var WeakPtr[T], src: WeakPtr[T]) =
  `=destroy`(dest)
  if src.p != nil:
    discard fetchAdd(src.p.weak, 1, Relaxed)
  dest.p = src.p

when defined(nimHasDup):
  proc `=dup`*[T](src: WeakPtr[T]): WeakPtr[T] =
    if src.p != nil:
      discard fetchAdd(src.p.weak, 1, Relaxed)
    result.p = src.p

proc toWeak*[T](sp: SharedPtr[T]): WeakPtr[T] =
  if sp.p != nil:
    discard fetchAdd(sp.p.weak, 1, Relaxed)
    result.p = sp.p

proc lock*[T](wp: WeakPtr[T]): SharedPtr[T] =
  if wp.p != nil:
    var n = wp.p.strong.load(Relaxed)
    if n == 0:
      return
    while true:
      if wp.p.strong.compareExchangeWeak(n, n + 1, Relaxed):
        when debug:
          withRLock refLocationLock:
            inc refCount
            let id = newId()
            ptrInfoStorage[][wp.p].referrers[id] = ReferrerInfo(stackTrace: getStackTrace())
            return SharedPtr[T](p: wp.p, id: id)
        else:
          return SharedPtr[T](p: wp.p)

proc `==`*[T](p: SharedPtr[T], t: typeof(nil)): bool {.inline.} =
  p.p == t

proc isNil*[T](p: SharedPtr[T]): bool {.inline.} =
  p.p == nil

template checkNotNil(p: SharedPtr) =
  when compileOption("boundChecks"):
    {.line.}:
      if isNil(p):
        raiseNilAccess()

proc strongCount*(p: SharedPtr): int =
  p.p.strong.load(Relaxed)

converter `[]`*[T](p: SharedPtr[T]): var T {.inline.} =
  checkNotNil(p)
  p.p.val

proc `[]=`*[T](p: SharedPtr[T], val: sink Isolated[T]) {.inline.} =
  checkNotNil(p)
  p.p.val = extract val

template `[]=`*[T](p: SharedPtr[T]; val: T) =
  `[]=`(p, isolate(val))

proc get*[T](p: SharedPtr[T]): ptr T {.inline.} =
  checkNotNil(p)
  addr p.p.val

proc `$`*[T](p: SharedPtr[T]): string {.inline.} =
  if p.p == nil: "nil"
  else: "(val: " & $p.p.val & ")"

macro baseTypeOf(t: typed): typedesc =
  var impl = t.getTypeImpl()
  if impl[1].kind == nnkEmpty:
    result = nnkCall.newTree(ident"typeof", nnkNilLit.newNimNode())
  else:
    result = impl[1][0]

proc castTo*[T, U](p: SharedPtr[T], _: typedesc[U]): SharedPtr[U] =
  when T isnot void and U isnot void:
    assert offsetOf(Inner[T], val) == offsetOf(Inner[U], val)
  cast[SharedPtr[U]](p)

proc toBase*[T](p: SharedPtr[T]): auto =
  p.castTo(baseTypeOf p[])

{.experimental: "dotOperators".}

template `.`*[T](p: SharedPtr[T], f: untyped): untyped =
  p[].f

template `.=`*[T](p: SharedPtr[T], f: untyped, v: untyped): untyped =
  p[].f = v

template Weak*[T](_: typedesc[SharedPtr[T]]): untyped =
  WeakPtr[T]

template exportDerefConverter*(PtrTy: typedesc[SharedPtr]): untyped =
  converter `[]`*(self: PtrTy): var PtrTy.T {.inject.} =
    smartptrs.`[]`(self)
