import std/unittest
import concurrent/smartptrs

test "down casting":
  type Base = object of RootObj
  type O = object of Base

  var destroyed = false
  proc `=destroy`(o: var O) =
    check not destroyed
    destroyed = true

  var sp1 = newSharedPtr(O)
  var sp2: SharedPtr[Base] = sp1.toBase()
  `=destroy`(sp1)
  `=destroy`(sp2)
  check destroyed == true

test "up casting":
  type Base = object of RootObj
  type O = object of Base
  
  var destroyed = false
  proc `=destroy`(o: var O) =
    check not destroyed
    destroyed = true

  var sp1 = newSharedPtr(O)
  var sp2: SharedPtr[Base] = sp1.toBase()
  `=destroy`(sp1)
  `=destroy`(sp2)
  check destroyed == true

test "weak pointers":
  var wp0: WeakPtr[int]

  block:
    var sp1 = newSharedPtr(44)
    check sp1[] == 44

    block:
      var sp2 = sp1
      check sp2 == sp1

    var wp1 = sp1.toWeak()
    check wp1.lock[] == 44

    block:
      var wp2 = wp1
      check wp2 == wp1

    var sp2 = wp1.lock()
    check sp1 == sp2

    wp0 = sp1.toWeak()
    check wp0.lock() != nil
    check wp0.lock()[] == sp1[]
  
  check wp0.lock() == nil

test "dot operators":
  var sp = newSharedPtr(tuple[a: int, b: float, c: string])
  sp.a = 1
  sp.b = 1.2
  sp.c = "123"

  check sp.a == 1
  check sp.b == 1.2
  check sp.c == "123"

test "default destructor":
  var ok = false
  type Impl = object
  proc `=destroy`(a: var Impl) =
    ok = true
  type O = object
    f: Impl
  block:
    discard newSharedPtr(O)
  check ok
