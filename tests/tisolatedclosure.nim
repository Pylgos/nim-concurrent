import std/unittest
import concurrent/isolatedclosures

test "test isolated closure":
  proc test(arg: int): proc(a: int){.isolatedClosure.} =
    proc(thing: int) {.isolatedClosure.} =
      check arg == 123
      check thing == 456
  test(123)(456)
