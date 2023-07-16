import concurrent/channels
import std/unittest

test "test channels":
  var chan = initChan(int, 1)
  var thread: Thread[ptr Chan[int]]
  proc th(chan: ptr Chan[int]) =
    for i in 0..<100:
      check chan[].recv() == 1
  createThread(thread, th, addr chan)
  for i in 0..<100:
    chan.send(1)
  joinThread(thread)
