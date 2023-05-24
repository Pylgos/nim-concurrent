
import mainthreadids


type DestructorContainer = object
  procs*: seq[proc() {.closure, gcsafe, raises: [].}]

proc `=destroy`(self: var DestructorContainer) =
  for p in self.procs:
    p()

var destructors: DestructorContainer

proc addThreadDestructor*(p: proc() {.closure, gcsafe, raises: [].}) =
  if getThreadId() == mainThreadId:
    destructors.procs.add p
  else:
    onThreadDestruction(p)
