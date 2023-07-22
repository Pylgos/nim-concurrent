import mainthreadids


type DestructorContainer = object
  procs: seq[proc() {.closure, gcsafe, raises: [].}]

proc `=destroy`(self: DestructorContainer) =
  for p in self.procs:
    p()

var destructors: DestructorContainer

proc addThreadDestructor*(p: proc() {.closure, gcsafe, raises: [].}) {.gcsafe.} =
  if getThreadId() == mainThreadId:
    {.cast(gcsafe).}:
      destructors.procs.add p
  else:
    onThreadDestruction(p)
