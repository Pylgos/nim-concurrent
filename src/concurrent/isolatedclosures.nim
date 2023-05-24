import std/[macros, tables, strformat, isolation]
import cps/rewrites

type
  IsolatedClosure*[T] = object
    fn: T
    env: pointer
    destructor: proc(env: pointer) {.nimcall, gcsafe, raises: [].}

proc `=copy`[T](dest: var IsolatedClosure[T], src: IsolatedClosure[T]) {.error.}

proc `==`*[T](a: IsolatedClosure[T], b: T): bool =
  a.fn == b

proc `=destroy`[T](self: var IsolatedClosure[T]) =
  if self.env != nil and self.destructor != nil:
    self.destructor(self.env)
    self.env = nil

proc nilIsolatedClosure*(T: typedesc[IsolatedClosure]): T =
  T()

proc isolatedClosureType(orig: NimNode): NimNode =
  let fnTyp = orig.kind.newNimNode()
  orig.copyChildrenTo(fnTyp)
  fnTyp.params.insert(1,
    newIdentDefs(genSym(nskParam, "env"), bindSym"pointer")
  )
  fnTyp.addPragma ident"nimcall"
  fnTyp.addPragma ident"gcsafe"
  quote do:
    IsolatedClosure[`fnTyp`]

proc isCapturedVar(p, n: NimNode): bool =
  let o = n.owner()
  o != p

proc findCapturedVarsAux(result: var Table[string, NimNode], procSym, node: NimNode) =
  if node.kind == nnkSym:
    if node.symKind in {nskLet, nskVar, nskParam}:
      if procSym.isCapturedVar(node):
        result[$node] = node
  else:
    for child in node:
      findCapturedVarsAux(result, procSym, child)

proc findCapturedVars(procDef: NimNode): Table[string, NimNode] =
  procDef.expectKind {nnkProcDef, nnkLambda, nnkDo}
  findCapturedVarsAux(result, procDef.name, procDef.body)

proc replaceCapturedVarsAux(vars: Table[string, NimNode], procSym, node, envType, envSym: NimNode): NimNode =
  result = node.copyNimNode()
  case node.kind
  of nnkSym:
    if node.symKind in {nskLet, nskVar, nskParam}:
      if procSym.isCapturedVar(node):
        let field = ident($node)
        result = nnkDotExpr.newTree(
          nnkCast.newTree(
            nnkPtrTy.newTree(
              envType
            ),
            envSym
          ),
          field
        )
  else:
    for i, child in node:
      result.add replaceCapturedVarsAux(vars, procSym, child, envType, envSym)

proc replaceCapturedVars(vars: Table[string, NimNode], procDef, envType, envSym: NimNode) =
  procDef.body = procDef.body.normalizingRewrites().workaroundRewrites().NimNode
  procDef.body = replaceCapturedVarsAux(vars, procDef.name, procDef.body, envType, envSym)

proc makeEnvType(vars: Table[string, NimNode]): NimNode =
  result = nnkTupleTy.newNimNode()
  for (name, node) in vars.pairs:
    result.add newIdentDefs(ident(name), node.getTypeInst())

macro cannotIsolateError(node: untyped) =
  error(fmt"captured variable {repr node} cannot be isolated", node)

template checkIsolation(val: untyped): untyped =
  when compiles(isolate(val)):
    val
  else:
    cannotIsolateError(val)
    val

proc makeEnvTupleConstructor(vars: Table[string, NimNode]): NimNode =
  result = nnkTupleConstr.newNimNode()
  for (name, node) in vars.pairs:
    result.add nnkExprColonExpr.newTree(
      ident(name), newCall(bindSym"checkIsolation", node)
    )

proc getEnvDestructor[T](): proc(p: pointer) {.nimcall, gcsafe, raises: [].} =
  proc(env: pointer) {.nimcall, raises: [].} =
    {.cast(raises: []).}:
      `=destroy`(cast[ptr T](env)[])
      deallocShared(env)

proc isolatedClosureBody(orig: NimNode): NimNode =
  let fn = nnkProcDef.newNimNode()
  orig.copyChildrenTo(fn)
  fn.addPragma ident"nimcall"
  fn.addPragma ident"gcsafe"
  let envSym = genSym(nskParam)
  fn.params.insert(1,
    newIdentDefs(envSym, bindSym("pointer", brClosed))
  )

  let capturedVars = findCapturedVars(orig)
  let envType = makeEnvType(capturedVars)
  replaceCapturedVars(capturedVars, fn, envType, envSym)
  
  let fnName = fn.name
  let env = makeEnvTupleConstructor(capturedVars)

  quote:
    block:
      `fn`
      let envPtr = createShared(`envType`)
      envPtr[] = `env`
      IsolatedClosure[typeof(`fnName`)](
        fn: `fnName`,
        env: envPtr,
        destructor: getEnvDestructor[`envType`]()
      )

macro isolatedClosure*(orig: typed): untyped =
  orig.expectKind {nnkProcTy, nnkProcDef, nnkLambda, nnkDo}
  case orig.kind
  of nnkProcTy:
    result = isolatedClosureType(orig)
  of nnkProcDef, nnkLambda, nnkDo:
    result = isolatedClosureBody(orig)
  else:
    doAssert false

macro call*[T](p: IsolatedClosure[T], args: varargs[untyped]): untyped =
  let
    fn = quote do: `p`.fn
    env = quote do: `p`.env

  result = newCall(fn, env)
  for arg in args:
    result.add arg

{.experimental: "callOperator".}

macro `()`*[T](p: IsolatedClosure[T], args: varargs[untyped]): untyped =
  let
    fn = quote do: `p`.fn
    env = quote do: `p`.env

  result = newCall(fn, env)
  for arg in args:
    result.add arg
