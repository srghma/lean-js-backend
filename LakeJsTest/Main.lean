import LakeJs.Compile
import LakeJsTest.JsShape

/-!
# The backend's own test run

Run it with `lake test`.  It compiles, in one go,

* **every** module of `SnapshotsPBOPure` — the whole directory is read at run time, so a
  snapshot added to it is tested without the list below being touched — together with
  the `SnapshotsMy` modules that are pure;
* and checks each generated module against `LakeJsTest.JsShape`: it must be valid
  JavaScript whose only repetition is a `while` or a `for` loop.  There is no
  `function`, no `eval`, no `new`, no `throw` and no self-application `x(x)` in it, so
  nothing in the output is an Omega, a `Y` combinator or any other way of looping that
  is not one of those two statements.  Where `node` is on the path, every module is also
  parsed by it as an ES module.
* A handful of modules additionally have to contain particular text — a `while` loop for
  the ones whose recursion is a tail call, the merged `_mut$…` dispatch loop for a
  mutually tail-recursive group, unboxed instance fields — which the `accepted` table
  below records.
* The modules that are *not* total, or that are effectful, must be refused with a
  message that says why: a `partial def`, or an IO entry point.
-/

open Lean

/-- Import one module and run `act` against the environment. -/
def withModule (mod : Name) (act : CoreM α) : IO α := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := true)
  let (res, _) ← act.toIO { fileName := "LakeJsTest", fileMap := default } { env }
  return res

/-- Does `hay` contain `needle`? -/
def occurs (hay needle : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- What a module is expected to compile to. -/
structure Expectation where
  /-- The module. -/
  mod : Name
  /-- Text the JavaScript must contain, such as `while` for a module whose recursion is
      a tail call. -/
  contains : List String := []
  /-- Text the JavaScript must *not* contain: an instance that stayed boxed, a
      primitive that leaked out as a name. -/
  absent : List String := []

/-- The modules whose output must contain particular text, over and above the checks
    every compiled module gets. -/
def accepted : List Expectation :=
  [ { mod := `SnapshotsPBOPure.Tco01, contains := ["while", "const test ="] }
  , { mod := `SnapshotsPBOPure.Tco03, contains := ["while", "_mut$go"] }
  , { mod := `SnapshotsPBOPure.Tco04, contains := ["while", "_mut$test1"] }
  , { mod := `SnapshotsPBOPure.Tco05, contains := ["while"] }
  , { mod := `SnapshotsPBOPure.Tco06, contains := ["while", "_mut$f"] }
    -- the instance is unboxed to one constant per field, and its single field is the
    -- function itself: no record is built at run time
  , { mod := `SnapshotsPBOPure.CaseJacobs,
      contains := ["renderExpr", "tag === 0", "._1",
                   "const instToStringExpr_toString = renderExpr;"],
      -- data is positional: a numeric tag and `_1 … _n`, with no constructor or field
      -- name anywhere in the output
      absent := ["const instToStringExpr =", "tag: \"", "\"Add\":", "mk"] }
  , { mod := `SnapshotsPBOPure.CaseLeafTco, contains := ["while"] }
  , { mod := `SnapshotsPBOPure.Fusion01 }
  , { mod := `SnapshotsPBOPure.Fusion02 }
  , { mod := `SnapshotsPBOPure.CaptureDerefRegression01,
      contains := ["while", "_mut$testEven"] }
    -- the Lean declaration is called `eval`, which a JavaScript module may not bind
  , { mod := `SnapshotsPBOPure.RecursionSchemes01, contains := ["const eval$ ="] }
  , { mod := `SnapshotsPBOPure.VanLaarhovenTraversals01,
      contains := ["const instReprFun_repr =", "const instDecidableEqFun_decEq ="],
      absent := ["const instReprFun ="] }
    -- externs print as a saturated call of their C name, and a function taking an
    -- unknown instance takes its fields as parameters instead
  , { mod := `SnapshotsMy.HashContainers,
      contains := ["$lean_uint64_of_nat(", "$lean_mk_array(",
                   "const List_forIn__loop__at__test7_spec_0 = (v0, v1, v2, v3, v4)"] }
  , { mod := `SnapshotsMy.MutualTail,
      contains := ["while", "_mut$test1", "_mut$test3",
                   "const test2 = (v0) => _mut$test1(1, v0)"] }
  , { mod := `SnapshotsMy.StringWalk, contains := ["while"] }
    -- a branch Lean proved impossible is dropped, not printed as a `throw`: `small`
    -- and `headOf` are compiled, and the module's own names are all bound
  , { mod := `SnapshotsMy.UnreachBranch,
      contains := ["const small =", "const headOf ="] }
    -- `Nat.gcd` is a well-founded recursion, and its `main` is commented out because an
    -- IO action is not a value the backend may reorder
  , { mod := `SnapshotsMy.GcdEntry, contains := ["const gcd2 =", "const run ="] } ]

/-- The `SnapshotsMy` modules that are pure, and so are compiled and checked.  The rest
    of that directory is IO, which the backend refuses on purpose. -/
def myModules : List Name :=
  [ `SnapshotsMy.HashContainers, `SnapshotsMy.MutualTail, `SnapshotsMy.StringWalk,
    `SnapshotsMy.UnreachBranch, `SnapshotsMy.GcdEntry ]

/-- The modules that must be refused, and a phrase their refusal must mention. -/
def rejected : List (Name × String) :=
  [ (`SnapshotsPBOPartial.RecursiveBindingGroup01, "partial def")
  , (`SnapshotsPBOPure.Html, "partial def")
    -- the translation must keep refusing an effect: a `Term` is a value, and a value
    -- may be reordered, duplicated or dropped, which `IO.println` may not be
  , (`SnapshotsMy.IoEntry, "IO type")
  , (`SnapshotsMy.StdinEntry, "IO type") ]

/-- JavaScript the backend must never print, with the reason each one is out.  The
    shape check has to *bite*: if `JsShape.issues` accepted these, its silence on the
    snapshots would mean nothing. -/
def shapeMustReject : List (String × String) :=
  [ ("the Omega combinator", "const omega = (x) => x(x);\nomega(omega);\n")
  , ("the Y combinator", "const Y = (f) => ((x) => f(x(x)))((x) => f(x(x)));\n")
  , ("a named function that calls itself", "function loop(n) { return loop(n + 1); }\n")
  , ("a `do … while`", "let i = 0;\ndo { i = i + 1; } while (i < 3);\n")
  , ("code built at run time", "const f = new Function(\"return 1\");\n")
  , ("a `throw`", "const f = (x) => { throw x; };\n") ]

/-- JavaScript of exactly the shape the backend does print, which the check must pass. -/
def shapeMustAccept : List (String × String) :=
  [ ("a `while` loop",
     "const f = (n) => { let i = n; while (i > 0) { i = i - 1; } return i; };\n")
  , ("a `for` loop",
     "const f = (n) => { let s = 0; for (let i = 0; i < n; i = i + 1) { s = s + i; } return s; };\n")
  , ("the word `catch` inside a string literal", "const f = () => \"catch\";\n") ]

/-- Every `.lean` file of `dir`, as a module name under `root`. -/
def modulesOfDir (dir : System.FilePath) (root : Name) : IO (Array Name) := do
  let mut out : Array Name := #[]
  for e in ← dir.readDir do
    let f := e.fileName
    if f.endsWith ".lean" then
      out := out.push (root ++ Name.mkSimple (f.dropEnd 5).toString)
  return out.qsort fun a b => a.toString < b.toString

/-- Is `node` on the path? -/
def haveNode : IO Bool :=
  try
    let out ← IO.Process.output { cmd := "node", args := #["--version"] }
    return out.exitCode == 0
  catch _ => return false

/-- Parse `js` with `node` as an ES module, and report what it says if it will not
    parse.  A module is always strict, so this catches a declaration bound to a name
    JavaScript reserves and a name bound twice. -/
def nodeCheck (mod : Name) (js : String) : IO (Option String) := do
  let dir : System.FilePath := ".lake" / "build" / "jscheck"
  IO.FS.createDirAll dir
  let path := dir / (mod.toString ++ ".mjs")
  IO.FS.writeFile path js
  let out ← IO.Process.output { cmd := "node", args := #["--check", path.toString] }
  if out.exitCode == 0 then return none else return some out.stderr.trimAscii.toString

/-- Compile `mod` and check everything that is asked of every compiled module.  Returns
    the messages of whatever failed. -/
def checkModule (useNode : Bool) (e : Expectation) : IO (List String) := do
  let outcome ←
    try
      let res ← withModule e.mod (LakeJs.Compile.compileModule e.mod)
      pure (Except.ok res)
    catch ex => pure (Except.error (toString ex))
  match outcome with
  | .error msg => return [s!"it was refused: {msg}"]
  | .ok res =>
    let mut bad : List String := []
    if res.js.isEmpty then
      bad := bad ++ ["it compiled to nothing"]
    if !res.failures.isEmpty then
      -- a declaration that is not translated is dropped together with everything that
      -- calls it, so a skipped declaration means the module is incomplete
      let why := res.failures.toList.map fun (n, m) => s!"{n}: {m}"
      bad := bad ++ [s!"were not translated: {String.intercalate "; " why}"]
    let missing := e.contains.filter fun s => !occurs res.js s
    if !missing.isEmpty then
      bad := bad ++ [s!"the output does not contain {missing}"]
    -- no primitive may ever leak out of the translation as a bare name, and nothing it
    -- drops may reappear as an `undefined` argument
    let forbidden := (["$prim_", "undefined"] ++ e.absent).filter fun s => occurs res.js s
    if !forbidden.isEmpty then
      bad := bad ++ [s!"the output still contains {forbidden}"]
    bad := bad ++ LakeJsTest.JsShape.issues res.js
    if useNode then
      if let some err ← nodeCheck e.mod res.js then
        bad := bad ++ [s!"node will not parse it: {err}"]
    -- not a failure, but the one place the output still repeats itself with something
    -- other than a loop: a Lean recursion that is not a tail call
    let rec? := LakeJsTest.JsShape.recursiveNames res.js
    if !rec?.isEmpty then
      IO.println s!"note {e.mod}: {rec?} call themselves, the Lean recursion not being a tail call"
    return bad

def main : IO UInt32 := do
  let useNode ← haveNode
  if !useNode then
    IO.println "note: `node` is not on the path, so the output is not parsed by it"
  -- every snapshot of `SnapshotsPBOPure`, plus the pure ones of `SnapshotsMy`
  let pureMods ← modulesOfDir "SnapshotsPBOPure" `SnapshotsPBOPure
  let refused := rejected.map (·.1)
  let sweep := (pureMods.toList ++ myModules).filter fun m => !refused.contains m
  let expectationOf (m : Name) : Expectation :=
    (accepted.find? (·.mod == m)).getD { mod := m }
  let mut failures := 0
  -- first, that the shape check is a check at all
  for (what, js) in shapeMustReject do
    if (LakeJsTest.JsShape.issues js).isEmpty then
      IO.eprintln s!"FAIL the shape check passes {what}, which it must not"
      failures := failures + 1
  for (what, js) in shapeMustAccept do
    let bad := LakeJsTest.JsShape.issues js
    if !bad.isEmpty then
      IO.eprintln s!"FAIL the shape check rejects {what}: {bad}"
      failures := failures + 1
  for m in sweep do
    let bad ← checkModule useNode (expectationOf m)
    if bad.isEmpty then
      IO.println s!"ok   {m}"
    else
      for b in bad do IO.eprintln s!"FAIL {m}: {b}"
      failures := failures + 1
  -- an expectation for a module the sweep does not reach would silently never run
  for e in accepted do
    if !sweep.contains e.mod then
      IO.eprintln s!"FAIL {e.mod}: it is expected to compile, but nothing compiled it"
      failures := failures + 1
  for (mod, phrase) in rejected do
    let outcome ←
      try
        let res ← withModule mod (LakeJs.Compile.compileModule mod)
        pure (Except.ok res.js)
      catch ex => pure (Except.error (toString ex))
    match outcome with
    | .ok _ =>
        IO.eprintln s!"FAIL {mod}: it was compiled, but it is not total"
        failures := failures + 1
    | .error msg =>
        if !occurs msg phrase then
          IO.eprintln s!"FAIL {mod}: refused, but not for the expected reason: {msg}"
          failures := failures + 1
        else
          IO.println s!"ok   {mod}: refused ({phrase})"
  if failures == 0 then
    IO.println s!"all tests passed ({sweep.length} modules compiled, {rejected.length} refused)"
    return 0
  else
    IO.eprintln s!"{failures} test(s) failed"
    return 1
