import LakeJs.Compile
import LakeJs.Program
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
  the ones whose recursion is a tail call, the specialised `_spec$…` loop of a mutually
  tail-recursive group whose jumps name their target (and the merged `_mut$…` dispatch
  loop of one whose jumps do not), unboxed instance fields — which the `accepted` table
  below records.
* The modules that are *not* total, or that are effectful, must be refused with a
  message that says why: a `partial def`, or an IO entry point.
* The *configuration* is checked by the convention the snapshot names follow, so that
  no module has to be listed twice.  `XxxConfigurable` is compiled at both presets: the
  two outputs must differ, the one of `--config=pbo` must import only `…_num.mjs`
  preludes and mention no `BigInt`, the one of `--config=faithful` must import only
  `…_bigint.mjs` preludes, and each must be the file beside the source
  (`XxxConfigurable-num.js`, `XxxConfigurable-bigint.js`).  `XxxNonConfigurable` is
  compiled at both presets too, but there the two outputs must be *identical*, must be
  `XxxNonConfigurable.js`, and may import no prelude other than
  `runtime/lean_runtime_non_configurable.mjs`.
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
  /-- Must no loop of this module build an object?  That is the property a scalarised
      accumulator has: its fields go round the loop as scalars. -/
  noAllocInLoop : Bool := false

/-- The modules whose output must contain particular text, over and above the checks
    every compiled module gets. -/
def accepted : List Expectation :=
    -- the loop leaves with a `return`, and the predecessor of a `Nat` the branch has
    -- just shown is not zero cannot truncate, so it is `n - 1` and not `Math.max(0, …)`
  [ { mod := `SnapshotsPBOPure.Tco01, contains := ["while", "const test =", "v1 - 1"],
      absent := ["Math.max"] }
  , { mod := `SnapshotsPBOPure.Tco03, contains := ["while", "_mut$go", "v3 - 1"] }
    -- a two-member cycle whose jumps name their target: the tag is a compile-time
    -- value, so the dispatch is gone and the loop is `_spec$…`, not `_mut$…`
  , { mod := `SnapshotsPBOPure.Tco04, contains := ["while", "_spec$test1"],
      absent := ["_mut$"] }
  , { mod := `SnapshotsPBOPure.Tco05, contains := ["while"] }
  , { mod := `SnapshotsPBOPure.Tco06, contains := ["while", "_spec$f"],
      absent := ["_mut$"] }
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
      contains := ["while", "_spec$testEven", "v2 - 1"],
      -- the guarded predecessor is exact, a slot whose new value needs no old one is
      -- assigned directly rather than through a temporary, and the tag of the cycle is
      -- specialised away, so there is no dispatch loop and no tag test
      absent := ["Math.max", "t$3$", "_mut$"],
      -- the `Box2` accumulator travels round the loop as its two fields, so the object
      -- is built only where the loop answers
      noAllocInLoop := true }
    -- the Lean declaration is called `eval`, which a JavaScript module may not bind
  , { mod := `SnapshotsPBOPure.RecursionSchemes01, contains := ["const eval$ ="] }
    -- the two arms of `Repr`'s precedence test share one join point, which is bound as a
    -- local function and called rather than duplicated into both arms
  , { mod := `SnapshotsPBOPure.VanLaarhovenTraversals01,
      contains := ["const instReprFun_repr =", "const instDecidableEqFun_decEq =",
                   "return v4(1);", "return v4(2);"],
      absent := ["const instReprFun ="] }
    -- externs print as a saturated call of their C name, and a function taking an
    -- unknown instance takes its fields as parameters instead
  , { mod := `SnapshotsMy.HashContainers,
      contains := ["$lean_uint64_of_nat(", "$lean_mk_array(",
                   "const List_forIn__loop__at__test7_spec_0 = (v0, v1, v2, v3, v4)"] }
    -- both groups are single cycles — a two-member one and a three-member one of
    -- differing arities — so both are specialised: one loop each, entered by the members
    -- that do not own it
  , { mod := `SnapshotsMy.MutualTail,
      contains := ["while", "_spec$test1", "_spec$test3",
                   "export const test1 = _spec$test1;",
                   "return _spec$test1(v1);"],
      absent := ["Math.max", "_mut$"] }
    -- a group whose members disagree on the type of a parameter gets a slot for each
    -- type rather than one slot widened to `Ty.typeParam`: `walkStr` holds its `String`
    -- in a slot of its own, and the slot a member does not use is filled with the empty
    -- value of *that slot’s* type rather than with a `0`
  , { mod := `SnapshotsMy.MutualSlots,
      contains := ["while", "_spec$walkNat", "_spec$walkNat(v0, v1, \"\")"],
      absent := ["_mut$", "_spec$walkNat(v0, v1, 0)"] }
    -- the `(Nat × String)` the loop carries travels as its two fields as well
  , { mod := `SnapshotsMy.StringWalk, contains := ["while"], noAllocInLoop := true }
    -- a branch Lean proved impossible is dropped, not printed as a `throw`: `small`
    -- and `headOf` are compiled, and the module's own names are all bound
  , { mod := `SnapshotsMy.UnreachBranch,
      contains := ["const small =", "const headOf ="] }
    -- `Nat.gcd` is a well-founded recursion, and its `main` is commented out because an
    -- IO action is not a value the backend may reorder
  , { mod := `SnapshotsMy.GcdEntry, contains := ["const gcd2 =", "const run ="] }
    -- a call of an `@[inline]` declaration, and of a small one Lean said nothing about,
    -- is the body of that declaration; `@[noinline]` is a prohibition the backend keeps,
    -- and a declaration every call site copied and nothing exports is not bound at all
  , { mod := `SnapshotsMy.InlineDemo,
      contains := ["const bar = 3;", "const v1 = v0 * 2;", "triple(v0)"],
      absent := ["scale(", "const scale"] }
    -- a `Nat` division whose answer Lean itself computed: the name of the declaration
    -- says what the answer has to be, and it is bound whatever the configuration is
  , { mod := `SnapshotsPBOPure.PrimOpIntDivConfigurable,
      contains := ["TestNat_test1_0_shouldBeTrue"] } ]

/-- The presets a snapshot is compiled at, with the suffix each one writes its output
    under: `--config=pbo` writes `<Module>-num.js`, `--config=faithful` writes
    `<Module>-bigint.js`.  Nothing below names a module: which snapshot is compiled at
    which configuration is read off the *name* of the module, so a snapshot added to
    `SnapshotsPBOPure` is checked without this file being touched. -/
def presets : List (String × String × LakeJs.Config.JsConfig) :=
  [ ("pbo", "-num", .presetPBO), ("faithful", "-bigint", .presetFaithful) ]

/-- The path of the source of a module, without its extension:
    `SnapshotsPBOPure.Tco01` is `SnapshotsPBOPure/Tco01`. -/
def pathOfModule (mod : Name) : String :=
  String.intercalate "/" (mod.components.map toString)

/-- Is this a module no knob can change?  By convention it is called
    `XxxNonConfigurable`, and it compiles to the single output
    `XxxNonConfigurable.js`. -/
def isNonConfigurableName (mod : Name) : Bool := (toString mod).endsWith "NonConfigurable"

/-- Is this a module the knobs *do* change?  By convention it is called
    `XxxConfigurable`, and it compiles to `XxxConfigurable-num.js` and
    `XxxConfigurable-bigint.js`. -/
def isConfigurableName (mod : Name) : Bool :=
  (toString mod).endsWith "Configurable" && !isNonConfigurableName mod

/-- Compile `mod` at `cfg`, reporting a refusal as an error rather than an exception. -/
def compileAt (mod : Name) (cfg : LakeJs.Config.JsConfig) : IO (Except String String) := do
  try
    let res ← withModule mod (LakeJs.Compile.compileModule mod (cfg := cfg))
    return .ok res.js
  catch ex => return .error (toString ex)

/-- The generated file beside the source, if it is there. -/
def readOutput? (path : String) : IO (Option String) := do
  if ← System.FilePath.pathExists path then
    return some (← IO.FS.readFile path)
  else
    return none

/-- The specifiers a generated module imports from, in order. -/
def importsOf (js : String) : List String :=
  ((js.splitOn "from \"").drop 1).filterMap fun s =>
    match s.splitOn "\"" with
    | spec :: _ => some spec
    | [] => none

/-- A module whose types the knobs change: the two presets must print *different*
    modules, each importing only preludes of its own representation, and each equal to
    the file that sits beside the source. -/
def checkConfigurable (mod : Name) : IO (List String) := do
  let path := pathOfModule mod
  let mut bad : List String := []
  let mut outs : List String := []
  for (name, suffix, cfg) in presets do
    match ← compileAt mod cfg with
    | .error msg => bad := bad ++ [s!"[{name}] it was refused: {msg}"]
    | .ok js =>
        outs := outs ++ [js]
        let out := path ++ suffix ++ ".js"
        match ← readOutput? out with
        | none => bad := bad ++ [s!"[{name}] there is no `{out}` beside the source"]
        | some disk =>
            if disk != js then
              bad := bad ++ [s!"[{name}] `{out}` is not what the compiler prints now"]
  match outs with
  | [numJs, bigJs] =>
      if numJs == bigJs then
        bad := bad ++ ["the two presets print the same module, so no type of it is \
          configurable and its name says otherwise"]
      let imports (js : String) (needle : String) :=
        (importsOf js).filter fun s => occurs s needle
      if !(imports numJs "_bigint.mjs").isEmpty then
        bad := bad ++ [s!"[pbo] it imports {imports numJs "_bigint.mjs"}"]
      if (imports numJs "_num.mjs").isEmpty then
        bad := bad ++ ["[pbo] it imports no prelude of the number representation"]
      if occurs numJs "BigInt" then
        bad := bad ++ ["[pbo] it mentions a `BigInt`"]
      if !(imports bigJs "_num.mjs").isEmpty then
        bad := bad ++ [s!"[faithful] it imports {imports bigJs "_num.mjs"}"]
      if (imports bigJs "_bigint.mjs").isEmpty then
        bad := bad ++ ["[faithful] it imports no prelude of the `BigInt` representation"]
  | _ => pure ()
  return bad

/-- A module no knob can change: the two presets must print the *same* module, which is
    the file beside the source, and the only prelude it may import is the
    non-configurable one. -/
def checkNonConfigurable (mod : Name) : IO (List String) := do
  let path := pathOfModule mod
  let mut bad : List String := []
  let mut outs : List String := []
  for (name, _, cfg) in presets do
    match ← compileAt mod cfg with
    | .error msg => bad := bad ++ [s!"[{name}] it was refused: {msg}"]
    | .ok js => outs := outs ++ [js]
  match outs with
  | [numJs, bigJs] =>
      if numJs != bigJs then
        bad := bad ++ ["the two presets print different modules, but no type of it is \
          configurable"]
      let configured := (importsOf numJs).filter fun s =>
        occurs s "lean_runtime_" && !occurs s "lean_runtime_non_configurable.mjs"
      if !configured.isEmpty then
        bad := bad ++ [s!"it imports the configured prelude(s) {configured}"]
      if occurs numJs "BigInt" then
        bad := bad ++ ["it mentions a `BigInt`"]
      let out := path ++ ".js"
      match ← readOutput? out with
      | none => bad := bad ++ [s!"there is no `{out}` beside the source"]
      | some disk =>
          if disk != numJs then
            bad := bad ++ [s!"`{out}` is not what the compiler prints now"]
  | _ => pure ()
  return bad

/-- The `SnapshotsMy` modules that are pure, and so are compiled and checked.  The rest
    of that directory is IO, which the backend refuses on purpose. -/
def myModules : List Name :=
  [ `SnapshotsMy.HashContainers, `SnapshotsMy.MutualTail, `SnapshotsMy.MutualSlots,
    `SnapshotsMy.StringWalk, `SnapshotsMy.UnreachBranch, `SnapshotsMy.GcdEntry,
    `SnapshotsMy.InlineDemo ]

/-- The modules that must be refused, and a phrase their refusal must mention. -/
def rejected : List (Name × String) :=
  [ (`SnapshotsPBOPartial.RecursiveBindingGroup01, "partial def")
  , (`SnapshotsPBOPure.Html, "partial def")
    -- `deriving Repr` writes a `partial def` beside the type, so the *module* is out;
    -- the program of one of its declarations is not (`checkDeclProgram` below)
  , (`SnapshotsMy.Html, "partial def")
    -- the translation must keep refusing an effect: a `Term` is a value, and a value
    -- may be reordered, duplicated or dropped, which `IO.println` may not be
  , (`SnapshotsMy.IoEntry, "IO type")
  , (`SnapshotsMy.StdinEntry, "IO type")
    -- a type with no constructors has no values, so it has no runtime representation:
    -- `Ty.enum` carries the proof that its constructor count is positive
  , (`SnapshotsMy.EmptyEntry, "no constructors") ]

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

/-- A loop the backend must never print: one that is driven by an exit flag and hands
    its answer back through a result variable, where a `return` would do. -/
def exitMustReject : List (String × String) :=
  [ ("a loop driven by an exit flag",
     "const f = (n) => { let i = n, c = true, r; while (c) { if (i === 0) { c = false; r = i; } else { i = i - 1; } } return r; };\n") ]

/-- A loop of exactly the shape the backend does print. -/
def exitMustAccept : List (String × String) :=
  [ ("a loop left with a `return`",
     "const f = (n) => { let i = n; while (true) { if (i === 0) { return i; } i = i - 1; } };\n") ]

/-- A loop that allocates once per iteration, which the allocation check must catch,
    and one that allocates only where it answers, which it must not. -/
def allocMustReject : List (String × String) :=
  [ ("an object rebuilt every iteration",
     "const f = (n, a) => { let i = n, b = a; while (true) { if (i === 0) { return b; } b = { tag: 0, _1: b._1 + 1 }; i = i - 1; } };\n") ]

/-- A loop whose accumulator has been scalarised: the object is built at the answer. -/
def allocMustAccept : List (String × String) :=
  [ ("an object built only where the loop answers",
     "const f = (n, a) => { let i = n, b = a._1; while (true) { if (i === 0) { return { tag: 0, _1: b }; } b = b + 1; i = i - 1; } };\n") ]

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

/-- The names a module of the runtime prelude exports: the `export const <name> =`
    lines of it. -/
def exportedNames (src : String) : List String :=
  (("\n" ++ src).splitOn "\nexport const ").drop 1 |>.filterMap fun s =>
    let n := (s.takeWhile fun c => c != ' ' && c != '=' && c != '\n').toString
    if n.isEmpty then none else some n

/-- The runtime prelude is split by knob, and the split must be exactly what
    `LakeJs.Config` says it is: every configurable group has a module per
    representation, that module exports every name the group claims, and it exports
    nothing else — a runtime function whose answer a knob decides but that sits in the
    part no knob changes would be read at the wrong representation, and one that is in
    no file at all is a `SyntaxError` at load time. -/
def checkRuntimeSplit : IO (List String) := do
  let mut bad : List String := []
  for g in LakeJs.Config.RuntimeGroup.all do
    match g.knob? with
    | none => pure ()
    | some knob =>
      for repr in ["num", "bigint"] do
        let path := s!"runtime/lean_runtime_{knob}_{repr}.mjs"
        if !(← System.FilePath.pathExists path) then
          bad := bad ++ [s!"there is no {path}"]
        else
          let exported := exportedNames (← IO.FS.readFile path)
          for n in g.names do
            if !exported.contains n then
              bad := bad ++ [s!"{path} does not export {n}"]
          for n in exported do
            if !g.names.contains n then
              bad := bad ++ [s!"{path} exports {n}, which the group does not claim"]
  return bad

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
    -- no compiled declaration may hold a `let` its body never reads: such a binding
    -- prints as a `const` nobody uses.  `LakeJs.Simp` removes them, and this is the
    -- check that it did.
    if !res.deadLets.isEmpty then
      bad := bad ++ [s!"these declarations still bind a value nothing reads: {res.deadLets}"]
    bad := bad ++ LakeJsTest.JsShape.issues res.js
    -- a loop is left with a `return`, never with an exit flag and a result variable
    bad := bad ++ LakeJsTest.JsShape.flagLoopIssues res.js
    if e.noAllocInLoop then
      bad := bad ++ LakeJsTest.JsShape.allocInLoopIssues res.js
    if useNode then
      if let some err ← nodeCheck e.mod res.js then
        bad := bad ++ [s!"node will not parse it: {err}"]
    -- not a failure, but the one place the output still repeats itself with something
    -- other than a loop: a Lean recursion that is not a tail call
    let rec? := LakeJsTest.JsShape.recursiveNames res.js
    if !rec?.isEmpty then
      IO.println s!"note {e.mod}: {rec?} call themselves, the Lean recursion not being a tail call"
    -- an ignored *parameter* is reported rather than refused: it belongs to the type of
    -- the function, hence to its calling convention, so it cannot be dropped
    for (nm, ps) in res.unusedParams do
      IO.println s!"note {e.mod}: `{nm}` never reads its parameter(s) {ps}"
    return bad

/-- The program of a single declaration: what `#lean_to_lean_term` prints.

    `SnapshotsMy.Html` is a module the backend refuses — `deriving Repr` writes a
    `partial def` beside the type — so it is exactly the case the declaration-rooted
    compiler is for: `test` itself calls nothing partial, and its closure compiles.  The
    closure is followed across modules and stops at the functions the runtime
    implements, and a root with no body to read is refused. -/
def checkDeclProgram : IO (List String) := do
  let mut bad : List String := []
  let run (act : CoreM String) : IO (Except String String) := do
    try
      pure (Except.ok (← withModule `SnapshotsMy.Html act))
    catch ex => pure (Except.error (toString ex))
  match ← run (LakeJs.Program.programOf `test) with
  | .error msg => bad := bad ++ [s!"the program of `test` was refused: {msg}"]
  | .ok text =>
      -- the type of the recursive `inductive` it builds, the primitive the runtime
      -- implements, the helpers it calls and the root itself
      for needle in ["recTaggedUnion", "HtmlM", "7 declarations",
                     "(extern lean_array_push)", "-- from `mkElem`",
                     "\ntest : (fn [string]"] do
        unless occurs text needle do
          bad := bad ++ [s!"the program of `test` does not mention `{needle}`"]
      -- a name the runtime implements is *not* a declaration of the program
      if occurs text "-- from `Array.push`" then
        bad := bad ++ ["the program of `test` translated `Array.push`, which is a \
          primitive of the runtime"]
  -- the same closure, emitted: one module, exporting the root
  match ← run (LakeJs.Program.javascriptOf `test) with
  | .error msg => bad := bad ++ [s!"the JavaScript of `test` was refused: {msg}"]
  | .ok js =>
      unless occurs js "export const test" do
        bad := bad ++ ["the JavaScript of `test` does not export it"]
      let issues := LakeJsTest.JsShape.issues js
      unless issues.isEmpty do
        bad := bad ++ [s!"the JavaScript of `test` is not of the shape the backend \
          promises: {issues}"]
  -- a root the backend has no body for is refused rather than printed empty
  match ← run (LakeJs.Program.programOf `Nat.add) with
  | .ok _ => bad := bad ++ ["the program of `Nat.add` was printed, but it is a \
      primitive of the runtime"]
  | .error msg =>
      unless occurs msg "no body the backend can read" do
        bad := bad ++ [s!"the program of `Nat.add` was refused for the wrong reason: {msg}"]
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
  for (what, js) in exitMustReject do
    if (LakeJsTest.JsShape.flagLoopIssues js).isEmpty then
      IO.eprintln s!"FAIL the loop-exit check passes {what}, which it must not"
      failures := failures + 1
  for (what, js) in exitMustAccept do
    let bad := LakeJsTest.JsShape.flagLoopIssues js
    if !bad.isEmpty then
      IO.eprintln s!"FAIL the loop-exit check rejects {what}: {bad}"
      failures := failures + 1
  for (what, js) in allocMustReject do
    if (LakeJsTest.JsShape.allocInLoopIssues js).isEmpty then
      IO.eprintln s!"FAIL the allocation check passes {what}, which it must not"
      failures := failures + 1
  for (what, js) in allocMustAccept do
    let bad := LakeJsTest.JsShape.allocInLoopIssues js
    if !bad.isEmpty then
      IO.eprintln s!"FAIL the allocation check rejects {what}: {bad}"
      failures := failures + 1
  -- the split of the runtime prelude is the one `LakeJs.Config` describes
  let splitBad ← checkRuntimeSplit
  if splitBad.isEmpty then
    IO.println "ok   the runtime prelude is split exactly as the configuration says"
  else
    for b in splitBad do IO.eprintln s!"FAIL the runtime split: {b}"
    failures := failures + 1
  -- the program of one declaration, followed across modules
  let declBad ← checkDeclProgram
  if declBad.isEmpty then
    IO.println "ok   the program of a single declaration (`#lean_to_lean_term test`)"
  else
    for b in declBad do IO.eprintln s!"FAIL the program of a declaration: {b}"
    failures := failures + 1
  -- a configuration that mixes the two representations has no prelude, and is refused
  let mixed : LakeJs.Config.JsConfig := { natRepr := .num, intRepr := .bigint }
  let mixedOutcome ←
    try
      let _ ← withModule `SnapshotsPBOPure.PrimOpIntDivConfigurable
        (LakeJs.Compile.compileModule `SnapshotsPBOPure.PrimOpIntDivConfigurable
          (cfg := mixed))
      pure (Except.ok ())
    catch ex => pure (Except.error (toString ex))
  match mixedOutcome with
  | .ok _ =>
      IO.eprintln "FAIL a configuration mixing numbers and `BigInt`s was compiled, \
        but there is no prelude for it"
      failures := failures + 1
  | .error msg =>
      if !occurs msg "mixes" then
        IO.eprintln s!"FAIL a mixed configuration was refused, but not for the expected \
          reason: {msg}"
        failures := failures + 1
      else
        IO.println "ok   a configuration mixing numbers and `BigInt`s is refused"
  -- the configured outputs, picked out by the convention their names follow
  let cfgMods := pureMods.toList.filter isConfigurableName
  let nonCfgMods := pureMods.toList.filter isNonConfigurableName
  if cfgMods.isEmpty || nonCfgMods.isEmpty then
    IO.eprintln "FAIL there is no `XxxConfigurable`/`XxxNonConfigurable` snapshot, so \
      the configuration is not exercised at all"
    failures := failures + 1
  for m in cfgMods do
    let bad ← checkConfigurable m
    if bad.isEmpty then
      IO.println s!"ok   {m} [-num.js, -bigint.js]"
    else
      for b in bad do IO.eprintln s!"FAIL {m}: {b}"
      failures := failures + 1
  for m in nonCfgMods do
    let bad ← checkNonConfigurable m
    if bad.isEmpty then
      IO.println s!"ok   {m} [.js, the same at either preset]"
    else
      for b in bad do IO.eprintln s!"FAIL {m}: {b}"
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
