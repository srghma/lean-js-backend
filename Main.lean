import LakeJs.FrontEnd

/-!
# The command line of the backend

```
lake build lean-to-js-backend SnapshotsMy.Tco08
lake env ./.lake/build/bin/lean-to-js-backend SnapshotsMy/Tco08.lean
#   SnapshotsMy/Tco08.lean -> SnapshotsMy/Tco08Program.lean (2 declarations, checked)
```

The driver reads the **compiled module**, not the `.lean` source: the path on the command
line only names the module, which therefore has to be built first (`lake build
SnapshotsMy.Tco08`).  For each declaration of the module it

* asks `LakeJs.Totality` whether the backend may compile it at all — a `partial def`, an
  `unsafe def`, an `IO` function and a partial fixpoint are refused there;
* translates the `saveBase` LCNF body into a term of the one grammar of `LakeJs.Expr`
  (`LakeJs.FrontEnd`), in which the only recursion is `Term.fix` and it carries its rank;
* and writes `<Module>Program.lean` beside the module: a Lean file whose header comment is
  the `Term` tree of every declaration, 🎯 for a public entry point and 📦 for one the
  translation pulled in, followed by the same program as Lean source — a `Sig`, one `Term`
  per declaration and the `Program` telescope.

Before writing the file the driver **elaborates it** against `import LakeJs`.  That is the guarantee the output carries: the tree in the file is a term of the
grammar, so it is terminating by construction, and its rank is the one the translation
read off Lean's own termination proof.

```
--check     report the verdict, write nothing
--stdout    print the program instead of writing it
--no-check  skip the elaboration of the generated Lean source (faster, unchecked)
--no-auto-check
            do not write `<Module>AutoCheck.lean`, the differential checks of every
            declaration whose arguments and result the generator can sample
--no-descends
            do not write `<Module>Descends.lean`, the verification condition of every
            recursion of the module
--out=FILE  write somewhere else
```

There is no JavaScript emitter in this tree: the driver produces the `Term` program and
stops there.
-/

open Lean

/-- The module name a path denotes: `SnapshotsMy/Tco08.lean` is `SnapshotsMy.Tco08`. -/
def moduleOfPath (p : String) : Name :=
  let p := if p.endsWith ".lean" then (p.dropEnd 5).toString else p
  let parts := (p.splitOn "/").flatMap (·.splitOn "\\") |>.filter (· ≠ "")
  parts.foldl (fun n s => n ++ Name.mkSimple s) Name.anonymous

/-- Import `mod` and run `act` against the resulting environment. -/
def withModule (mod : Name) (act : MetaM α) : IO α := do
  -- `LakeJs.CoreModels` holds the Lean bodies of the core functions Lean implements in
  -- C, which the front end compiles instead of the primitive
  let env ← importModules #[{ module := mod }, { module := `LakeJs.CoreModels }] {}
    (trustLevel := 1024) (loadExts := true)
  let (res, _) ← (act.run' {}).toIO
    { fileName := "lean-to-js-backend", fileMap := default } { env }
  return res

/-- Elaborate the generated program, so that what is written out is known to be a term of
    the grammar.  Returns the error messages, if any. -/
def checkLeanSource (mod : Name) (src : String) : IO (Array String) := do
  match ← Lean.Elab.runFrontend src {} s!"{mod}Program.lean" `ProgramCheck with
  | some _ => return #[]
  | none => return #["the generated program does not elaborate (see the errors above)"]

def usage : String :=
  "usage: lean-to-js-backend [--check|--stdout|--no-check] [--out=<file>] \
<path/to/Module.lean>"

def main (args : List String) : IO UInt32 := do
  let flags := args.filter (·.startsWith "--")
  let paths := args.filter (fun a => !a.startsWith "--")
  if paths.isEmpty then
    IO.eprintln usage
    return 1
  let checkOnly := flags.contains "--check"
  let toStdout := flags.contains "--stdout"
  let noCheck := flags.contains "--no-check"
  let noAutoCheck := flags.contains "--no-auto-check"
  let noDescends := flags.contains "--no-descends"
  let outPath? := flags.findSome? fun f =>
    if f.startsWith "--out=" then some (f.drop 6).toString else none
  Lean.initSearchPath (← Lean.findSysroot)
  let mut bad : Nat := 0
  for path in paths do
    let mod := moduleOfPath path
    let outcome ←
      try
        pure (Except.ok (← withModule mod (LakeJs.FrontEnd.translateModule mod)))
      catch e => pure (Except.error (toString e))
    match outcome with
    | .error msg =>
        IO.eprintln s!"{path}: refused: {msg}"
        bad := bad + 1
    | .ok res =>
        for r in res.rejections do
          IO.eprintln s!"{path}: refused by the totality gate: {r.message}"
        for (n, why) in res.outside do
          IO.eprintln s!"{path}: note: `{n}` is outside the language: {why}"
        for (n, why) in res.failures do
          IO.eprintln s!"{path}: note: `{n}` was not translated: {why}"
        let checkMsgs ←
          if noCheck || res.decls.isEmpty then pure #[]
          else checkLeanSource mod res.text
        for m in checkMsgs do
          IO.eprintln s!"{path}: {m}"
        if !checkMsgs.isEmpty then
          bad := bad + 1
        else if toStdout then
          IO.print res.text
        else if checkOnly then
          IO.println s!"{path}: ok ({res.decls.size} declarations)"
        else
          let stem := (if path.endsWith ".lean" then (path.dropEnd 5).toString else path)
          let out := outPath?.getD (stem ++ "Program.lean")
          IO.FS.writeFile out res.text
          let checked := if noCheck then "unchecked" else "checked"
          IO.println s!"{path} -> {out} ({res.decls.size} declarations, {checked})"
          -- the differential checks of the declarations the generator can sample: a
          -- separate file, because it imports the module as well as the program and so
          -- can only be elaborated once both are built
          if !noAutoCheck && !res.autoCheck.isEmpty && outPath?.isNone then
            let checkOut := stem ++ "AutoCheck.lean"
            IO.FS.writeFile checkOut res.autoCheck
            IO.println s!"{path} -> {checkOut} (differential checks)"
          -- the verification condition of every recursion of the module, proved by
          -- `descent_auto`: a separate file for the same reason, and the one that makes
          -- a measure the front end read wrongly a compile error rather than a wrong
          -- answer at run time
          if !noDescends && !res.descends.isEmpty && outPath?.isNone then
            let descOut := stem ++ "Descends.lean"
            IO.FS.writeFile descOut res.descends
            IO.println s!"{path} -> {descOut} (verification conditions)"
        if !res.failures.isEmpty then
          bad := bad + 1
  return (if bad == 0 then 0 else 1)
