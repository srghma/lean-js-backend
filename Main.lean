import LakeJs.Compile

/-!
# The command line of the backend

```
lake build lean-to-js-backend
lake env ./.lake/build/bin/lean-to-js-backend SnapshotsPBOPure/Tco01.lean
#   SnapshotsPBOPure/Tco01.lean -> SnapshotsPBOPure/Tco01.js

lake env ./.lake/build/bin/lean-to-js-backend --check  SnapshotsMy/IoEntry.lean
lake env ./.lake/build/bin/lean-to-js-backend --stdout SnapshotsPBOPure/Tco01.lean
```

`--check` only reports the verdict, `--stdout` prints the module instead of writing it,
and the default writes `<path>.js` beside the source, overwriting it, together with
`<path>-Expr.txt`: the terms of the module as the translation produced them, before the
optimiser ran.  `--no-expr` leaves that second file alone.

`--config=<preset>` picks the representation of the numeric types: `pbo` (the default)
represents every configurable type as a JavaScript number, `faithful` represents it as a
`BigInt`.  A configuration given on the command line also names the file, so that the two
renderings of one module can sit beside each other: `--config=pbo` writes
`<path>-num.js` and `--config=faithful` writes `<path>-bigint.js`.  `--out=<file>` writes
somewhere else again.
-/

open Lean

/-- The module name a path denotes: `SnapshotsPBOPure/Tco01.lean` is
    `SnapshotsPBOPure.Tco01`. -/
def moduleOfPath (p : String) : Name :=
  let p := if p.endsWith ".lean" then (p.dropEnd 5).toString else p
  let parts := (p.splitOn "/").flatMap (·.splitOn "\\") |>.filter (· ≠ "")
  parts.foldl (fun n s => n ++ Name.mkSimple s) Name.anonymous

/-- How deep below the package root the output sits, i.e. how many `../` steps the
    import of the runtime prelude needs. -/
def depthOfPath (p : String) : Nat :=
  ((p.splitOn "/").flatMap (·.splitOn "\\") |>.filter (· ≠ "")).length - 1

/-- Import `mod` and run `act` against the resulting environment. -/
def withModule (mod : Name) (act : CoreM α) : IO α := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := true)
  let (res, _) ← act.toIO { fileName := "lean-to-js-backend", fileMap := default } { env }
  return res

def usage : String :=
  "usage: lean-to-js-backend [--check|--stdout|--no-expr] [--config=pbo|faithful] \
[--out=<file.js>] <path/to/Module.lean>"

/-- The value of `--<key>=<value>`, if the flags carry one. -/
def flagValue? (flags : List String) (key : String) : Option String :=
  flags.findSome? fun f =>
    if f.startsWith ("--" ++ key ++ "=") then some (f.drop (key.length + 3)).toString
    else none

/-- The name of the output of a configuration: an explicit preset names the file, so
    that the two renderings of one module can sit beside each other. -/
def outSuffix : Option String → String
  | some "pbo" => "-num"
  | some "faithful" => "-bigint"
  | _ => ""

def main (args : List String) : IO UInt32 := do
  let flags := args.filter (·.startsWith "--")
  let paths := args.filter (fun a => !a.startsWith "--")
  if paths.isEmpty then
    IO.eprintln usage
    return 1
  let check := flags.contains "--check"
  let toStdout := flags.contains "--stdout"
  let noExpr := flags.contains "--no-expr"
  let presetName? := flagValue? flags "config"
  let cfg ←
    match presetName? with
    | none => pure LakeJs.Config.JsConfig.presetPBO
    | some name =>
        match LakeJs.Config.JsConfig.ofPresetName? name with
        | some c => pure c
        | none => do
            IO.eprintln s!"unknown configuration `{name}`: use `pbo` or `faithful`"
            return 1
  let outPath? := flagValue? flags "out"
  let mut bad := 0
  for path in paths do
    let mod := moduleOfPath path
    let outcome ←
      try
        let res ← withModule mod
          (LakeJs.Compile.compileModule mod (preludeDepth := depthOfPath path) (cfg := cfg))
        pure (Except.ok res)
      catch e => pure (Except.error (toString e))
    match outcome with
    | .error msg =>
        IO.eprintln s!"{path}: refused: {msg}"
        bad := bad + 1
    | .ok res =>
        for (n, why) in res.failures do
          IO.eprintln s!"{path}: note: `{n}` was not translated: {why}"
        if toStdout then
          IO.print res.js
        else if check then
          IO.println s!"{path}: ok ({res.compiled.size} declarations)"
        else
          let base :=
            (if path.endsWith ".lean" then (path.dropEnd 5).toString else path)
              ++ outSuffix presetName?
          let base := match outPath? with
            | some o => if o.endsWith ".js" then (o.dropEnd 3).toString else o
            | none => base
          let out := base ++ ".js"
          IO.FS.writeFile out res.js
          if noExpr then
            IO.println s!"{path} -> {out}"
          else
            let exprOut := base ++ "-Expr.txt"
            IO.FS.writeFile exprOut res.exprs
            IO.println s!"{path} -> {out}, {exprOut}"
  return (if bad == 0 then 0 else 1)
