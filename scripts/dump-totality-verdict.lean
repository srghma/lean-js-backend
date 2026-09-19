/-
Print the verdict of `LakeJs.Totality.check` — the front end's safety / IO / recursion-kind
gate — for the named declarations of a module, reading nothing but that module's `.olean`.

    lake env lean --run scripts/dump-totality-verdict.lean <Module.Name> <Decl.Name> ...

With no declaration names, every non-internal declaration of the module is reported.  The
module has to have been built first (`lake build <Module.Name>`): the gate reads the
compiled artefacts, never the `.lean` source.
-/
import Lean
import LakeJs.Totality

open Lean

def report (mod : Name) (decls : List Name) : CoreM Unit := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? mod
    | IO.println s!"{mod}: not imported"
  let decls :=
    if decls.isEmpty then
      env.constants.map₁.toList.filterMap fun (n, _) =>
        if env.getModuleIdxFor? n == some modIdx && !n.isInternal then some n else none
    else decls
  for n in decls do
    let rejections ← LakeJs.Totality.check #[modIdx.toNat] #[n]
    if rejections.isEmpty then
      IO.println s!"{n}: accepted ({repr (LakeJs.Totality.recKind? env n)})"
    else
      for r in rejections do
        IO.println s!"{n}: refused: {r.message}"

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "usage: dump-totality-verdict.lean <Module.Name> [<Decl.Name> ...]"
  | modStr :: declStrs => do
    Lean.initSearchPath (← Lean.findSysroot)
    let mod := modStr.toName
    let env ← importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := true)
    let (_, _) ← (report mod (declStrs.map String.toName)).toIO
      { fileName := "dump-totality-verdict", fileMap := default } { env }
    pure ()
