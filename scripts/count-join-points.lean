/-
How many join points does the optimiser find in the corpus?

Every snapshot module is compiled and `LakeJs.Contify.Term.joinCount` is summed over the
declarations the module prints — the terms as the optimiser leaves them, join points of
loop blocks (`Body.joinPointB`) included.

Run it with

    lake env lean scripts/count-join-points.lean
-/
import Lean
import LakeJs.Compile

open Lean

/-- Import one module and run `act` against the environment. -/
def withModule (mod : Name) (act : CoreM α) : IO α := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := true)
  let (res, _) ← act.toIO { fileName := "count-join-points", fileMap := default } { env }
  return res

/-- Every `.lean` file of `dir`, as a module name under `root`. -/
def modulesOfDir (dir : System.FilePath) (root : Name) : IO (Array Name) := do
  let mut out : Array Name := #[]
  for e in ← dir.readDir do
    let f := e.fileName
    if f.endsWith ".lean" then
      out := out.push (root ++ Name.mkSimple (f.dropEnd 5).toString)
  return out.qsort fun a b => a.toString < b.toString

def main : IO Unit := do
  let mut mods := #[]
  for (dir, root) in [("SnapshotsPBOPure", `SnapshotsPBOPure), ("SnapshotsMy", `SnapshotsMy)] do
    mods := mods ++ (← modulesOfDir dir root)
  let mut total := 0
  let mut joins := 0
  let mut withJoins := 0
  for m in mods do
    let res? ←
      try
        pure (some (← withModule m (LakeJs.Compile.compileModule m)))
      catch _ => pure none
    match res? with
    | none => pure ()
    | some res =>
      total := total + res.compiled.size
      let mut here := 0
      for (_, n) in res.joinPoints do
        here := here + n
        withJoins := withJoins + 1
      joins := joins + here
      if here != 0 then IO.println s!"{m}: {here}"
  IO.println s!"declarations compiled: {total}; with a join point: {withJoins}; \
join points in all: {joins}"

#eval main
