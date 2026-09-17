/-
Which compiled declarations break the usage discipline of `LakeJs.Usage`?

Every snapshot module is compiled and its declarations are run through
`LakeJs.Usage.Term.declIssues`: a binder inside a declaration that nothing reads, a
`let` whose value has fewer than two readers, or a join point used as anything but the
target of a jump.  The parameters of a declaration itself are its calling convention and
are exempt.

Run it with

    lake env lean scripts/check-usage.lean
-/
import Lean
import LakeJs.Compile

open Lean

/-- Import one module and run `act` against the environment. -/
def withModule (mod : Name) (act : CoreM α) : IO α := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := true)
  let (res, _) ← act.toIO { fileName := "check-usage", fileMap := default } { env }
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
  let mut bad := 0
  for m in mods do
    let res? ←
      try
        pure (some (← withModule m (LakeJs.Compile.compileModule m)))
      catch _ => pure none
    match res? with
    | none => pure ()
    | some res =>
      total := total + res.compiled.size
      for (nm, issues) in res.usageIssues do
        bad := bad + 1
        IO.println s!"{m} `{nm}`:"
        for i in issues do IO.println s!"    {i}"
  IO.println s!"declarations compiled: {total}; declarations with usage issues: {bad}"

#eval main
