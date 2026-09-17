/-
Which rows of the `@[extern]` catalogue can never appear in a `Term`?

`LakeJs/ExternTable.lean` maps the *text* of a Lean name to the row of `LakeJs.Externs`
that stands for it, and the translation reaches a row only by looking a name up there.
A row is therefore unreachable when

* this version of Lean has no declaration of that name, so the lookup can never match, or
* the declaration is one `LakeJs.Totality` refuses (an `IO` type), so no declaration that
  calls it is ever compiled.

Run it with

    lake env lean scripts/check-extern-names.lean
-/
import Lean
import Std
import LakeJs.ExternTable
import LakeJs.Totality

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Lean }, { module := `Std }] {}
  let mut missing : Array String := #[]
  let mut io : Array String := #[]
  for (nm, _) in LakeJs.ExternTable.externTable.toList do
    let n := nm.toName
    match env.find? n with
    | none => missing := missing.push nm
    | some ci => if LakeJs.Totality.isIOType ci.type then io := io.push nm
  IO.println s!"rows whose Lean name this toolchain does not have ({missing.size}):"
  for m in missing.qsort (· < ·) do IO.println s!"  {m}"
  IO.println s!"rows whose Lean declaration has an IO type, which the backend refuses ({io.size}):"
  for m in io.qsort (· < ·) do IO.println s!"  {m}"

#eval main
