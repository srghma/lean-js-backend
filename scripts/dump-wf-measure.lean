/-
Print, for well-founded recursive declarations, where Lean stored the termination
measure: the packed non-recursive declaration, and the measure function found inside it
as either the `h` of `WellFounded.Nat.fix h _ _` (carrier `Nat`) or the `f` of
`invImage f inst` (general carrier).

    lake env lean --run scripts/dump-wf-measure.lean <Module.Name> [<Decl.Name> ...]
-/
import Lean
import Lean.Elab.PreDefinition.WF.Eqns

open Lean Lean.Meta

/-- The measure function of the first `WellFounded.Nat.fix h _ _` or `invImage f inst`
    application inside `e`, with a tag saying which of the two was found. -/
partial def findMeasure? (e : Expr) : Option (String × Expr) :=
  if e.isAppOf ``WellFounded.Nat.fix && e.getAppNumArgs ≥ 4 then
    some ("WellFounded.Nat.fix", e.getArg! 2)
  else if e.isAppOf ``invImage && e.getAppNumArgs ≥ 4 then
    some ("invImage", e.getArg! 2)
  else
    match e with
    | .app f a => (findMeasure? f).orElse fun _ => findMeasure? a
    | .lam _ _ b _ | .forallE _ _ b _ => findMeasure? b
    | .letE _ _ v b _ => (findMeasure? v).orElse fun _ => findMeasure? b
    | .mdata _ b => findMeasure? b
    | .proj _ _ b => findMeasure? b
    | _ => none

def report (n : Name) : MetaM Bool := do
  match Lean.Elab.WF.eqnInfoExt.find? (← getEnv) n with
  | none => return false
  | some info =>
    IO.println s!"{n}: WF recursion"
    IO.println s!"  clique       : {info.declNames.toList}"
    IO.println s!"  packed decl  : {info.declNameNonRec}"
    match (← getEnv).find? info.declNameNonRec |>.bind ConstantInfo.value? with
    | none => IO.println "  packed decl has no value"
    | some v =>
      match findMeasure? v with
      | none => IO.println "  no measure application found"
      | some (how, f) => IO.println s!"  measure, via {how}:\n    {← ppExpr f}"
    return true

def main (args : List String) : IO Unit := do
  let mod :: decls := args | throw (IO.userError "usage: <Module.Name> [<Decl.Name> ...]")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := mod.toName }] {}
  let act : MetaM Unit := do
    for d in decls do
      let names := [mod.toName ++ d.toName, d.toName]
      let mut found := false
      for n in names do
        if !found then
          found ← report n
      if !found then
        IO.println s!"{d}: no WF EqnInfo under {names}"
  let _ ← act.run' {} |>.toIO { fileName := "<dump>", fileMap := default } { env }
  return ()
