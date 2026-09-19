/-
Print, for a well-founded recursive declaration, the *relation* its measure lands in —
not just the measure function.

    lake env lean --run scripts/dump-wf-relation.lean <Module.Name> [<Decl.Name> ...]

`scripts/dump-wf-measure.lean` prints the `termination_by` expression; this script prints
what that expression is compared with.  The distinction is the whole question for a
lexicographic `termination_by`: `boom`'s measure lands in `Nat` with `Nat.lt`, so it can be
transcribed as a single rank, while `ack`'s lands in `Nat ×' Nat` with `Prod.Lex`, which no
single `Nat` rank can carry — the recursion has to be curried into one ranked recursion per
component instead.
-/
import Lean
import Lean.Elab.PreDefinition.WF.Eqns

open Lean Lean.Meta

/-- The first `invImage f inst` or `WellFounded.Nat.fix h _ _` application inside `e`,
    together with the measure and (for `invImage`) the relation instance. -/
partial def findInvImage? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOf ``invImage && e.getAppNumArgs ≥ 4 then
    -- invImage (α β) (f : α → β) (h : WellFoundedRelation β)
    some (e.getArg! 1, e.getArg! 2, e.getArg! 3)
  else
    match e with
    | .app f a => (findInvImage? f).orElse fun _ => findInvImage? a
    | .lam _ _ b _ | .forallE _ _ b _ => findInvImage? b
    | .letE _ _ v b _ => (findInvImage? v).orElse fun _ => findInvImage? b
    | .mdata _ b => findInvImage? b
    | .proj _ _ b => findInvImage? b
    | _ => none

def report (n : Name) : MetaM Unit := do
  let some info := Lean.Elab.WF.eqnInfoExt.find? (← getEnv) n
    | do IO.println s!"{n}: not elaborated by well-founded recursion"; IO.println ""; return
  IO.println s!"{n}: WF recursion"
  IO.println s!"  packed decl  : {info.declNameNonRec}"
  match (← getEnv).find? info.declNameNonRec |>.bind ConstantInfo.value? with
  | none => IO.println "  packed declaration has no value"
  | some v =>
    match findInvImage? v with
    | none => IO.println "  no `invImage` application found (measure is a plain `Nat`)"
    | some (β, f, inst) =>
      IO.println s!"  measure      : {← ppExpr f}"
      IO.println s!"  lands in     : {← ppExpr β}"
      IO.println s!"  ordered by   : {← ppExpr inst}"
      IO.println s!"  single-Nat rank possible : {β.isConstOf ``Nat}"
  IO.println ""

def main (args : List String) : IO Unit := do
  let mod :: decls := args | throw (IO.userError "usage: <Module.Name> [<Decl.Name> ...]")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := mod.toName }] {}
  let act : MetaM Unit := do
    let env ← getEnv
    let idx := env.getModuleIdx? mod.toName
    let names : List Name :=
      if decls.isEmpty then
        env.constants.toList.filterMap fun (n, _) =>
          if env.getModuleIdxFor? n == idx then some n else none
      else
        decls.map fun d =>
          let full := mod.toName ++ d.toName
          if (env.find? full).isSome then full else d.toName
    for n in names do
      report n
  let _ ← act.run' {} |>.toIO { fileName := "<dump>", fileMap := default } { env }
  return ()
