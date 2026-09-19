/-
Print, for each named declaration, which kind of recursion Lean recorded for it, and —
for structural recursion — whether the argument it recurses on survives erasure.

    lake env lean --run scripts/dump-recursion-kind.lean <Module.Name> [<Decl.Name> ...]

With no declaration names, every declaration of the module is reported.

The point of the `recArgPos` line is the whitelist question: a declaration that recurses
structurally on a `Prop`-typed argument (an `Acc` proof, say) has no rank at run time,
because that argument is erased — so "Lean says structural" is not on its own a licence
to translate it.
-/
import Lean
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns

open Lean Lean.Meta

/-- The type of parameter `i` of `declName`, and whether it is a proof. -/
def paramInfo (declName : Name) (i : Nat) : MetaM (Option (Expr × Bool)) := do
  let some ci := (← getEnv).find? declName | return none
  forallTelescopeReducing ci.type fun xs _ => do
    let some x := xs[i]? | return none
    let ty ← inferType x
    return some (ty, (← isProp ty))

def reportStructural (n : Name) : MetaM Bool := do
  let some info := Lean.Elab.Structural.eqnInfoExt.find? (← getEnv) n | return false
  IO.println s!"{n}: structural recursion"
  IO.println s!"  clique     : {info.declNames.toList}"
  IO.println s!"  recArgPos  : {info.recArgPos}"
  match ← paramInfo n info.recArgPos with
  | none => IO.println "  recursed-on argument: not found"
  | some (ty, isPrf) =>
      IO.println s!"  recursed-on argument type : {← ppExpr ty}"
      IO.println s!"  erased (a proof)          : {isPrf}"
      if isPrf then
        IO.println "  ⇒ NO RANK AT RUN TIME: the argument the recursion descends on is erased"
  return true

/-- The measure function of the first `WellFounded.Nat.fix h _ _` or `invImage f inst`
    application inside `e`. -/
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

def reportWF (n : Name) : MetaM Bool := do
  let some info := Lean.Elab.WF.eqnInfoExt.find? (← getEnv) n | return false
  IO.println s!"{n}: well-founded recursion"
  IO.println s!"  clique     : {info.declNames.toList}"
  IO.println s!"  packed     : {info.declNameNonRec}"
  match (← getEnv).find? info.declNameNonRec |>.bind ConstantInfo.value? with
  | none => IO.println "  packed declaration has no value"
  | some v =>
    match findMeasure? v with
    | none => IO.println "  no measure application found"
    | some (how, f) => IO.println s!"  measure, via {how}:\n    {← ppExpr f}"
  return true

def reportFixpoint (n : Name) : MetaM Bool := do
  let some _ := Lean.Elab.PartialFixpoint.eqnInfoExt.find? (← getEnv) n | return false
  IO.println s!"{n}: partial fixpoint (refused: kind 3/4)"
  return true

def report (n : Name) : MetaM Unit := do
  let some ci := (← getEnv).find? n
    | do IO.println s!"{n}: not in the environment"; IO.println ""; return
  let safety := if ci.isUnsafe then "unsafe" else "safe"
  let hasCode := (Lean.IR.findEnvDecl (← getEnv) n).isSome
  if !(← reportStructural n) then
    if !(← reportWF n) then
      if !(← reportFixpoint n) then
        IO.println s!"{n}: no recursion info recorded"
  IO.println s!"  safety     : {safety}"
  IO.println s!"  compiled   : {hasCode}"
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
