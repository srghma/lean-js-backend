/-
Print, for every inductive declared in a module, the shape the backend's type language
gives it: `enum`, `record`, `taggedUnion`, `recTaggedUnion`, `recObject`, `recAlias`,
`mutualRecursiveFamily`, or one of the three erased/degenerate cases (`bool`, `newtype`,
`unit (erased)`).

    lake env lean --run scripts/dump-shape.lean <Module.Name> [--out <file>]

A caveat: several types the backend treats as *primitive* (`List`, `Array`, `String`,
`ByteArray`, …) are ordinary inductives in Lean, and the classifier reports the structural
shape they would have if they were user-defined.  In `Ty` they are leaves.

The shape is computed the way the translator computes it: a field is counted only if it
survives erasure — a `Prop`-typed field, a type-former field and a field of a type with a
single value carry nothing at run time — and a declaration counts as recursive only if a
*surviving* field mentions it.
-/
import Lean

open Lean Lean.Meta

/-- Is a field of this type dropped: a proof, a type, or a value of a type with one
    inhabitant? -/
partial def erasedFieldTy (fuel : Nat) (ty : Expr) : MetaM Bool := do
  if ← isProp ty then return true
  if (← inferType ty).isSort && (← whnf (← inferType ty)) matches .sort (.succ _) then
    -- `ty : Sort u`: a field holding a *type* is erased
    if ty.isSort then return true
  if ty.isSort then return true
  if fuel == 0 then return false
  let fn := ty.getAppFn
  let some n := fn.constName? | return false
  match (← getEnv).find? n with
  | some (.inductInfo iv) =>
      if iv.all.length != 1 then return false
      match iv.ctors with
      | [cn] =>
          let some (.ctorInfo ci) := (← getEnv).find? cn | return false
          let cnt ← surviving (fuel - 1) ci
          return cnt == 0
      | _ => return false
  | _ => return false
where
  /-- How many fields of this constructor survive erasure. -/
  surviving (fuel : Nat) (ci : ConstructorVal) : MetaM Nat := do
    forallBoundedTelescope ci.type ci.numParams fun _ rest =>
      forallTelescopeReducing rest fun fields _ => do
        let mut k := 0
        for f in fields do
          if !(← erasedFieldTy fuel (← inferType f)) then k := k + 1
        return k

/-- The surviving field types of a constructor. -/
def survivingFieldTys (ci : ConstructorVal) : MetaM (Array Expr) := do
  forallBoundedTelescope ci.type ci.numParams fun _ rest =>
    forallTelescopeReducing rest fun fields _ => do
      let mut out := #[]
      for f in fields do
        let ty ← inferType f
        if !(← erasedFieldTy 8 ty) then out := out.push (← instantiateMVars ty)
      return out

/-- Does this type mention any of these declarations? -/
def mentions (names : List Name) (e : Expr) : Bool :=
  Option.isSome <| e.find? fun sub =>
    match sub.getAppFn.constName? with
    | some n => names.contains n
    | none => false

/-- Which members of the block this one mentions through a surviving field. -/
def memberEdges (iv : InductiveVal) : MetaM (List Name) := do
  let mut out : List Name := []
  for cn in iv.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? cn | continue
    for ty in ← survivingFieldTys ci do
      for m in iv.all do
        if mentions [m] ty && !out.contains m then out := m :: out
  return out

/-- The members reachable from `start`, following surviving fields. -/
partial def reachable (edges : Name → List Name) (todo : List Name) (seen : List Name) : List Name :=
  match todo with
  | [] => seen
  | n :: rest =>
      if seen.contains n then reachable edges rest seen
      else reachable edges (edges n ++ rest) (n :: seen)

def shapeOf (iv : InductiveVal) : MetaM String := do
  let isPropType ← forallTelescopeReducing iv.type fun _ concl => do
    let concl ← whnf concl
    return concl.isProp
  if isPropType then
    return s!"{iv.name}: proof (the whole type is a `Prop`: erased, no Ty)"
  let mut counts : Array Nat := #[]
  let mut selfRec := false
  for cn in iv.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? cn | continue
    let tys ← survivingFieldTys ci
    counts := counts.push tys.size
    for ty in tys do
      if mentions [iv.name] ty then selfRec := true
  let nCtors := counts.size
  let total := counts.foldl (· + ·) 0
  -- a block is a genuine family only where two of its members reach each other
  let mut edgeMap : List (Name × List Name) := []
  for m in iv.all do
    let some (.inductInfo mv) := (← getEnv).find? m | continue
    edgeMap := (m, ← memberEdges mv) :: edgeMap
  let edges : Name → List Name := fun n =>
    match edgeMap.find? (·.1 == n) with | some (_, es) => es | none => []
  let inCycle := (iv.all.filter (· != iv.name)).any fun m =>
    (reachable edges [iv.name] []).contains m && (reachable edges [m] []).contains iv.name
  let verdict : String :=
    if inCycle then "mutualRecursiveFamily"
    else if total == 0 then
      if nCtors == 1 then "unit (erased: no Ty)"
      else if nCtors == 2 then "bool"
      else "enum"
    else if nCtors == 1 then
      if total == 1 then (if selfRec then "recAlias (newtype)" else "newtype (erased wrapper)")
      else (if selfRec then "recObject" else "record")
    else
      if selfRec then "recTaggedUnion" else "taggedUnion"
  return s!"{iv.name}: {verdict}\n  surviving fields per constructor : {counts.toList}\n  members of the block             : {iv.all}\n  recursive (through a surviving field) : {selfRec}, in a mutual cycle : {inCycle}"

def main (args : List String) : IO Unit := do
  let (args, out) :=
    match args with
    | m :: "--out" :: f :: rest => (m :: rest, some f)
    | _ => (args, none)
  let mod :: names := args | throw (IO.userError "usage: <Module.Name> [--out <file>] [<Type.Name> ...]")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := mod.toName }] {}
  let act : MetaM String := do
    let env ← getEnv
    let idx := env.getModuleIdx? mod.toName
    let mut lines := #[]
    if !names.isEmpty then
      for nm in names do
        let n := nm.toName
        match env.find? n with
        | some (.inductInfo iv) => lines := lines.push (← shapeOf iv)
        | _ => lines := lines.push s!"{n}: not an inductive in this environment"
    else
      for (n, ci) in env.constants.toList do
        if env.getModuleIdxFor? n == idx then
          if let .inductInfo iv := ci then
            lines := lines.push (← shapeOf iv)
    return String.intercalate "\n\n" (lines.qsort (· < ·)).toList ++ "\n"
  let (s, _) ← act.run' {} |>.toIO { fileName := "<dump>", fileMap := default } { env }
  match out with
  | some f => IO.FS.writeFile f s
  | none => IO.print s
