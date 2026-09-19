module

public import Lean
public meta import LakeJs.DescentSimp
public import LakeJs.DescentVC
public import LakeJs.Examples.Ops

@[expose] public section

set_option autoImplicit false

/-!
# `descent_vc`: the tactic that assembles a descent derivation

`LakeJs.DescentVC` is a calculus: one rule per construct of the grammar, and a derivation
is built by `apply`ing them structurally.  Doing that by hand is mechanical — the shape of
the term decides which rule applies at every node — which is what
`TERM_RANK_FLAKINESS_AND_ALTERNATIVES.md` §8 step 6 needs automated before a *generated*
program can carry its own verification condition.

This module supplies that automation:

| tactic | what it does |
| :-- | :-- |
| `self_indep_step` | one rule of the calculus, chosen by the head constructor of the term |
| `self_indep` | `self_indep_step` to exhaustion, on every goal it produces |
| `descent_vc as` | `Term.Descends` ⟶ the judgment, argument environment named `as`, then `self_indep` |
| `descent_call` | normalise one leftover self-call obligation into plain arithmetic |
| `descent_auto as` | `descent_vc as` followed by `descent_call <;> omega` on what is left |

The division of labour is the one the plan asks for: **the structural half is complete and
automatic, and everything it leaves is arithmetic**.  `self_indep` cannot leave anything
else, because the only rule of the calculus with a non-judgmental premise is
`Term.selfIndepOn_selfCall`, whose premise is

```
∀ γ' g, Φ γ' g → S (arguments of the call)
```

— the path condition of the call implies that its arguments descend, which is exactly the
obligation Lean's own `decreasing_by` discharges for the declaration the term came from.
-/

namespace LakeJs.Expr

/-! ## The structural half -/

/-- One step of the descent calculus: the rule of `LakeJs.DescentVC` whose conclusion
    matches the goal.  The order below is irrelevant to the result — no two rules apply to
    the same term — and is chosen so that the common cases are tried first. -/
syntax "self_indep_step" : tactic

macro_rules
  | `(tactic| self_indep_step) => `(tactic|
      first
        -- leaves
        | exact Term.selfIndepOn_var _
        | exact Term.selfIndepOn_lit _
        | exact Term.selfIndepOn_global _
        | exact Term.selfIndepOn_extern _
        | exact Spine.selfIndepOn_nil
        | exact Alts.selfIndepOn_nilFull
        | exact AltsT.selfIndepOn_nilFull
        -- terms
        | apply Term.selfIndepOn_ap
        | apply Term.selfIndepOn_lam
        | apply Term.selfIndepOn_letE
        | apply Term.selfIndepOn_ite
        | apply Term.selfIndepOn_ctor
        | apply Term.selfIndepOn_proj
        | apply Term.selfIndepOn_tagOf
        | apply Term.selfIndepOn_structSize
        | apply Term.selfIndepOn_lazyMk
        | apply Term.selfIndepOn_lazyForce
        | apply Term.selfIndepOn_caseTag
        | apply Term.selfIndepOn_block
        | apply Term.selfIndepOn_outerCall
        | apply Term.selfIndepOn_selfCall
        -- spines and branches
        | apply Spine.selfIndepOn_cons
        | apply Alts.selfIndepOn_cons
        | apply Alts.selfIndepOn_deflt
        | apply AltsT.selfIndepOn_cons
        | apply AltsT.selfIndepOn_deflt
        -- blocks
        | apply Tail.selfIndepOn_ret
        | apply Tail.selfIndepOn_jmp
        | apply Tail.selfIndepOn_letT
        | apply Tail.selfIndepOn_iteT
        | apply Tail.selfIndepOn_caseT
        | apply Tail.selfIndepOn_join)

/-- The structural derivation, to exhaustion: every judgment goal is decomposed until the
    only goals left are the self-call obligations. -/
syntax "self_indep" : tactic

macro_rules
  | `(tactic| self_indep) => `(tactic| repeat' self_indep_step)

/-- **Reduce `Term.Descends` to the calculus and run it.**  `descent_vc as` names the
    argument environment `as` — the obligations left over speak about it — and leaves one
    goal per self call of the body. -/
syntax "descent_vc" (ppSpace colGt ident)? : tactic

macro_rules
  | `(tactic| descent_vc) => `(tactic| descent_vc as)
  | `(tactic| descent_vc $x:ident) => `(tactic|
      (refine Term.descends_of_selfIndepOn _ _ _ _ _ ?_
       intro $x:ident
       self_indep))

/-! ## The arithmetic half

What `self_indep` leaves is `∀ γ' g, Φ γ' g → S args`, where `Φ` is the path condition the
calculus accumulated — a nest of conjunctions and existentials ending in an equation that
fixes the environment — and `S` is *"the measure descends"*.  `descent_call` performs the
bookkeeping that is the same in every such goal: introduce, destructure the path condition,
substitute the equations it contains, split the argument environment into its components,
and turn a one-component lexicographic comparison into `<` on `Nat`.  What remains is the
arithmetic, in the form `omega` wants it. -/

open Lean Elab Tactic Meta in
/-- Case-split every hypothesis that a path condition is built out of: a conjunction, an
    existential, or an argument environment `Env (σ :: Γ)`.  Repeated to exhaustion, this
    flattens the accumulated path condition into its atoms and the argument tuple into its
    components. -/
elab "descent_destruct" : tactic => do
  let rec splittable (t : Expr) : MetaM Bool := do
    let t ← whnfR t
    if t.isAppOf ``And || t.isAppOf ``Exists then return true
    if t.isAppOf ``LakeJs.Expr.Env then
      let some ctx := t.getAppArgs[0]? | return false
      return (← whnfR ctx).isAppOfArity ``List.cons 3
    return false
  let rec go (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := do
    match fuel with
    | 0 => return [g]
    | fuel + 1 =>
      let target? ← g.withContext do
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          if ← splittable d.type then return some d.fvarId
        return none
      match target? with
      | none => return [g]
      | some fv =>
        let subs ← g.cases fv
        let gss ← subs.toList.mapM fun s => go s.mvarId fuel
        return gss.flatten
  liftMetaTactic fun g => go g 64

/-! ### The unfoldings that run the interpreter

Both the path condition and the descent obligation are `Term.eval` / `Spine.eval` /
`Term.measureVal` applied to *concrete* syntax, so unfolding the evaluator and the
runtime's primitives turns them into ordinary arithmetic about the argument components —
which is what `omega` and the other arithmetic tactics need to see.

The set is `descent_eval`, registered in `LakeJs.DescentSimp`, and it is open: a front end
that emits new abbreviations for calls of the runtime tags them with `@[descent_eval]` and
the tactics below pick them up. -/

/-! Reading a variable out of an argument environment extended by the enclosing one.  The
plain unfoldings of `Env.get` and `Env.append` are awkward for `simp` here, because the
type of an environment mentions its context and rewriting the context underneath `Env.get`
is a dependent rewrite; these three equations — all `rfl` — do the same job as rewrites of
`Env.get` itself, so no dependent motive arises. -/

/-- The empty argument list contributes nothing. -/
@[descent_eval] theorem Env.nil_append {Δ : Ctx} (γ : Env Δ) :
    (Env.nil).append γ = γ := rfl

/-- The first variable of an extended environment is the first argument. -/
@[descent_eval] theorem Env.get_head_append {σ : Ty} {Γ Δ : Ctx} (v : σ.den) (rest : Env Γ)
    (γ : Env Δ) : ((Env.cons v rest).append γ).get .head = v := rfl

/-- Every later variable skips it. -/
@[descent_eval] theorem Env.get_tail_append {σ τ : Ty} {Γ Δ : Ctx} (v : σ.den)
    (rest : Env Γ) (γ : Env Δ) (x : (Γ ++ Δ) ∋ τ) :
    ((Env.cons v rest).append γ).get (.tail x) = (rest.append γ).get x := rfl

-- the evaluator itself
attribute [descent_eval]
  Term.eval Spine.eval Alts.eval Tail.eval AltsT.eval
  Term.measureVal Term.measure1 Term.structMeasure
  Env.toNatVec Env.get Env.append Env.ofData Env.pop Env.pop_cons Env.get_head_cons
  Ty.toData Ty.ofData Ty.fieldsOfVal Ty.tagOfVal Ty.buildVal
  Data.size Data.sizeList Data.fields Data.tag
  Term.callExtern Term.appSpine
  Extern.den Extern.den1 Extern.den2 Extern.den3 Extern.den4 Extern.den6
  LeanInitPureExtern1OnlyPrim.eval LeanInitPureExtern2OnlyPrim.eval
  LeanInitPureExtern3OnlyPrim.eval LeanInitPureExtern5.eval
  LeanPrimLit.val
  Lex.NatVec.lt_one_iff
  List.map_map List.map_id List.map_id' List.map_nil List.map_cons
  Function.comp_def Function.comp_apply
  dite_true dite_false ite_true ite_false

-- the abbreviations the front end emits for calls of the runtime
attribute [descent_eval]
  Ops.prim1Op Ops.prim2Op Ops.prim3Op Ops.prim5Op
  Ops.natAdd Ops.natSub Ops.natMul Ops.natMod Ops.natDiv Ops.natPow
  Ops.natEq Ops.natLe Ops.natLt
  Ops.natShiftLeft Ops.natShiftRight Ops.natLand Ops.natLor Ops.natLog2
  Ops.natToInt Ops.intToNat
  Ops.intAdd Ops.intSub Ops.intMul Ops.intEq Ops.intLe Ops.intLt
  Ops.strAppend Ops.strLength Ops.strUtf8ByteSize Ops.strPush Ops.strCharAt
  Ops.strEq Ops.strExtract Ops.strMemcmp
  Ops.arrLen Ops.arrGet Ops.arrEmpty Ops.arrPush Ops.arrReplicate Ops.arrSet
  Ops.arrSwap Ops.arrPop

open Lean Elab Tactic Meta in
/-- Give every argument component its Lean type.  A component of an argument list is bound
    at type `σ.den`, and an equation between two of them is an equation at `p.denote`;
    both are `Type`-valued functions, so an arithmetic tactic does not recognise such a
    statement as one about numbers until they are unfolded.  This unfolds them wherever
    they occur, in the goal and in every hypothesis. -/
elab "descent_denote" : tactic => do
  let norm (e : Expr) : MetaM Expr :=
    Meta.transform e (post := fun e' => do
      if e'.isAppOfArity ``LakeJs.Ty.den 1 || e'.isAppOfArity ``LakeJs.LeanPrimTy.denote 1 then
        let e'' ← whnf e'
        return if e'' == e' then .done e' else .visit e''
      return .continue)
  liftMetaTactic1 fun g => do
    let fvars ← g.withContext do
      pure ((← getLCtx).decls.foldl (init := #[]) fun acc d? =>
        match d? with
        | some d => if d.isImplementationDetail || d.isAuxDecl then acc else acc.push d.fvarId
        | none => acc)
    let (reverted, g) ← g.revert fvars
    let t ← g.withContext (norm (← g.getType))
    let g ← g.change t
    let (_, g) ← g.introNP reverted.size
    return some g

/-- Run the interpreter away, in the goal and in the path condition. -/
syntax "descent_reduce" : tactic

macro_rules
  | `(tactic| descent_reduce) => `(tactic|
      simp only [descent_eval, decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.not_eq_true, Bool.not_eq_false] at *)

/-- Normalise one self-call obligation: introduce and destructure the path condition, then
    expose the comparison. -/
syntax "descent_call" : tactic

macro_rules
  | `(tactic| descent_call) => `(tactic|
      (intro _ _ _
       descent_destruct
       subst_eqs
       descent_destruct
       try descent_reduce
       try descent_reduce
       descent_denote
       try subst_eqs
       try descent_reduce))

open Lean Elab Tactic Meta in
/-- Case-split the recursion subject of a *structural* recursion over data.  Such an
    obligation compares the size of a field with the size of the value it came from, and
    neither is a number until one knows which constructor the value is; the values that
    carry fields are the cons lists and the `Data` trees. -/
elab "descent_subject" : tactic => do
  let splittable (t : Expr) : MetaM Bool := do
    let t ← whnfR t
    return t.isAppOfArity ``List 1 || t.isConstOf ``LakeJs.Data
  let rec go (g : MVarId) (fuel : Nat) (progress : Bool) : MetaM (List MVarId × Bool) := do
    match fuel with
    | 0 => return ([g], progress)
    | fuel + 1 =>
      let target? ← g.withContext do
        for d in ← getLCtx do
          if d.isImplementationDetail || d.isAuxDecl then continue
          if ← splittable d.type then return some d.fvarId
        return none
      match target? with
      | none => return ([g], progress)
      | some fv =>
        let subs ← g.cases fv
        let mut gs := []
        for s in subs do
          let (gs', _) ← go s.mvarId fuel true
          gs := gs ++ gs'
        return (gs, true)
  let (gs, progress) ← liftMetaMAtMain fun g => go g 8 false
  unless progress do
    throwError "descent_subject: no recursion subject to split"
  replaceMainGoal gs

/-- Close a comparison of measures: a lexicographic vector is split into the component
    that decreases — `Lex.NatVec.Lt.head` when an earlier one does, `.tail` when the
    earlier ones are equal — and the arithmetic itself is `omega`, together with the one
    fact about `Nat` that is not linear and does occur in the corpus, that a remainder is
    smaller than its modulus. -/
syntax "descent_lt" : tactic

macro_rules
  | `(tactic| descent_lt) => `(tactic|
      first
        | omega
        | (apply Nat.mod_lt; omega)
        | (apply Lex.NatVec.Lt.head; descent_lt)
        | (apply Lex.NatVec.Lt.tail; descent_lt))

/-- Close one normalised obligation.  Beyond the comparison itself there are three things
    a generated body leaves behind: tests of the path condition that `simp` has to fold
    into the hypotheses, a measure that branches on the member of a merged clique (so the
    comparison is under an `if` that the path condition decides), and — for a structural
    recursion over data — a recursion subject that has to be case-split before its size is
    a number at all. -/
syntax "descent_arith" : tactic

macro_rules
  | `(tactic| descent_arith) => `(tactic|
      first
        | descent_lt
        | (descent_subject
           all_goals (try descent_reduce)
           all_goals (first | descent_lt | (simp_all; all_goals descent_lt)))
        | (simp_all; all_goals descent_lt)
        | (split <;> descent_arith)
        | assumption)

/-- The whole verification condition, when the arithmetic is the kind the corpus has: the
    structural derivation, then one normalised obligation per self call, each closed by
    `descent_arith`. -/
syntax "descent_auto" (ppSpace colGt ident)? : tactic

macro_rules
  | `(tactic| descent_auto) => `(tactic| descent_auto as)
  | `(tactic| descent_auto $x:ident) => `(tactic|
      (descent_vc $x:ident
       all_goals (descent_call <;> descent_arith)))

end LakeJs.Expr

end
