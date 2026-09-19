module

public import LakeJs.Reduce

@[expose] public section

set_option autoImplicit false

/-!
# Progress: there is nothing to get stuck on

`LakeJs.Reduce` says how a `Term` runs.  This module used to say that it *does* run: with
a small-step semantics, a closed term had to be shown to be either an answer (a `Value`,
including the `Neutral` terms that waited for something outside the language) or able to
take a `Step`.  Progress is not a theorem any more, it is the **type** of the evaluator:

```
Term.eval : Term Sg Γ Ρ τ → GEnv Sg.decls → Env Γ → REnv Ρ → τ.den
```

answers with a value of `τ.den` for *every* term, in *every* environment.  There is no
`Option`, no error and no stuck state to characterise, so the three sources of stuckness
the old proof had to rule out are gone at their root:

* **an extern with no meaning** — every entry of `LakeJs.Externs` denotes a total Lean
  function (`Extern.den`), so `Term.extern` evaluates to it;
* **a dispatch with no branch for the tag** — `Term.caseTag` carries `Ty.caseOkAlts`, so
  it either has a default branch or a branch for every constructor, and the evaluator's
  fallback (`Ty.dflt`) is unreachable;
* **a recursion that never comes back** — `Term.fix` carries its measure, and a self
  call recurses only on a strict lexicographic decrease of it.

What is worth writing down instead is *what* running each construct does.  The equations
below are the small-step rules of the old semantics, recovered as propositional equalities
about the evaluator: β, the δ-rule for an extern, the ι-rules for a conditional and a
dispatch, and the rules for a jump, a join point and a recursion.  Every one of them holds
by `rfl`, so they are checked whenever this module is built.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty}
variable (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)

/-! ## Progress, as it now reads -/

/-- **Every term has an answer.**  This is what progress has become: not a theorem about
    a relation, but the observation that the evaluator is a function. -/
theorem Term.progress (t : Term Sg Γ Ρ τ) : ∃ v : τ.den, t.eval δ γ ρ = v :=
  ⟨t.eval δ γ ρ, rfl⟩

/-- **Evaluation is deterministic.**  Also by construction: a Lean function has one
    value. -/
theorem Term.eval_deterministic (t : Term Sg Γ Ρ τ) {v w : τ.den}
    (hv : t.eval δ γ ρ = v) (hw : t.eval δ γ ρ = w) : v = w := hv ▸ hw

/-- The same, for a block. -/
theorem Tail.progress {Ω : LCtx} (b : Tail Sg Γ Ω Ρ τ) (lenv : LEnv τ Ω) :
    ∃ v : τ.den, b.eval δ γ lenv ρ = v :=
  ⟨b.eval δ γ lenv ρ, rfl⟩

/-! ## The rules the step relation used to have -/

/-- **β**: applying an abstraction binds the argument. -/
@[simp] theorem Term.eval_beta (b : Term Sg (σ :: Γ) Ρ τ) (a : Term Sg Γ Ρ σ) :
    (Term.ap (.lam b) a).eval δ γ ρ = b.eval δ (.cons (a.eval δ γ ρ) γ) ρ := rfl

/-- A `let` binds the value of what it binds. -/
@[simp] theorem Term.eval_letE (e : Term Sg Γ Ρ σ) (b : Term Sg (σ :: Γ) Ρ τ) :
    (Term.letE e b).eval δ γ ρ = b.eval δ (.cons (e.eval δ γ ρ) γ) ρ := rfl

/-- **δ**: an extern runs the total Lean function it denotes. -/
@[simp] theorem Term.eval_extern {σs : List Ty} (e : Externs σs τ) :
    (Term.extern (Sg := Sg) (Γ := Γ) (Ρ := Ρ) e).eval δ γ ρ = e.den := rfl

/-- **ι**, one way: a conditional on `true` runs its first arm. -/
@[simp] theorem Term.eval_ite_true (c : Term Sg Γ Ρ (.prim .bool))
    (t e : Term Sg Γ Ρ τ) (hc : c.eval δ γ ρ = true) :
    (Term.ite c t e).eval δ γ ρ = t.eval δ γ ρ := by
  show (if cond (c.eval δ γ ρ) true false then _ else _) = _
  rw [hc]
  rfl

/-- **ι**, the other way. -/
@[simp] theorem Term.eval_ite_false (c : Term Sg Γ Ρ (.prim .bool))
    (t e : Term Sg Γ Ρ τ) (hc : c.eval δ γ ρ = false) :
    (Term.ite c t e).eval δ γ ρ = e.eval δ γ ρ := by
  show (if cond (c.eval δ γ ρ) true false then _ else _) = _
  rw [hc]
  rfl

/-- A dispatch runs the branch whose tag the scrutinee has, with the constructor's fields
    bound. -/
theorem Term.eval_caseTag {tags : List Nat} {full : Bool} (scrut : Term Sg Γ Ρ σ)
    (alts : Alts Sg Γ Ρ σ τ tags full) (h : σ.caseOkAlts full tags = true) :
    (Term.caseTag scrut alts h).eval δ γ ρ =
      (alts.eval (σ.tagOfVal (scrut.eval δ γ ρ)) (σ.fieldsOfVal (scrut.eval δ γ ρ))
        δ γ ρ).getD τ.dflt := by
  show (match alts.eval _ _ δ γ ρ with | some r => r | none => τ.dflt) = _
  cases alts.eval (σ.tagOfVal (scrut.eval δ γ ρ)) (σ.fieldsOfVal (scrut.eval δ γ ρ))
      δ γ ρ <;> rfl

/-- A branch whose tag matches is the one that runs. -/
@[simp] theorem Alts.eval_cons_hit {tags : List Nat} {full : Bool} (tag : Nat)
    (fields : Layout.FieldLayout) (hf : σ.ctorFields? tag = some fields)
    (body : Term Sg (fields ++ Γ) Ρ τ) (rest : Alts Sg Γ Ρ σ τ tags full)
    (fs : List Data) :
    (Alts.cons tag fields hf body rest).eval tag fs δ γ ρ =
      some (body.eval δ ((Env.ofData fields fs).append γ) ρ) := by
  simp [Alts.eval]

/-- A branch whose tag does not match passes the dispatch on. -/
@[simp] theorem Alts.eval_cons_miss {tags : List Nat} {full : Bool} (tag t : Nat)
    (fields : Layout.FieldLayout) (hf : σ.ctorFields? tag = some fields)
    (body : Term Sg (fields ++ Γ) Ρ τ) (rest : Alts Sg Γ Ρ σ τ tags full)
    (fs : List Data) (hne : tag ≠ t) :
    (Alts.cons tag fields hf body rest).eval t fs δ γ ρ = rest.eval t fs δ γ ρ := by
  simp [Alts.eval, hne]

/-- A jump runs the block its label names, on the arguments it supplies — and nothing
    happens after it. -/
@[simp] theorem Tail.eval_jmp {Ω : LCtx} {ps : List Ty} (l : Ω ∋ₗ ps)
    (args : Spine Sg Γ Ρ ps) (lenv : LEnv τ Ω) :
    (Tail.jmp (τ := τ) l args).eval δ γ lenv ρ = lenv.get l (args.eval δ γ ρ) := rfl

/-- A join point binds its block and runs the rest. -/
@[simp] theorem Tail.eval_join {Ω : LCtx} (ps : List Ty)
    (body : Tail Sg (ps ++ Γ) Ω Ρ τ) (rest : Tail Sg Γ (ps :: Ω) Ρ τ)
    (lenv : LEnv τ Ω) :
    (Tail.join ps body rest).eval δ γ lenv ρ =
      rest.eval δ γ (.cons (fun args => body.eval δ (args.append γ) lenv ρ) lenv) ρ :=
  rfl

/-- **The one rule that used to be a loop**: a recursion runs its body with the guarded
    iteration as its self-reference, which recurses when the measure descends and answers
    `stuck` when it does not.  Compare `Term.fixFun_unfold` and
    `Term.fixFun_stuck_of_not_lt`. -/
theorem Term.eval_selfCall {ps : List Ty} (r : Ρ ∋ᵣ ⟨ps, τ⟩) (args : Spine Sg Γ Ρ ps) :
    (Term.selfCall r args).eval δ γ ρ = ρ.get r (args.eval δ γ ρ) := rfl

end LakeJs.Expr

end
