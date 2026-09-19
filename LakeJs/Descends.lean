module

public import LakeJs.Fundamental
public import LakeJs.CertGen

@[expose] public section

set_option autoImplicit false

/-!
# `Descends`: the verification condition that says a recursion never gets stuck

This module is step 6 of the migration of `TERM_RANK_FLAKINESS_AND_ALTERNATIVES.md` §8 —
the *generic theorem* half of its §5.4.

The guarded semantics of `Term.fix` answers `stuck` at a self call whose measure does not
descend.  That is the design's safety valve: a measure the front end read wrongly cannot
produce a wrong number, only an observable `stuck` one.  What it does **not** by itself
give is the statement one actually wants about a *correct* translation:

> the `stuck` branch is never taken, so the recursion satisfies the ordinary unrolling
> equation — the one Lean's own equation lemmas have.

The condition under which that holds is stated here, once and for all, as
`Term.Descends`: *the body consults its self-reference only at arguments of strictly
smaller measure*.  Note what this is and is not:

* it is a property of the **term** and its environment, not of the Lean declaration the
  term was translated from, and not of the front end's reasoning about it.  Nothing about
  Lean's `termination_by`, its `decreasing_by` proof, or the front end's transcription of
  either occurs in it;
* it is exactly the erased-body statement §1.2 of the flakiness note says nobody checks:
  quantified over *all* argument environments, so the branches erasure made reachable are
  included;
* it mentions neither an iteration bound nor the `stuck` branch, so it cannot be satisfied
  by accident.

From it follow the three theorems a checked design needs:

| theorem | reading |
| :-- | :-- |
| `Term.fixFun_unfold_of_descends` | the recursion equals its body run with **itself** as the self-reference — no guard, no `stuck` |
| `Term.fix_stuck_irrelevant` | the value does not depend on the `stuck` term at all: *the branch is unreachable* |
| `Term.fixFun_eq_of_equation` | any Lean function satisfying that same unrolling equation **is** the recursion |

The last is the tool translation validation (step 7 of §8) needs: Lean generates, for
every function it accepts by structural or well-founded recursion, exactly such an
equation lemma, so a faithfulness proof reduces to (a) `Descends` and (b) matching the
body against `f.eq_def`.  `LakeJs.Examples.Descent` carries it out on Ackermann and on a
structural recursion, and also shows the condition has teeth: it fails, provably, for the
recursion whose call does not descend.

Everything here is proved at the level of `LakeJs.Lex.guardedFix`, so none of it depends
on the shape of the grammar: adding a constructor to `Term` cannot invalidate it.
-/

namespace LakeJs.Lex

universe u

/-- **The verification condition, at the level of the runner.**  `step` uses its
    self-reference only at arguments whose measure is strictly smaller: two
    self-references that agree below the current measure give the same answer.

    This is the semantic content of "every self call of the body descends", with the path
    conditions of the branches the call sits under accounted for automatically — a call in
    a branch that the arguments do not take is never evaluated, so it constrains
    nothing. -/
def UsesBelow {k : Nat} {α β : Type u} (m : α → NatVec k) (step : (α → β) → α → β) :
    Prop :=
  ∀ (as : α) (g₁ g₂ : α → β),
    (∀ bs : α, NatVec.Lt (m bs) (m as) → g₁ bs = g₂ bs) → step g₁ as = step g₂ as

/-- **The guard is never refused.**  Under `UsesBelow`, the guarded recursion is its body
    run with the *unguarded* self-reference: the `if` of `guardedFix_unfold` disappears,
    and with it the `stuck` branch. -/
theorem guardedFix_unfold_of_usesBelow {k : Nat} {α β : Type u} (m : α → NatVec k)
    (stuck : α → β) (step : (α → β) → α → β) (h : UsesBelow m step) (as : α) :
    guardedFix m stuck step as = step (guardedFix m stuck step) as := by
  rw [guardedFix_unfold]
  refine h as _ _ (fun bs hbs => ?_)
  rw [(NatVec.lt_iff _ _).mpr hbs]
  rfl

/-- **The `stuck` branch is unreachable.**  Under `UsesBelow`, changing it changes
    nothing: the recursion computes the same function whatever it is. -/
theorem guardedFix_stuck_irrelevant {k : Nat} {α β : Type u} (m : α → NatVec k)
    (s₁ s₂ : α → β) (step : (α → β) → α → β) (h : UsesBelow m step) (as : α) :
    guardedFix m s₁ step as = guardedFix m s₂ step as := by
  have main : ∀ v : NatVec k, Acc (NatVec.Lt (k := k)) v →
      ∀ as : α, m as = v → guardedFix m s₁ step as = guardedFix m s₂ step as := by
    intro v hv
    induction hv with
    | intro v _ ih =>
      intro as has
      rw [guardedFix_unfold_of_usesBelow m s₁ step h as,
        guardedFix_unfold_of_usesBelow m s₂ step h as]
      exact h as _ _ (fun bs hbs => ih (m bs) (has ▸ hbs) bs rfl)
  exact main (m as) (NatVec.acc _) as rfl

/-- **The recursion is the unique solution of its equation.**  Under `UsesBelow`, a
    function that satisfies the body's unrolling equation *is* the guarded recursion.

    This is the shape of a translation-validation proof: `f` is the Lean declaration, and
    the hypothesis is its own equation lemma. -/
theorem guardedFix_eq_of_fixpoint {k : Nat} {α β : Type u} (m : α → NatVec k)
    (stuck : α → β) (step : (α → β) → α → β) (h : UsesBelow m step) (f : α → β)
    (hf : ∀ as : α, step f as = f as) (as : α) : guardedFix m stuck step as = f as := by
  refine guardedFix_eq m stuck step f (fun g as hg => ?_) as
  rw [h as g f hg]
  exact hf as

end LakeJs.Lex

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {ps : List Ty} {τ : Ty} {k : Nat}

/-- **The verification condition of a recursion**: its body consults the self-reference
    only at arguments of strictly smaller measure.

    It does not mention the `stuck` branch, which is the point: `stuck` is what a *failure*
    of this condition produces. -/
def Term.Descends (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) : Prop :=
  Lex.UsesBelow (Term.measureVal measure δ γ ρ)
    (fun (g : Env ps → τ.den) (as : Env ps) => body.eval δ (as.append γ) (.cons g ρ))

/-- The definition, spelled out: the form a proof of `Descends` is given in. -/
theorem Term.descends_iff (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) :
    Term.Descends measure body δ γ ρ ↔
      ∀ (as : Env ps) (g₁ g₂ : Env ps → τ.den),
        (∀ bs : Env ps, Lex.NatVec.Lt (Term.measureVal measure δ γ ρ bs)
            (Term.measureVal measure δ γ ρ as) → g₁ bs = g₂ bs) →
        body.eval δ (as.append γ) (.cons g₁ ρ) = body.eval δ (as.append γ) (.cons g₂ ρ) :=
  Iff.rfl

/-- **The unrolling equation, with no guard.**  A recursion whose calls all descend runs
    its body with *itself* as the self-reference.  Compare `Term.fixFun_unfold`, whose
    self-reference is the guarded one: the `if` and the `stuck` branch are gone. -/
theorem Term.fixFun_unfold_of_descends (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)
    (h : Term.Descends measure body δ γ ρ) (args : Env ps) :
    Term.fixFun measure body stuck δ γ ρ args =
      body.eval δ (args.append γ)
        (.cons (Term.fixFun measure body stuck δ γ ρ) ρ) :=
  Lex.guardedFix_unfold_of_usesBelow _ _ _ h args

/-- **The `stuck` branch is never taken.**  Two recursions that differ only in it compute
    the same function.  This is the statement §5.4 of the flakiness note asks for: not
    "the branch answers a default", but "the branch is unreachable". -/
theorem Term.fix_stuck_irrelevant (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck₁ stuck₂ : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)
    (h : Term.Descends measure body δ γ ρ) (args : Env ps) :
    Term.fixFun measure body stuck₁ δ γ ρ args =
      Term.fixFun measure body stuck₂ δ γ ρ args :=
  Lex.guardedFix_stuck_irrelevant _ _ _ _ h args

/-- **A recursion is the unique solution of its own equation.**  If `f` satisfies the
    body's unrolling equation and the recursion descends, the recursion *is* `f`.

    Unlike `Term.fixFun_eq_of_descends`, whose hypothesis is an induction step, this one
    takes the plain equation — which is the form Lean's generated equation lemmas have, so
    it is the lemma a mechanical faithfulness proof would use. -/
theorem Term.fixFun_eq_of_equation (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (f : Env ps → τ.den)
    (h : Term.Descends measure body δ γ ρ)
    (hf : ∀ as : Env ps, body.eval δ (as.append γ) (.cons f ρ) = f as) (args : Env ps) :
    Term.fixFun measure body stuck δ γ ρ args = f args :=
  Lex.guardedFix_eq_of_fixpoint _ _ _ h f hf args

/-- **A one-component measure descends**, stated in `Nat`.  The companion of
    `Term.fix_implements_measure`: the obligation is phrased with `<` on the measure's
    value rather than with `Lex.NatVec.Lt`, which is the form a proof about a
    single-component recursion wants. -/
theorem Term.descends_of_measure1 (measure : Term Sg (ps ++ Γ) Ρ (.prim .nat))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (m : Env ps → Nat)
    (hm : ∀ as : Env ps, measure.eval δ (as.append γ) ρ = m as)
    (h : ∀ (as : Env ps) (g₁ g₂ : Env ps → τ.den),
      (∀ bs : Env ps, m bs < m as → g₁ bs = g₂ bs) →
      body.eval δ (as.append γ) (.cons g₁ ρ) = body.eval δ (as.append γ) (.cons g₂ ρ)) :
    Term.Descends (Term.measure1 measure) body δ γ ρ := by
  intro as g₁ g₂ hg
  refine h as g₁ g₂ (fun bs hbs => hg bs ?_)
  show Lex.NatVec.Lt
    (Lex.NatVec.cons (show Nat from measure.eval δ (bs.append γ) ρ) .nil)
    (Lex.NatVec.cons (show Nat from measure.eval δ (as.append γ) ρ) .nil)
  rw [hm as, hm bs]
  exact (Lex.NatVec.lt_one_iff _ _).mpr hbs

/-- The closed case of `Term.fixFun_eq_of_equation`, packaged as `Term.Implements`: a
    translated top-level recursion that descends and whose body matches the Lean
    declaration's equation computes that declaration. -/
theorem Term.fix_implements_of_equation (measure : Spine Sg (ps ++ []) [] (Ty.nats k))
    (body : Term Sg (ps ++ []) [⟨ps, τ⟩] τ) (stuck : Term Sg (ps ++ []) [] τ)
    (δ : GEnv Sg.decls) (f : Env ps → τ.den)
    (h : Term.Descends measure body δ .nil .nil)
    (hf : ∀ as : Env ps, body.eval δ (as.append .nil) (.cons f .nil) = f as) :
    (Term.fix (Γ := []) ps k measure body stuck).Implements δ f := by
  intro args
  show Env.apply ((Term.fix (Γ := []) ps k measure body stuck).eval δ .nil .nil) args
      = f args
  rw [Term.apply_eval_fix]
  exact Term.fixFun_eq_of_equation measure body stuck δ .nil .nil f h hf args

end LakeJs.Expr

end
