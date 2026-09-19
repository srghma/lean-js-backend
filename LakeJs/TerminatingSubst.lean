module

public import LakeJs.Terminating
public import LakeJs.SubstLemmas
public import LakeJs.LSubstLemmas

@[expose] public section

set_option autoImplicit false

/-!
# Termination is stable under the operations a pass performs

This file used to show that the old certificate — the object that licensed running a term
— survived renaming, weakening and substitution, so that a compiler pass could rewrite a
certified term and still hand the result to the evaluator.

There is no certificate any more: every term of the one grammar terminates
(`LakeJs.Terminating`).  What a pass now has to be told is the stronger statement that
replaced it — not merely *the rewritten term still answers*, but **it answers the same
thing**.  That is what this file collects, as corollaries of `LakeJs.SubstLemmas` and
`LakeJs.LSubstLemmas`:

* `Term.terminating_rename` — a renaming moves the value along, unchanged;
* `Term.value_weaken`, `Term.value_rweaken` — a variable, or a recursion, that a weakening
  adds is not read;
* `Tail.terminating_lsubst0` — inlining a join point keeps the value;
* `Term.Implements.congr` — and therefore a pass that preserves values preserves
  faithfulness to the Lean function the term was translated from.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {ps : List Ty} {σ τ : Ty}

/-- **Renaming moves the value along.**  Under environments that agree along the renaming,
    the renamed term answers exactly what the original one does — so it terminates, and
    with the same value. -/
theorem Term.terminating_rename {Γ₁ Γ₂ : Ctx} {Ρ₁ Ρ₂ : RCtx} (t : Term Sg Γ₁ Ρ₁ τ)
    (ρv : VRen Γ₁ Γ₂) (ξ : RRen Ρ₁ Ρ₂) (δ : GEnv Sg.decls) (γ₁ : Env Γ₁) (γ₂ : Env Γ₂)
    (ρ₁ : REnv Ρ₁) (ρ₂ : REnv Ρ₂) (hγ : Env.Agree ρv γ₁ γ₂) (hρ : REnv.Agree ξ ρ₁ ρ₂) :
    ∃ v : τ.den, (t.rename ρv ξ).eval δ γ₂ ρ₂ = v ∧ t.eval δ γ₁ ρ₁ = v :=
  ⟨t.eval δ γ₁ ρ₁, Term.eval_rename t ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ, rfl⟩

/-- The value of a weakened term: the variable the weakening added is not read. -/
theorem Term.value_weaken (t : Term Sg Γ Ρ τ) (δ : GEnv Sg.decls) (a : σ.den)
    (γ : Env Γ) (ρ : REnv Ρ) :
    (Term.weaken (σ := σ) t).eval δ (.cons a γ) ρ = t.eval δ γ ρ :=
  Term.eval_weaken t δ a γ ρ

/-- The value of a recursion-weakened term: the recursion the weakening added cannot be
    called. -/
theorem Term.value_rweaken {r : RSig} (t : Term Sg Γ Ρ τ) (δ : GEnv Sg.decls) (γ : Env Γ)
    (f : Env r.ps → r.ret.den) (ρ : REnv Ρ) :
    (Term.rweaken (r := r) t).eval δ γ (.cons f ρ) = t.eval δ γ ρ :=
  Term.eval_rweaken t δ γ f ρ

/-- **Inlining a join point keeps the value.**  The one label former of the grammar can be
    eliminated by a pass without changing what the block answers. -/
theorem Tail.terminating_lsubst0 (rest : Tail Sg Γ (ps :: Ω) Ρ τ)
    (jb : Tail Sg (ps ++ Γ) Ω Ρ τ) (δ : GEnv Sg.decls) (γ : Env Γ) (lenv : LEnv τ Ω)
    (ρ : REnv Ρ) :
    ∃ v : τ.den, (rest.lsubst0 jb).eval δ γ lenv ρ = v ∧
      (Tail.join ps jb rest).eval δ γ lenv ρ = v :=
  ⟨(Tail.join ps jb rest).eval δ γ lenv ρ,
    Tail.eval_lsubst0 rest jb δ γ lenv ρ, rfl⟩

/-- **A value-preserving rewrite preserves faithfulness.**  If two closed terms answer the
    same, and one implements a Lean function, so does the other. -/
theorem Term.Implements.congr {t t' : Term Sg [] [] (Ty.arrows ps τ)}
    {δ : GEnv Sg.decls} {f : Env ps → τ.den}
    (h : t.Implements δ f) (he : t'.evalClosed δ = t.evalClosed δ) :
    t'.Implements δ f := by
  intro args
  rw [he]
  exact h args

end LakeJs.Expr

end
