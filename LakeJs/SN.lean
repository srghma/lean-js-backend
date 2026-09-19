module

public import LakeJs.Progress

@[expose] public section

set_option autoImplicit false

/-!
# Normalisation, by construction — and how to reason about a recursion

This module used to be the elementary half of a totality *proof*: `Term.SN t` said that
every reduction sequence from `t` is finite, and the rest of the development
(`LakeJs.Reducibility`, `LakeJs.Fundamental`, `LakeJs.TermTotal`) worked towards showing
that a certified term is `SN`.  That shape of argument belonged to a grammar in which a
term could fail to stop.

There is no such term now.  Running a term is `Term.eval`, an ordinary structurally
recursive Lean function, so "every term runs out of steps" is not a theorem about a
relation but the fact that the definition elaborates.  What is left to say is
**how to reason about the one construct that repeats work**, and that is what this module
provides:

* `Term.fixFun_eq_body` is the one equation of the recursion — the body, run with a
  guarded self-reference.  This is what a proof that a term computes the Lean function it
  was translated from starts with, together with the well-founded induction on the measure
  that `Term.fixFun_eq_of_descends` (in `LakeJs.Reducibility`) packages;
* `Term.fixFun_not_descending` says the body is not consulted by a call that does not
  descend — the seal, read from the semantics' side;
* `Term.eval_unique` is the uniqueness half of "one answer, always".
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {ps : List Ty} {τ : Ty}

/-- **The one equation of the recursion.**  The recursion is its body, run with a
    self-reference that is the recursion itself at every strictly smaller measure and
    `stuck` at everything else.  This is what a proof about a recursion starts from; there
    is no second equation, and no base case, because there is no counter. -/
theorem Term.fixFun_eq_body {k : Nat} (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (args : Env ps) :
    Term.fixFun measure body stuck δ γ ρ args =
      body.eval δ (args.append γ)
        (.cons (fun bs =>
            if (Term.measureVal measure δ γ ρ bs).lt (Term.measureVal measure δ γ ρ args)
            then Term.fixFun measure body stuck δ γ ρ bs
            else stuck.eval δ (bs.append γ) ρ) ρ) :=
  Term.fixFun_unfold measure body stuck δ γ ρ args

/-- **The seal, read from the semantics' side.**  Two recursions with the same measure and
    the same `stuck` branch answer alike at every call that does not descend, however
    different their bodies are: a call that does not descend never reaches a body. -/
theorem Term.fixFun_not_descending {k : Nat} (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body body' : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (args bs : Env ps)
    (h : ¬ Lex.NatVec.Lt (Term.measureVal measure δ γ ρ bs)
            (Term.measureVal measure δ γ ρ args)) :
    (if (Term.measureVal measure δ γ ρ bs).lt (Term.measureVal measure δ γ ρ args)
     then Term.fixFun measure body stuck δ γ ρ bs
     else stuck.eval δ (bs.append γ) ρ)
      = (if (Term.measureVal measure δ γ ρ bs).lt (Term.measureVal measure δ γ ρ args)
         then Term.fixFun measure body' stuck δ γ ρ bs
         else stuck.eval δ (bs.append γ) ρ) := by
  rw [Term.fixFun_stuck_of_not_lt measure body stuck δ γ ρ args bs h,
    Term.fixFun_stuck_of_not_lt measure body' stuck δ γ ρ args bs h]

/-- **One answer, always.**  The evaluator is a function, so a term has exactly one
    value; this is the statement the old `SN`-plus-confluence development was working
    towards. -/
theorem Term.eval_unique (t : Term Sg Γ Ρ τ) (δ : GEnv Sg.decls) (γ : Env Γ)
    (ρ : REnv Ρ) {v w : τ.den} (hv : t.eval δ γ ρ = v) (hw : t.eval δ γ ρ = w) :
    v = w := by
  rw [← hv, ← hw]

/-- **A closed term normalises**: it has a value, and only one. -/
theorem Term.normalises (t : Term Sg [] [] τ) (δ : GEnv Sg.decls) :
    ∃ v : τ.den, t.evalClosed δ = v ∧ ∀ w : τ.den, t.evalClosed δ = w → w = v :=
  ⟨t.evalClosed δ, rfl, fun _ h => h.symm⟩

end LakeJs.Expr

end
