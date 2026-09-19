module

public import LakeJs.Reducibility
public import LakeJs.Diverge

@[expose] public section

set_option autoImplicit false

/-!
# Termination, and why it is no longer a hypothesis

This file used to define what it means for a term to *carry a certificate*: the old
grammar had an unrestricted loop, so an evaluator could only be a function on the
sub-language of terms whose loops had been certified, and every downstream theorem was
conditional on such a certificate.

In the one grammar there is nothing to certify.  Repeating work is `Term.fix`, which
carries its own measure, and the only other label former is `Tail.join`, whose body is typed
in the *outer* label context and therefore cannot jump back to itself.  So
`LakeJs.Reduce`'s evaluator is an ordinary structurally recursive Lean function, and
termination is a theorem about *every* term rather than a hypothesis about some of them.

`Term.Terminating` and `Tail.Terminating` name the property; `Term.terminating` and
`Tail.terminating` prove it for every term and every tail, with no side conditions.  The
old API's certificate argument survives as `Term.cert`, which manufactures one for
anything, so a caller that used to have to produce a certificate now cannot fail to.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {ps : List Ty} {τ : Ty}

/-- A term **terminates** when it has a value in every environment. -/
def Term.Terminating (t : Term Sg Γ Ρ τ) : Prop :=
  ∀ (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ), ∃ v : τ.den, t.eval δ γ ρ = v

/-- A tail **terminates** when it has a value in every environment, including every
    assignment of values to the join points in scope. -/
def Tail.Terminating (b : Tail Sg Γ Ω Ρ τ) : Prop :=
  ∀ (δ : GEnv Sg.decls) (γ : Env Γ) (lenv : LEnv τ Ω) (ρ : REnv Ρ),
    ∃ v : τ.den, b.eval δ γ lenv ρ = v

/-- **Every term terminates.**  There is no fragment and no certificate: the witness is
    the value that `Term.eval` — a total Lean function — computes. -/
theorem Term.terminating (t : Term Sg Γ Ρ τ) : t.Terminating :=
  fun δ γ ρ => ⟨t.eval δ γ ρ, rfl⟩

/-- **Every tail terminates**, for the same reason. -/
theorem Tail.terminating (b : Tail Sg Γ Ω Ρ τ) : b.Terminating :=
  fun δ γ lenv ρ => ⟨b.eval δ γ lenv ρ, rfl⟩

/-- The old certificate argument, manufactured.  A front end that used to have to justify
    a loop before it could hand a term to the evaluator now calls this. -/
theorem Term.cert (t : Term Sg Γ Ρ τ) : t.Terminating := t.terminating

/-- Termination of a closed term, stated at `Term.evalClosed`: this is the form the
    top-level runner needs. -/
theorem Term.terminating_closed (t : Term Sg [] [] τ) (δ : GEnv Sg.decls) :
    ∃ v : τ.den, t.evalClosed δ = v :=
  t.terminating δ .nil .nil

/-- The witness is the value, so termination says exactly what the evaluator answers. -/
theorem Term.eq_of_terminating (t : Term Sg Γ Ρ τ) (δ : GEnv Sg.decls) (γ : Env Γ)
    (ρ : REnv Ρ) {v : τ.den} (h : t.eval δ γ ρ = v) : t.eval δ γ ρ = v := h

/-- The shape that used to need a certificate — and used not to have one — terminates
    like everything else. -/
example : spinTerm (Sg := ⟨[], by decide⟩).Terminating := Term.terminating _

/-- And its value at a concrete argument is a numeral the kernel computes. -/
example : Term.runNat1 spinTerm 12 = 7 := rfl

end LakeJs.Expr

end
