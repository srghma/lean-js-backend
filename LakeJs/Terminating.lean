module

public import LakeJs.Reducibility

@[expose] public section

/-!
# `Term.Terminating`: the certified language

`LakeJs.Fragment` carves out `Term.simple`, the *decidable* fragment the evaluator is
total on: it throws away the whole block grammar, because a self-`Tail.label` is the one
construct that repeats work and `LakeJs.Diverge` shows a block that never answers.  That
restriction is too blunt — a compiled Lean function is a loop, and a loop is a block.

This module implements **design D2 of `TERMINATING_TERM_ASSESSMENT.md`**: the language is
left alone and a *certificate* is attached to the term.

* `Tail.Certified b` is the certificate of a block: **whatever closed values the
  enclosing context supplies, the block runs out of steps.**  Three properties of that
  shape, all of them deliberate:

  1. it **quantifies over closing environments** (§4.2(1) of the assessment), so it
     survives the substitution a β step performs — which is exactly what the fundamental
     theorem needs of it;
  2. it is a `Prop`, so it is **erased**: the emitted code is the same loop, and nothing
     is paid at run time;
  3. it is **not decidable**, and by the diagonal argument of §2 of the assessment no
     sound *and* complete criterion could be.  Certificates are produced, not checked:
     `LakeJs.CertGen` derives them mechanically for the shapes that admit it, and the
     general case transports the termination proof the source function already has.

* `Term.Terminating t` is `Term.simple` with the block case replaced by "the block is
  certified, and it answers at a value type".  It is a `Prop` rather than a `Bool`
  precisely because of point 3.

* `CertifiedTerm Sg Γ τ` packages a term with its certificate: the *program* is the
  certified object, so `SnapshotsPBOPartial` — which contains genuinely `partial` Lean
  functions, and must stay expressible — keeps the uncertified path.

`LakeJs.Fundamental` extends the logical relation to it, and `LakeJs.TermTotal` draws the
conclusion: a closed certified term runs out of steps, reaches an answer, and the
fuel-free evaluator computes it.

## What a certified block may answer with

A certified block is required to answer at a **value type** (`Ty.ground`): a block whose
answer is itself a function is outside the guarantee, for the same reason a field read at
a function type is (`LakeJs.Fragment`) — the logical relation would have to hold
hereditarily of what comes out of a block, and that is the hereditary-reducibility step
of the assessment (§4.3(3)), which is not implemented.  Every root of a compiled module
answers with data, so nothing in the corpus is lost.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## The certificate of a block -/

/-- **The termination certificate of a block.**  For every reducible closing
    substitution — every way the enclosing context can supply closed, reducible answers
    for the variables the block reads — the block runs out of steps.

    Quantifying over the substitution rather than fixing one is what makes the
    certificate stable under β: when the block sits under a binder and an argument is
    substituted into it, the certificate still speaks about the result. -/
def Tail.Certified {Γ : Ctx} {τ : Ty} (b : Tail Sg Γ [] τ) : Prop :=
  ∀ γ : VSub Sg Γ [], RedSub γ → (Term.block (b.subst γ)).SN

/-- A certificate for a closed block says what it should: the block runs out of steps. -/
theorem Tail.Certified.sn_closed {τ : Ty} {b : Tail Sg [] [] τ} (h : b.Certified) :
    (Term.block b).SN := by
  have := h VSub.id RedSub.nil
  rwa [Tail.subst_id] at this

/-! ## The certified language -/

mutual

/-- **Is this term certified to terminate?**  `Term.simple`, with the block case replaced
    by a certificate instead of an outright refusal. -/
def Term.Terminating {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Prop
  | _, _, .var _ => True
  | _, _, .lam b => b.Terminating
  | _, _, .ap f a => f.Terminating ∧ a.Terminating
  | _, _, .lit _ => True
  | _, _, .global _ => True
  | _, _, .extern _ => True
  | _, _, .lazyMk e => e.Terminating
  | _, _, .lazyForce e => e.Terminating
  | _, _, .letE e b => e.Terminating ∧ b.Terminating
  | _, _, .ite c t e => c.Terminating ∧ t.Terminating ∧ e.Terminating
  | _, _, .ctor _ _ _ args => args.Terminating
  | _, _, .proj (τ := τ) e _ _ _ _ => τ.ground = true ∧ e.Terminating
  | _, _, .tagOf e _ => e.Terminating
  | _, _, .caseTag e alts _ => e.Terminating ∧ alts.Terminating
  | _, τ, .block b => τ.ground = true ∧ b.Certified

/-- Is every term of this spine certified? -/
def Spine.Terminating {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Prop
  | _, _, .nil => True
  | _, _, .cons t rest => t.Terminating ∧ rest.Terminating

/-- Is every branch of this dispatch certified? -/
def Alts.Terminating {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ τ tags full → Prop
  | _, _, _, _, .deflt t => t.Terminating
  | _, _, _, _, .nilFull => True
  | _, _, _, _, .cons _ t rest => t.Terminating ∧ rest.Terminating

end

/-- **A term with its certificate.**  This is the certified object the program level is
    built out of: a `Term` need not terminate — `SnapshotsPBOPartial` has Lean functions
    that do not — but a `CertifiedTerm` does. -/
structure CertifiedTerm (Sg : Sig) (Γ : Ctx) (τ : Ty) where
  /-- The term. -/
  term : Term Sg Γ τ
  /-- Its termination certificate. -/
  cert : term.Terminating

/-! ## The decidable fragment is certified

`Term.simple` is the *block-free* fragment, so its certificate is vacuous: there is no
block to certify.  Everything proved about `Term.simple` is therefore a special case of
what is proved about `Term.Terminating`. -/

mutual

/-- **A term of the decidable fragment is certified.** -/
theorem Term.terminating_of_simple {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ)
    (hs : t.simple = true) : t.Terminating :=
  match t, hs with
  | .var _, _ => trivial
  | .lam b, hs => by
      simp only [Term.simple] at hs
      exact Term.terminating_of_simple b hs
  | .ap f a, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      exact ⟨Term.terminating_of_simple f hs.1, Term.terminating_of_simple a hs.2⟩
  | .lit _, _ => trivial
  | .global _, _ => trivial
  | .extern _, _ => trivial
  | .lazyMk e, hs => by
      simp only [Term.simple] at hs
      exact Term.terminating_of_simple e hs
  | .lazyForce e, hs => by
      simp only [Term.simple] at hs
      exact Term.terminating_of_simple e hs
  | .letE e b, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      exact ⟨Term.terminating_of_simple e hs.1, Term.terminating_of_simple b hs.2⟩
  | .ite c t e, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      exact ⟨Term.terminating_of_simple c hs.1.1, Term.terminating_of_simple t hs.1.2,
        Term.terminating_of_simple e hs.2⟩
  | .ctor _ _ _ args, hs => by
      simp only [Term.simple] at hs
      exact Spine.terminating_of_simple args hs
  | .proj e _ _ _ _, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      exact ⟨hs.1, Term.terminating_of_simple e hs.2⟩
  | .tagOf e _, hs => by
      simp only [Term.simple] at hs
      exact Term.terminating_of_simple e hs
  | .caseTag e alts _, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      exact ⟨Term.terminating_of_simple e hs.1, Alts.terminating_of_simple alts hs.2⟩
  | .block _, hs => by simp [Term.simple] at hs
  termination_by sizeOf t

/-- **A spine of the decidable fragment is certified.** -/
theorem Spine.terminating_of_simple {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs)
    (hs : s.simple = true) : s.Terminating :=
  match s, hs with
  | .nil, _ => trivial
  | .cons t rest, hs => by
      simp only [Spine.simple, Bool.and_eq_true] at hs
      exact ⟨Term.terminating_of_simple t hs.1, Spine.terminating_of_simple rest hs.2⟩
  termination_by sizeOf s

/-- **Every branch of a dispatch of the decidable fragment is certified.** -/
theorem Alts.terminating_of_simple {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool}
    (alts : Alts Sg Γ τ tags full) (hs : alts.simple = true) : alts.Terminating :=
  match alts, hs with
  | .deflt t, hs => by
      simp only [Alts.simple] at hs
      exact Term.terminating_of_simple t hs
  | .nilFull, _ => trivial
  | .cons _ t rest, hs => by
      simp only [Alts.simple, Bool.and_eq_true] at hs
      exact ⟨Term.terminating_of_simple t hs.1, Alts.terminating_of_simple rest hs.2⟩
  termination_by sizeOf alts

end

end LakeJs.Expr

end
