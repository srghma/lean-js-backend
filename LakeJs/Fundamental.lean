module

public import LakeJs.Reducibility

@[expose] public section

/-!
# The fundamental theorem of the logical relation

`LakeJs.Reducibility` says what it is for a closed term to be *reducible* and shows that
every construct of the fragment preserves reducibility.  What is left is the induction
that puts those together: **a term of the fragment is reducible under any reducible
substitution**.

A substitution is reducible (`RedSub`) when it gives every variable a reducible answer.
The empty context has no variables, so the empty substitution is reducible for nothing at
all — and a closed term substituted by it is itself.  That is how `LakeJs.TermTotal` gets
from here to *a closed term of the fragment runs out of steps*.

The one place the substitution changes is under a binder: the body of a `Term.lam` and of
a `Term.letE` is substituted by the environment carried under the binder, and then the
bound variable is replaced by the argument.  `Term.subst0_subst_lift` says those two are
one substitution, the environment extended by the argument — which is reducible as soon
as the argument is.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Reducible substitutions -/

/-- **A reducible substitution**: it gives every variable a reducible *answer*.  The
    answer part is what a call-by-value β step puts into the body, so it is what the
    induction has to carry. -/
def RedSub {Γ : Ctx} (γ : VSub Sg Γ []) : Prop :=
  ∀ {σ : Ty} (v : Γ ∋ σ), Value (γ v) ∧ Red σ (γ v)

/-- The empty substitution is reducible: there is no variable to give anything to. -/
theorem RedSub.nil : RedSub (Sg := Sg) (Γ := []) VSub.id := fun v => nomatch v

/-- **Extending a reducible substitution by a reducible answer keeps it reducible.** -/
theorem RedSub.cons {Γ : Ctx} {σ : Ty} {γ : VSub Sg Γ []} {a : Term Sg [] σ}
    (hva : Value a) (ha : Red σ a) (hγ : RedSub γ) : RedSub (VSub.cons a γ) := by
  intro ν v
  match v with
  | .head => exact ⟨hva, ha⟩
  | .tail v => exact hγ v

/-! ## Two small facts -/

/-- A function of the runtime standing on its own, as a computed test.  Stating the
    next lemma through it is what lets it be proved by a case analysis on the δ-redex
    judgement, whose term index is then a variable. -/
def Term.isBareExtern {Γ : Ctx} {τ : Ty} : Term Sg Γ τ → Bool
  | .extern _ => true
  | _ => false

/-- A δ-redex is not a bare function of the runtime: the only rule that would make one is
    `DeltaRedex.const`, and `LeanInitPureExternLazy` has no entry. -/
theorem DeltaRedex.not_bareExtern {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ}
    (h : DeltaRedex t) : t.isBareExtern = false := by
  cases h with
  | const e => exact nomatch e
  | prim1 _ _ => rfl
  | prim2 _ _ _ => rfl
  | prim3 _ _ _ _ => rfl
  | prim5 _ _ _ _ _ _ => rfl
  | quick => rfl

/-- **A function of the runtime on its own is not a δ-redex**, so it is an answer. -/
theorem not_deltaRedex_extern {Γ : Ctx} {σs : List Ty} {τ : Ty} (e : Externs σs τ) :
    ¬ DeltaRedex (Term.extern (Sg := Sg) (Γ := Γ) e) := fun hd => by
  simpa [Term.isBareExtern] using hd.not_bareExtern

/-! ## The fundamental theorem -/

mutual

/-- **A term of the fragment is reducible under any reducible substitution.** -/
theorem Term.fundamental {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) (γ : VSub Sg Γ [])
    (hγ : RedSub γ) (hs : t.simple = true) : Red τ (t.subst γ) :=
  match t, hs with
  | .var v, _ => (hγ v).2
  | .lam b, hs => by
      simp only [Term.simple] at hs
      simp only [Term.subst]
      refine Red.lam fun a hva ha => ?_
      rw [Term.subst0_subst_lift]
      exact Term.fundamental b _ (RedSub.cons hva ha hγ) hs
  | .ap f a, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      exact Red.app (Term.fundamental f γ hγ hs.1) (Term.fundamental a γ hγ hs.2)
  | .lit l, _ => Red.of_ground rfl (Value.lit l).sn
  | .global r, _ => Red.neutral (.global r)
  | .extern e, _ => Red.neutral (.extern e (not_deltaRedex_extern e))
  | .lazyMk e, hs => by
      simp only [Term.simple] at hs
      exact Red.lazyMk (Term.fundamental e γ hγ hs)
  | .lazyForce e, hs => by
      simp only [Term.simple] at hs
      exact Red.lazyForce (Term.fundamental e γ hγ hs)
  | .letE e b, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      simp only [Term.subst]
      refine Red.letE (Term.fundamental e γ hγ hs.1) fun a hva ha => ?_
      rw [Term.subst0_subst_lift]
      exact Term.fundamental b _ (RedSub.cons hva ha hγ) hs.2
  | .ite c t e, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      exact Red.ite (Term.fundamental c γ hγ hs.1.1) (Term.fundamental t γ hγ hs.1.2)
        (Term.fundamental e γ hγ hs.2)
  | .ctor _ _ _ args, hs => by
      simp only [Term.simple] at hs
      exact Red.ctor (Spine.fundamental args γ hγ hs)
  | .proj e _ _ _ _, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      exact Red.proj hs.1 (Term.fundamental e γ hγ hs.2)
  | .tagOf e _, hs => by
      simp only [Term.simple] at hs
      exact Red.tagOf (Term.fundamental e γ hγ hs)
  | .caseTag e alts _, hs => by
      simp only [Term.simple, Bool.and_eq_true] at hs
      exact Red.caseTag (Term.fundamental e γ hγ hs.1) (Alts.fundamental alts γ hγ hs.2)
  | .block _, hs => by simp [Term.simple] at hs
  termination_by sizeOf t

/-- **A spine of the fragment is reducible under any reducible substitution.** -/
theorem Spine.fundamental {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs)
    (γ : VSub Sg Γ []) (hγ : RedSub γ) (hs : s.simple = true) : SpineRed (s.subst γ) :=
  match s, hs with
  | .nil, _ => trivial
  | .cons t rest, hs => by
      simp only [Spine.simple, Bool.and_eq_true] at hs
      exact ⟨Term.fundamental t γ hγ hs.1, Spine.fundamental rest γ hγ hs.2⟩
  termination_by sizeOf s

/-- **Every branch of a dispatch of the fragment is reducible under any reducible
    substitution.** -/
theorem Alts.fundamental {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool}
    (alts : Alts Sg Γ τ tags full) (γ : VSub Sg Γ []) (hγ : RedSub γ)
    (hs : alts.simple = true) : RedAlts (alts.subst γ) :=
  match alts, hs with
  | .deflt t, hs => by
      simp only [Alts.simple] at hs
      exact Term.fundamental t γ hγ hs
  | .nilFull, _ => trivial
  | .cons _ t rest, hs => by
      simp only [Alts.simple, Bool.and_eq_true] at hs
      exact ⟨Term.fundamental t γ hγ hs.1, Alts.fundamental rest γ hγ hs.2⟩
  termination_by sizeOf alts

end

end LakeJs.Expr

end
