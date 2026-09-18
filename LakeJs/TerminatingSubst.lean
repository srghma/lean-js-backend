module

public import LakeJs.Terminating

@[expose] public section

/-!
# The certificate survives renaming and copying a variable

A block's certificate (`Tail.Certified`) quantifies over the *closing substitutions* the
enclosing context can supply.  That is what makes it stable under the operations the
reduction of a block performs on the terms it contains, and this module proves the two
stability properties the certificate generators of `LakeJs.CertGen` need:

* **renaming** — a certified term stays certified when its variables are renamed
  (`Term.terminating_rename`).  The reason is one line of substitution algebra: renaming
  and then closing is closing by the composite, and a reducible closing substitution
  composed with a renaming is reducible again;

* **copying an atomic term** — a certified term stays certified when a variable is
  replaced by a *variable or a literal* (`Term.terminating_subst_atomic`).  An atomic
  term closes to an answer, which is exactly what makes the composite substitution
  reducible again, and that is what fails for an arbitrary term.

A general substitution — one that may put an arbitrary *computation* under a binder —
does **not** preserve the certificate, and should not: the logical relation is about
closing by answers, and call-by-value never substitutes anything else.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Atomic terms and atomic substitutions -/

/-- **A term that may be copied freely**: a variable or a literal.  This is the `Prop`
    counterpart of `Term.atomic?`. -/
inductive Term.Atomic {Γ : Ctx} : ∀ {τ : Ty}, Term Sg Γ τ → Prop
  | var {τ : Ty} (v : Γ ∋ τ) : Term.Atomic (.var v)
  | lit {p : LeanPrimTy} (l : LeanPrimLit p) : Term.Atomic (.lit l)

/-- An atomic term stays atomic when its variables are renamed. -/
theorem Term.Atomic.rename {Γ₁ Γ₂ : Ctx} {τ : Ty} {t : Term Sg Γ₁ τ} (h : t.Atomic)
    (ρ : VRen Γ₁ Γ₂) : (t.rename ρ).Atomic := by
  cases h with
  | var v => exact .var (ρ v)
  | lit l => exact .lit l

/-- **A substitution that only copies**: every variable goes to a variable or a
    literal. -/
def VSub.Atomic {Γ₁ Γ₂ : Ctx} (θ : VSub Sg Γ₁ Γ₂) : Prop :=
  ∀ {σ : Ty} (v : Γ₁ ∋ σ), (θ v).Atomic

/-- An atomic term is certified: there is nothing in it to certify. -/
theorem Term.Atomic.terminating {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ} (h : t.Atomic) :
    t.Terminating := by
  cases h with
  | var _ => exact trivial
  | lit _ => exact trivial

/-- **An atomic term closes to a reducible answer.**  A variable goes to what the
    substitution gives it, and a literal is already one. -/
theorem Term.Atomic.red_subst {Γ : Ctx} {σ : Ty} {a : Term Sg Γ σ} (h : a.Atomic)
    {γ : VSub Sg Γ []} (hγ : RedSub γ) : Value (a.subst γ) ∧ Red σ (a.subst γ) := by
  cases h with
  | var w => exact hγ w
  | lit l => exact ⟨Value.lit l, Red.of_ground rfl (Value.lit l).sn⟩

/-- Carrying an atomic substitution under a binder keeps it atomic. -/
theorem VSub.Atomic.lift {Γ₁ Γ₂ : Ctx} {σ : Ty} {θ : VSub Sg Γ₁ Γ₂} (h : VSub.Atomic θ) :
    VSub.Atomic (VSub.lift (σ := σ) θ) := by
  intro ν v
  match v with
  | .head => exact .var .head
  | .tail v => exact (h v).rename VRen.weaken

/-- Carrying an atomic substitution under a binder that binds a whole list keeps it
    atomic. -/
theorem VSub.Atomic.liftList {Γ₁ Γ₂ : Ctx} {θ : VSub Sg Γ₁ Γ₂} (h : VSub.Atomic θ) :
    ∀ (σs : List Ty), VSub.Atomic (VSub.liftList σs θ)
  | [] => h
  | _ :: σs => VSub.Atomic.lift (h.liftList σs)

/-- The substitution that replaces the innermost variable by an atomic term is
    atomic. -/
theorem VSub.Atomic.zero {Γ : Ctx} {σ : Ty} {a : Term Sg Γ σ} (h : a.Atomic) :
    VSub.Atomic (VSub.zero a) := by
  intro ν v
  match v with
  | .head => exact h
  | .tail v => exact .var v

/-! ## A reducible substitution, composed -/

/-- **A reducible closing substitution composed with a renaming is reducible.** -/
theorem RedSub.comp_ren {Γ₁ Γ₂ : Ctx} {ρ : VRen Γ₁ Γ₂} {γ : VSub Sg Γ₂ []}
    (hγ : RedSub γ) : RedSub (fun {_} v => γ (ρ v)) :=
  fun v => hγ (ρ v)

/-- **An atomic substitution followed by a reducible closing substitution is reducible.**
    An atomic term closes to a variable's answer or to a literal, and both are reducible
    answers. -/
theorem RedSub.comp_atomic {Γ₁ Γ₂ : Ctx} {θ : VSub Sg Γ₁ Γ₂} {γ : VSub Sg Γ₂ []}
    (hθ : VSub.Atomic θ) (hγ : RedSub γ) : RedSub (fun {_} v => (θ v).subst γ) :=
  fun v => (hθ v).red_subst hγ

/-! ## The certificate itself -/

/-- **A certified block stays certified when its variables are renamed.** -/
theorem Tail.Certified.rename {Γ₁ Γ₂ : Ctx} {τ : Ty} {b : Tail Sg Γ₁ [] τ}
    (h : b.Certified) (ρ : VRen Γ₁ Γ₂) : (b.rename ρ LRen.id).Certified := by
  intro γ hγ
  have heq : (b.rename ρ LRen.id).subst γ = b.subst (fun {_} v => γ (ρ v)) := by
    rw [Tail.subst_rename b (ρ := ρ) (κ := LRen.id) (θ := γ)
      (θ'' := fun {_} v => γ (ρ v)) (ρ₀ := VRen.id) (fun _ => rfl) (fun _ => rfl)]
    exact Tail.rename_eq_self _ (fun _ => rfl) (fun _ => rfl)
  rw [heq]
  exact h _ hγ.comp_ren

/-- **A certified block stays certified when a variable is replaced by an atomic
    term.** -/
theorem Tail.Certified.subst_atomic {Γ₁ Γ₂ : Ctx} {τ : Ty} {b : Tail Sg Γ₁ [] τ}
    (h : b.Certified) {θ : VSub Sg Γ₁ Γ₂} (hθ : VSub.Atomic θ) :
    (b.subst θ).Certified := by
  intro γ hγ
  rw [b.subst_subst (θ := θ) (θ' := γ) (θ'' := fun {_} v => (θ v).subst γ)
    (fun _ => rfl)]
  exact h _ (RedSub.comp_atomic hθ hγ)

/-! ## The certified language is closed under both -/

mutual

/-- **A certified term stays certified when its variables are renamed.** -/
theorem Term.terminating_rename {Γ₁ Γ₂ : Ctx} {τ : Ty} (t : Term Sg Γ₁ τ)
    (ρ : VRen Γ₁ Γ₂) (h : t.Terminating) : (t.rename ρ).Terminating :=
  match t, h with
  | .var _, _ => trivial
  | .lam b, h => Term.terminating_rename b ρ.lift h
  | .ap f a, h => ⟨Term.terminating_rename f ρ h.1, Term.terminating_rename a ρ h.2⟩
  | .lit _, _ => trivial
  | .global _, _ => trivial
  | .extern _, _ => trivial
  | .lazyMk e, h => Term.terminating_rename e ρ h
  | .lazyForce e, h => Term.terminating_rename e ρ h
  | .letE e b, h => ⟨Term.terminating_rename e ρ h.1, Term.terminating_rename b ρ.lift h.2⟩
  | .ite c t e, h => ⟨Term.terminating_rename c ρ h.1, Term.terminating_rename t ρ h.2.1,
      Term.terminating_rename e ρ h.2.2⟩
  | .ctor _ _ _ args, h => Spine.terminating_rename args ρ h
  | .proj e _ _ _ _, h => ⟨h.1, Term.terminating_rename e ρ h.2⟩
  | .tagOf e _, h => Term.terminating_rename e ρ h
  | .caseTag e alts _, h =>
      ⟨Term.terminating_rename e ρ h.1, Alts.terminating_rename alts ρ h.2⟩
  | .block b, h => ⟨h.1, h.2.rename ρ⟩
  termination_by sizeOf t

/-- **A certified spine stays certified when its variables are renamed.** -/
theorem Spine.terminating_rename {Γ₁ Γ₂ : Ctx} {σs : List Ty} (s : Spine Sg Γ₁ σs)
    (ρ : VRen Γ₁ Γ₂) (h : s.Terminating) : (s.rename ρ).Terminating :=
  match s, h with
  | .nil, _ => trivial
  | .cons t rest, h =>
      ⟨Term.terminating_rename t ρ h.1, Spine.terminating_rename rest ρ h.2⟩
  termination_by sizeOf s

/-- **Certified branches stay certified when their variables are renamed.** -/
theorem Alts.terminating_rename {Γ₁ Γ₂ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool}
    (alts : Alts Sg Γ₁ τ tags full) (ρ : VRen Γ₁ Γ₂) (h : alts.Terminating) :
    (alts.rename ρ).Terminating :=
  match alts, h with
  | .deflt t, h => Term.terminating_rename t ρ h
  | .nilFull, _ => trivial
  | .cons _ t rest, h =>
      ⟨Term.terminating_rename t ρ h.1, Alts.terminating_rename rest ρ h.2⟩
  termination_by sizeOf alts

end

mutual

/-- **A certified term stays certified when a variable is replaced by an atomic
    term.** -/
theorem Term.terminating_subst_atomic {Γ₁ Γ₂ : Ctx} {τ : Ty} (t : Term Sg Γ₁ τ)
    {θ : VSub Sg Γ₁ Γ₂} (hθ : VSub.Atomic θ) (h : t.Terminating) :
    (t.subst θ).Terminating :=
  match t, h with
  | .var v, _ => (hθ v).terminating
  | .lam b, h => Term.terminating_subst_atomic b hθ.lift h
  | .ap f a, h =>
      ⟨Term.terminating_subst_atomic f hθ h.1, Term.terminating_subst_atomic a hθ h.2⟩
  | .lit _, _ => trivial
  | .global _, _ => trivial
  | .extern _, _ => trivial
  | .lazyMk e, h => Term.terminating_subst_atomic e hθ h
  | .lazyForce e, h => Term.terminating_subst_atomic e hθ h
  | .letE e b, h =>
      ⟨Term.terminating_subst_atomic e hθ h.1,
        Term.terminating_subst_atomic b hθ.lift h.2⟩
  | .ite c t e, h =>
      ⟨Term.terminating_subst_atomic c hθ h.1, Term.terminating_subst_atomic t hθ h.2.1,
        Term.terminating_subst_atomic e hθ h.2.2⟩
  | .ctor _ _ _ args, h => Spine.terminating_subst_atomic args hθ h
  | .proj e _ _ _ _, h => ⟨h.1, Term.terminating_subst_atomic e hθ h.2⟩
  | .tagOf e _, h => Term.terminating_subst_atomic e hθ h
  | .caseTag e alts _, h =>
      ⟨Term.terminating_subst_atomic e hθ h.1, Alts.terminating_subst_atomic alts hθ h.2⟩
  | .block b, h => ⟨h.1, h.2.subst_atomic hθ⟩
  termination_by sizeOf t

/-- **A certified spine stays certified when a variable is replaced by an atomic
    term.** -/
theorem Spine.terminating_subst_atomic {Γ₁ Γ₂ : Ctx} {σs : List Ty} (s : Spine Sg Γ₁ σs)
    {θ : VSub Sg Γ₁ Γ₂} (hθ : VSub.Atomic θ) (h : s.Terminating) :
    (s.subst θ).Terminating :=
  match s, h with
  | .nil, _ => trivial
  | .cons t rest, h =>
      ⟨Term.terminating_subst_atomic t hθ h.1, Spine.terminating_subst_atomic rest hθ h.2⟩
  termination_by sizeOf s

/-- **Certified branches stay certified when a variable is replaced by an atomic
    term.** -/
theorem Alts.terminating_subst_atomic {Γ₁ Γ₂ : Ctx} {τ : Ty} {tags : List Nat}
    {full : Bool} (alts : Alts Sg Γ₁ τ tags full) {θ : VSub Sg Γ₁ Γ₂}
    (hθ : VSub.Atomic θ)
    (h : alts.Terminating) : (alts.subst θ).Terminating :=
  match alts, h with
  | .deflt t, h => Term.terminating_subst_atomic t hθ h
  | .nilFull, _ => trivial
  | .cons _ t rest, h =>
      ⟨Term.terminating_subst_atomic t hθ h.1, Alts.terminating_subst_atomic rest hθ h.2⟩
  termination_by sizeOf alts

end

end LakeJs.Expr

end
