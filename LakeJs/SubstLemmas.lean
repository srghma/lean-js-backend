module

public import LakeJs.Subst

@[expose] public section

/-!
# The laws of renaming and substitution

`LakeJs.Subst` defines renaming and substitution; this module proves the equations they
satisfy.  They are the usual four of a de Bruijn presentation — a renaming after a
renaming, a substitution after a renaming, a renaming after a substitution and a
substitution after a substitution are each a single traversal — together with the two
congruences (a traversal only reads its function pointwise) and the two identity laws.

Everything here is proved once for each of the five families of the language (`Term`,
`Spine`, `Alts`, `Tail`, `AltsT`), by the mutual structural recursion they are defined
by.  A `Term` has no labels, so only the two families of the block grammar carry a label
renaming; the lemma for a `Term` carries the renaming `ρ₀` of the statement it shares
with them, which its uses discharge with the identity.

The one consequence the rest of the development uses is `Term.subst0_subst_lift`:
substituting under a binder and then substituting the bound variable is one
substitution — which is what the β rule of `LakeJs.Reduce` needs in order to be read as
an extension of the environment.
-/

namespace LakeJs.Expr

open LakeJs

variable {Sg : Sig}

/-! ## Composing and extending -/

/-- A substitution that gives the variable just bound the term `a`, and every other
    variable what `θ` gives it: the environment `θ` extended by `a`. -/
def VSub.cons {Γ₁ Γ₂ : Ctx} {σ : Ty} (a : Term Sg Γ₂ σ) (θ : VSub Sg Γ₁ Γ₂) :
    VSub Sg (σ :: Γ₁) Γ₂ :=
  fun {_} v =>
    match v with
    | .head => a
    | .tail v => θ v

/-! ## Lifting reads its function pointwise -/

/-- Carrying two pointwise-equal renamings under a binder gives pointwise-equal
    renamings. -/
theorem VRen.lift_congr {Γ₁ Γ₂ : Ctx} {σ : Ty} {ρ ρ' : VRen Γ₁ Γ₂}
    (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), ρ v = ρ' v) :
    ∀ {τ : Ty} (v : (σ :: Γ₁) ∋ τ), VRen.lift ρ v = VRen.lift ρ' v
  | _, .head => rfl
  | _, .tail v => by simp [VRen.lift, h v]

/-- The same, under a binder that binds a whole list. -/
theorem VRen.liftList_congr {Γ₁ Γ₂ : Ctx} {ρ ρ' : VRen Γ₁ Γ₂}
    (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), ρ v = ρ' v) :
    ∀ (σs : List Ty) {τ : Ty} (v : (σs ++ Γ₁) ∋ τ),
      VRen.liftList σs ρ v = VRen.liftList σs ρ' v
  | [], _, v => h v
  | _ :: σs, _, v => VRen.lift_congr (VRen.liftList_congr h σs) v

/-- The same, for renamings of labels. -/
theorem LRen.lift_congr {Ω₁ Ω₂ : LCtx} {ps : List Ty} {κ κ' : LRen Ω₁ Ω₂}
    (h : ∀ {qs : List Ty} (v : Ω₁ ∋ₗ qs), κ v = κ' v) :
    ∀ {qs : List Ty} (v : (ps :: Ω₁) ∋ₗ qs), LRen.lift κ v = LRen.lift κ' v
  | _, .head => rfl
  | _, .tail v => by simp [LRen.lift, h v]

/-- The same, into the body of a label. -/
theorem LRen.ext_congr {Ω₁ Ω₂ : LCtx} {κ κ' : LRen Ω₁ Ω₂}
    (h : ∀ {qs : List Ty} (v : Ω₁ ∋ₗ qs), κ v = κ' v) (self : Bool) (ps : List Ty) :
    ∀ {qs : List Ty} (v : (LCtx.ext self ps Ω₁) ∋ₗ qs),
      LRen.ext self ps κ v = LRen.ext self ps κ' v := by
  cases self
  · intro _ v; exact h v
  · intro _ v; exact LRen.lift_congr h v

/-! ## Renaming by the identity -/

/-- A renaming that moves nothing still moves nothing under a binder. -/
theorem VRen.lift_self {Γ : Ctx} {σ : Ty} {ρ : VRen Γ Γ}
    (h : ∀ {τ : Ty} (v : Γ ∋ τ), ρ v = v) :
    ∀ {τ : Ty} (v : (σ :: Γ) ∋ τ), VRen.lift ρ v = v
  | _, .head => rfl
  | _, .tail v => by simp [VRen.lift, h v]

/-- The same, under a binder that binds a whole list. -/
theorem VRen.liftList_self {Γ : Ctx} {ρ : VRen Γ Γ}
    (h : ∀ {τ : Ty} (v : Γ ∋ τ), ρ v = v) :
    ∀ (σs : List Ty) {τ : Ty} (v : (σs ++ Γ) ∋ τ), VRen.liftList σs ρ v = v
  | [], _, v => h v
  | _ :: σs, _, v => VRen.lift_self (VRen.liftList_self h σs) v

/-- The same, for renamings of labels. -/
theorem LRen.lift_self {Ω : LCtx} {ps : List Ty} {κ : LRen Ω Ω}
    (h : ∀ {qs : List Ty} (v : Ω ∋ₗ qs), κ v = v) :
    ∀ {qs : List Ty} (v : (ps :: Ω) ∋ₗ qs), LRen.lift κ v = v
  | _, .head => rfl
  | _, .tail v => by simp [LRen.lift, h v]

/-- The same, into the body of a label. -/
theorem LRen.ext_self {Ω : LCtx} {κ : LRen Ω Ω}
    (h : ∀ {qs : List Ty} (v : Ω ∋ₗ qs), κ v = v) (self : Bool) (ps : List Ty) :
    ∀ {qs : List Ty} (v : (LCtx.ext self ps Ω) ∋ₗ qs), LRen.ext self ps κ v = v := by
  cases self
  · intro _ v; exact h v
  · intro _ v; exact LRen.lift_self h v

/-! ## The congruences: a traversal reads its function pointwise -/

mutual

/-- Renaming a term reads the renaming pointwise. -/
theorem Term.rename_congr {Γ₁ Γ₂ : Ctx} {τ : Ty} :
    ∀ (t : Term Sg Γ₁ τ) {ρ ρ' : VRen Γ₁ Γ₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ v = ρ' v) → t.rename ρ = t.rename ρ'
  | .var v, _, _, hρ => by simp [Term.rename, hρ v]
  | .lam b, _, _, hρ => by simp only [Term.rename, b.rename_congr (VRen.lift_congr hρ)]
  | .ap f a, _, _, hρ => by
      simp only [Term.rename, f.rename_congr hρ, a.rename_congr hρ]
  | .lit _, _, _, _ => rfl
  | .global _, _, _, _ => rfl
  | .extern _, _, _, _ => rfl
  | .lazyMk e, _, _, hρ => by simp only [Term.rename, e.rename_congr hρ]
  | .lazyForce e, _, _, hρ => by simp only [Term.rename, e.rename_congr hρ]
  | .letE e b, _, _, hρ => by
      simp only [Term.rename, e.rename_congr hρ, b.rename_congr (VRen.lift_congr hρ)]
  | .ite c t e, _, _, hρ => by
      simp only [Term.rename, c.rename_congr hρ, t.rename_congr hρ, e.rename_congr hρ]
  | .ctor _ _ _ args, _, _, hρ => by simp only [Term.rename, args.rename_congr hρ]
  | .proj e _ _ _ _, _, _, hρ => by simp only [Term.rename, e.rename_congr hρ]
  | .tagOf e _, _, _, hρ => by simp only [Term.rename, e.rename_congr hρ]
  | .caseTag e alts _, _, _, hρ => by
      simp only [Term.rename, e.rename_congr hρ, alts.rename_congr hρ]
  | .block b, _, _, hρ => by
      simp only [Term.rename,
        b.rename_congr (κ := LRen.id) (κ' := LRen.id) hρ (fun _ => rfl)]

/-- Renaming a spine reads the renaming pointwise. -/
theorem Spine.rename_congr {Γ₁ Γ₂ : Ctx} {σs : List Ty} :
    ∀ (s : Spine Sg Γ₁ σs) {ρ ρ' : VRen Γ₁ Γ₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ v = ρ' v) → s.rename ρ = s.rename ρ'
  | .nil, _, _, _ => rfl
  | .cons t rest, _, _, hρ => by
      simp only [Spine.rename, t.rename_congr hρ, rest.rename_congr hρ]

/-- Renaming the branches of a case reads the renaming pointwise. -/
theorem Alts.rename_congr {Γ₁ Γ₂ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool} :
    ∀ (as : Alts Sg Γ₁ τ tags full) {ρ ρ' : VRen Γ₁ Γ₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ v = ρ' v) → as.rename ρ = as.rename ρ'
  | .deflt t, _, _, hρ => by simp only [Alts.rename, t.rename_congr hρ]
  | .nilFull, _, _, _ => rfl
  | .cons _ t rest, _, _, hρ => by
      simp only [Alts.rename, t.rename_congr hρ, rest.rename_congr hρ]

/-- Renaming a tail reads the renamings pointwise. -/
theorem Tail.rename_congr {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ₁ Ω₁ τ) {ρ ρ' : VRen Γ₁ Γ₂} {κ κ' : LRen Ω₁ Ω₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ v = ρ' v) →
      (∀ {ps : List Ty} (v : Ω₁ ∋ₗ ps), κ v = κ' v) →
      b.rename ρ κ = b.rename ρ' κ'
  | .ret t, _, _, _, _, hρ, _ => by simp only [Tail.rename, t.rename_congr hρ]
  | .jmp l args, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename, hκ l, args.rename_congr hρ]
  | .letT e b, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename, e.rename_congr hρ,
        b.rename_congr (VRen.lift_congr hρ) hκ]
  | .iteT c t e, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename, c.rename_congr hρ, t.rename_congr hρ hκ,
        e.rename_congr hρ hκ]
  | .caseT e alts _, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename, e.rename_congr hρ, alts.rename_congr hρ hκ]
  | .label self body rest, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename,
        body.rename_congr (VRen.liftList_congr hρ _) (LRen.ext_congr hκ self _),
        rest.rename_congr hρ (LRen.lift_congr hκ)]

/-- Renaming the branches of a dispatch inside a block reads the renamings pointwise. -/
theorem AltsT.rename_congr {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (as : AltsT Sg Γ₁ Ω₁ τ tags full) {ρ ρ' : VRen Γ₁ Γ₂} {κ κ' : LRen Ω₁ Ω₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ v = ρ' v) →
      (∀ {ps : List Ty} (v : Ω₁ ∋ₗ ps), κ v = κ' v) →
      as.rename ρ κ = as.rename ρ' κ'
  | .deflt b, _, _, _, _, hρ, hκ => by
      simp only [AltsT.rename, b.rename_congr hρ hκ]
  | .nilFull, _, _, _, _, _, _ => rfl
  | .cons _ b rest, _, _, _, _, hρ, hκ => by
      simp only [AltsT.rename, b.rename_congr hρ hκ, rest.rename_congr hρ hκ]

end

/-! ## Renaming by something that moves nothing -/

mutual

/-- A renaming that moves nothing changes nothing. -/
theorem Term.rename_eq_self {Γ : Ctx} {τ : Ty} :
    ∀ (t : Term Sg Γ τ) {ρ : VRen Γ Γ},
      (∀ {σ : Ty} (v : Γ ∋ σ), ρ v = v) → t.rename ρ = t
  | .var v, _, hρ => by simp [Term.rename, hρ v]
  | .lam b, _, hρ => by simp only [Term.rename, b.rename_eq_self (VRen.lift_self hρ)]
  | .ap f a, _, hρ => by
      simp only [Term.rename, f.rename_eq_self hρ, a.rename_eq_self hρ]
  | .lit _, _, _ => rfl
  | .global _, _, _ => rfl
  | .extern _, _, _ => rfl
  | .lazyMk e, _, hρ => by simp only [Term.rename, e.rename_eq_self hρ]
  | .lazyForce e, _, hρ => by simp only [Term.rename, e.rename_eq_self hρ]
  | .letE e b, _, hρ => by
      simp only [Term.rename, e.rename_eq_self hρ, b.rename_eq_self (VRen.lift_self hρ)]
  | .ite c t e, _, hρ => by
      simp only [Term.rename, c.rename_eq_self hρ, t.rename_eq_self hρ,
        e.rename_eq_self hρ]
  | .ctor _ _ _ args, _, hρ => by simp only [Term.rename, args.rename_eq_self hρ]
  | .proj e _ _ _ _, _, hρ => by simp only [Term.rename, e.rename_eq_self hρ]
  | .tagOf e _, _, hρ => by simp only [Term.rename, e.rename_eq_self hρ]
  | .caseTag e alts _, _, hρ => by
      simp only [Term.rename, e.rename_eq_self hρ, alts.rename_eq_self hρ]
  | .block b, _, hρ => by
      simp only [Term.rename, b.rename_eq_self (κ := LRen.id) hρ (fun _ => rfl)]

/-- A renaming that moves nothing changes no spine. -/
theorem Spine.rename_eq_self {Γ : Ctx} {σs : List Ty} :
    ∀ (s : Spine Sg Γ σs) {ρ : VRen Γ Γ},
      (∀ {σ : Ty} (v : Γ ∋ σ), ρ v = v) → s.rename ρ = s
  | .nil, _, _ => rfl
  | .cons t rest, _, hρ => by
      simp only [Spine.rename, t.rename_eq_self hρ, rest.rename_eq_self hρ]

/-- A renaming that moves nothing changes no branch. -/
theorem Alts.rename_eq_self {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool} :
    ∀ (as : Alts Sg Γ τ tags full) {ρ : VRen Γ Γ},
      (∀ {σ : Ty} (v : Γ ∋ σ), ρ v = v) → as.rename ρ = as
  | .deflt t, _, hρ => by simp only [Alts.rename, t.rename_eq_self hρ]
  | .nilFull, _, _ => rfl
  | .cons _ t rest, _, hρ => by
      simp only [Alts.rename, t.rename_eq_self hρ, rest.rename_eq_self hρ]

/-- A renaming that moves nothing changes no tail. -/
theorem Tail.rename_eq_self {Γ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ Ω τ) {ρ : VRen Γ Γ} {κ : LRen Ω Ω},
      (∀ {σ : Ty} (v : Γ ∋ σ), ρ v = v) →
      (∀ {ps : List Ty} (v : Ω ∋ₗ ps), κ v = v) →
      b.rename ρ κ = b
  | .ret t, _, _, hρ, _ => by simp only [Tail.rename, t.rename_eq_self hρ]
  | .jmp l args, _, _, hρ, hκ => by
      simp only [Tail.rename, hκ l, args.rename_eq_self hρ]
  | .letT e b, _, _, hρ, hκ => by
      simp only [Tail.rename, e.rename_eq_self hρ,
        b.rename_eq_self (VRen.lift_self hρ) hκ]
  | .iteT c t e, _, _, hρ, hκ => by
      simp only [Tail.rename, c.rename_eq_self hρ, t.rename_eq_self hρ hκ,
        e.rename_eq_self hρ hκ]
  | .caseT e alts _, _, _, hρ, hκ => by
      simp only [Tail.rename, e.rename_eq_self hρ, alts.rename_eq_self hρ hκ]
  | .label self body rest, _, _, hρ, hκ => by
      simp only [Tail.rename,
        body.rename_eq_self (VRen.liftList_self hρ _) (LRen.ext_self hκ self _),
        rest.rename_eq_self hρ (LRen.lift_self hκ)]

/-- A renaming that moves nothing changes no branch of a block. -/
theorem AltsT.rename_eq_self {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (as : AltsT Sg Γ Ω τ tags full) {ρ : VRen Γ Γ} {κ : LRen Ω Ω},
      (∀ {σ : Ty} (v : Γ ∋ σ), ρ v = v) →
      (∀ {ps : List Ty} (v : Ω ∋ₗ ps), κ v = v) →
      as.rename ρ κ = as
  | .deflt b, _, _, hρ, hκ => by simp only [AltsT.rename, b.rename_eq_self hρ hκ]
  | .nilFull, _, _, _, _ => rfl
  | .cons _ b rest, _, _, hρ, hκ => by
      simp only [AltsT.rename, b.rename_eq_self hρ hκ, rest.rename_eq_self hρ hκ]

end

/-! ## Composing two renamings -/

/-- Composing two renamings under a binder. -/
theorem VRen.lift_comp {Γ₁ Γ₂ Γ₃ : Ctx} {σ : Ty} {ρ : VRen Γ₁ Γ₂} {ρ' : VRen Γ₂ Γ₃}
    {ρ'' : VRen Γ₁ Γ₃} (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), ρ'' v = ρ' (ρ v)) :
    ∀ {τ : Ty} (v : (σ :: Γ₁) ∋ τ), VRen.lift ρ'' v = VRen.lift ρ' (VRen.lift ρ v)
  | _, .head => rfl
  | _, .tail v => by simp [VRen.lift, h v]

/-- The same, under a binder that binds a whole list. -/
theorem VRen.liftList_comp {Γ₁ Γ₂ Γ₃ : Ctx} {ρ : VRen Γ₁ Γ₂} {ρ' : VRen Γ₂ Γ₃}
    {ρ'' : VRen Γ₁ Γ₃} (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), ρ'' v = ρ' (ρ v)) :
    ∀ (σs : List Ty) {τ : Ty} (v : (σs ++ Γ₁) ∋ τ),
      VRen.liftList σs ρ'' v = VRen.liftList σs ρ' (VRen.liftList σs ρ v)
  | [], _, v => h v
  | _ :: σs, _, v => VRen.lift_comp (VRen.liftList_comp h σs) v

/-- The same, for renamings of labels. -/
theorem LRen.lift_comp {Ω₁ Ω₂ Ω₃ : LCtx} {ps : List Ty} {κ : LRen Ω₁ Ω₂}
    {κ' : LRen Ω₂ Ω₃} {κ'' : LRen Ω₁ Ω₃}
    (h : ∀ {qs : List Ty} (v : Ω₁ ∋ₗ qs), κ'' v = κ' (κ v)) :
    ∀ {qs : List Ty} (v : (ps :: Ω₁) ∋ₗ qs),
      LRen.lift κ'' v = LRen.lift κ' (LRen.lift κ v)
  | _, .head => rfl
  | _, .tail v => by simp [LRen.lift, h v]

/-- The same, into the body of a label. -/
theorem LRen.ext_comp {Ω₁ Ω₂ Ω₃ : LCtx} {κ : LRen Ω₁ Ω₂} {κ' : LRen Ω₂ Ω₃}
    {κ'' : LRen Ω₁ Ω₃} (h : ∀ {qs : List Ty} (v : Ω₁ ∋ₗ qs), κ'' v = κ' (κ v))
    (self : Bool) (ps : List Ty) :
    ∀ {qs : List Ty} (v : (LCtx.ext self ps Ω₁) ∋ₗ qs),
      LRen.ext self ps κ'' v = LRen.ext self ps κ' (LRen.ext self ps κ v) := by
  cases self
  · intro _ v; exact h v
  · intro _ v; exact LRen.lift_comp h v

mutual

/-- Renaming twice is renaming once, by the composite. -/
theorem Term.rename_rename {Γ₁ Γ₂ Γ₃ : Ctx} {τ : Ty} :
    ∀ (t : Term Sg Γ₁ τ) {ρ : VRen Γ₁ Γ₂} {ρ' : VRen Γ₂ Γ₃} {ρ'' : VRen Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ'' v = ρ' (ρ v)) →
      (t.rename ρ).rename ρ' = t.rename ρ''
  | .var v, _, _, _, hρ => by simp [Term.rename, hρ v]
  | .lam b, _, _, _, hρ => by
      simp only [Term.rename, b.rename_rename (VRen.lift_comp hρ)]
  | .ap f a, _, _, _, hρ => by
      simp only [Term.rename, f.rename_rename hρ, a.rename_rename hρ]
  | .lit _, _, _, _, _ => rfl
  | .global _, _, _, _, _ => rfl
  | .extern _, _, _, _, _ => rfl
  | .lazyMk e, _, _, _, hρ => by simp only [Term.rename, e.rename_rename hρ]
  | .lazyForce e, _, _, _, hρ => by simp only [Term.rename, e.rename_rename hρ]
  | .letE e b, _, _, _, hρ => by
      simp only [Term.rename, e.rename_rename hρ, b.rename_rename (VRen.lift_comp hρ)]
  | .ite c t e, _, _, _, hρ => by
      simp only [Term.rename, c.rename_rename hρ, t.rename_rename hρ,
        e.rename_rename hρ]
  | .ctor _ _ _ args, _, _, _, hρ => by simp only [Term.rename, args.rename_rename hρ]
  | .proj e _ _ _ _, _, _, _, hρ => by simp only [Term.rename, e.rename_rename hρ]
  | .tagOf e _, _, _, _, hρ => by simp only [Term.rename, e.rename_rename hρ]
  | .caseTag e alts _, _, _, _, hρ => by
      simp only [Term.rename, e.rename_rename hρ, alts.rename_rename hρ]
  | .block b, _, _, _, hρ => by
      simp only [Term.rename, b.rename_rename (κ := LRen.id) (κ' := LRen.id)
        (κ'' := LRen.id) hρ (fun _ => rfl)]

/-- The same, for a spine. -/
theorem Spine.rename_rename {Γ₁ Γ₂ Γ₃ : Ctx} {σs : List Ty} :
    ∀ (s : Spine Sg Γ₁ σs) {ρ : VRen Γ₁ Γ₂} {ρ' : VRen Γ₂ Γ₃} {ρ'' : VRen Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ'' v = ρ' (ρ v)) →
      (s.rename ρ).rename ρ' = s.rename ρ''
  | .nil, _, _, _, _ => rfl
  | .cons t rest, _, _, _, hρ => by
      simp only [Spine.rename, t.rename_rename hρ, rest.rename_rename hρ]

/-- The same, for the branches of a case. -/
theorem Alts.rename_rename {Γ₁ Γ₂ Γ₃ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool} :
    ∀ (as : Alts Sg Γ₁ τ tags full) {ρ : VRen Γ₁ Γ₂} {ρ' : VRen Γ₂ Γ₃}
      {ρ'' : VRen Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ'' v = ρ' (ρ v)) →
      (as.rename ρ).rename ρ' = as.rename ρ''
  | .deflt t, _, _, _, hρ => by simp only [Alts.rename, t.rename_rename hρ]
  | .nilFull, _, _, _, _ => rfl
  | .cons _ t rest, _, _, _, hρ => by
      simp only [Alts.rename, t.rename_rename hρ, rest.rename_rename hρ]

/-- The same, for a tail. -/
theorem Tail.rename_rename {Γ₁ Γ₂ Γ₃ : Ctx} {Ω₁ Ω₂ Ω₃ : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ₁ Ω₁ τ) {ρ : VRen Γ₁ Γ₂} {κ : LRen Ω₁ Ω₂} {ρ' : VRen Γ₂ Γ₃}
      {κ' : LRen Ω₂ Ω₃} {ρ'' : VRen Γ₁ Γ₃} {κ'' : LRen Ω₁ Ω₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ'' v = ρ' (ρ v)) →
      (∀ {ps : List Ty} (v : Ω₁ ∋ₗ ps), κ'' v = κ' (κ v)) →
      (b.rename ρ κ).rename ρ' κ' = b.rename ρ'' κ''
  | .ret t, _, _, _, _, _, _, hρ, _ => by
      simp only [Tail.rename, t.rename_rename hρ]
  | .jmp l args, _, _, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename, hκ l, args.rename_rename hρ]
  | .letT e b, _, _, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename, e.rename_rename hρ,
        b.rename_rename (VRen.lift_comp hρ) hκ]
  | .iteT c t e, _, _, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename, c.rename_rename hρ, t.rename_rename hρ hκ,
        e.rename_rename hρ hκ]
  | .caseT e alts _, _, _, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename, e.rename_rename hρ, alts.rename_rename hρ hκ]
  | .label self body rest, _, _, _, _, _, _, hρ, hκ => by
      simp only [Tail.rename,
        body.rename_rename (VRen.liftList_comp hρ _) (LRen.ext_comp hκ self _),
        rest.rename_rename hρ (LRen.lift_comp hκ)]

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.rename_rename {Γ₁ Γ₂ Γ₃ : Ctx} {Ω₁ Ω₂ Ω₃ : LCtx} {τ : Ty}
    {tags : List Nat} {full : Bool} :
    ∀ (as : AltsT Sg Γ₁ Ω₁ τ tags full) {ρ : VRen Γ₁ Γ₂} {κ : LRen Ω₁ Ω₂}
      {ρ' : VRen Γ₂ Γ₃} {κ' : LRen Ω₂ Ω₃} {ρ'' : VRen Γ₁ Γ₃} {κ'' : LRen Ω₁ Ω₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), ρ'' v = ρ' (ρ v)) →
      (∀ {ps : List Ty} (v : Ω₁ ∋ₗ ps), κ'' v = κ' (κ v)) →
      (as.rename ρ κ).rename ρ' κ' = as.rename ρ'' κ''
  | .deflt b, _, _, _, _, _, _, hρ, hκ => by
      simp only [AltsT.rename, b.rename_rename hρ hκ]
  | .nilFull, _, _, _, _, _, _, _, _ => rfl
  | .cons _ b rest, _, _, _, _, _, _, hρ, hκ => by
      simp only [AltsT.rename, b.rename_rename hρ hκ, rest.rename_rename hρ hκ]

end

/-! ## The congruence of substitution -/

/-- Carrying two pointwise-equal substitutions under a binder gives pointwise-equal
    substitutions. -/
theorem VSub.lift_congr {Γ₁ Γ₂ : Ctx} {σ : Ty} {θ θ' : VSub Sg Γ₁ Γ₂}
    (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), θ v = θ' v) :
    ∀ {τ : Ty} (v : (σ :: Γ₁) ∋ τ), VSub.lift θ v = VSub.lift θ' v
  | _, .head => rfl
  | _, .tail v => by simp [VSub.lift, h v]

/-- The same, under a binder that binds a whole list. -/
theorem VSub.liftList_congr {Γ₁ Γ₂ : Ctx} {θ θ' : VSub Sg Γ₁ Γ₂}
    (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), θ v = θ' v) :
    ∀ (σs : List Ty) {τ : Ty} (v : (σs ++ Γ₁) ∋ τ),
      VSub.liftList σs θ v = VSub.liftList σs θ' v
  | [], _, v => h v
  | _ :: σs, _, v => VSub.lift_congr (VSub.liftList_congr h σs) v

mutual

/-- Substituting in a term reads the substitution pointwise. -/
theorem Term.subst_congr {Γ₁ Γ₂ : Ctx} {τ : Ty} :
    ∀ (t : Term Sg Γ₁ τ) {θ θ' : VSub Sg Γ₁ Γ₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ v = θ' v) → t.subst θ = t.subst θ'
  | .var v, _, _, hθ => by simp [Term.subst, hθ v]
  | .lam b, _, _, hθ => by simp only [Term.subst, b.subst_congr (VSub.lift_congr hθ)]
  | .ap f a, _, _, hθ => by
      simp only [Term.subst, f.subst_congr hθ, a.subst_congr hθ]
  | .lit _, _, _, _ => rfl
  | .global _, _, _, _ => rfl
  | .extern _, _, _, _ => rfl
  | .lazyMk e, _, _, hθ => by simp only [Term.subst, e.subst_congr hθ]
  | .lazyForce e, _, _, hθ => by simp only [Term.subst, e.subst_congr hθ]
  | .letE e b, _, _, hθ => by
      simp only [Term.subst, e.subst_congr hθ, b.subst_congr (VSub.lift_congr hθ)]
  | .ite c t e, _, _, hθ => by
      simp only [Term.subst, c.subst_congr hθ, t.subst_congr hθ, e.subst_congr hθ]
  | .ctor _ _ _ args, _, _, hθ => by simp only [Term.subst, args.subst_congr hθ]
  | .proj e _ _ _ _, _, _, hθ => by simp only [Term.subst, e.subst_congr hθ]
  | .tagOf e _, _, _, hθ => by simp only [Term.subst, e.subst_congr hθ]
  | .caseTag e alts _, _, _, hθ => by
      simp only [Term.subst, e.subst_congr hθ, alts.subst_congr hθ]
  | .block b, _, _, hθ => by simp only [Term.subst, b.subst_congr hθ]

/-- The same, for a spine. -/
theorem Spine.subst_congr {Γ₁ Γ₂ : Ctx} {σs : List Ty} :
    ∀ (s : Spine Sg Γ₁ σs) {θ θ' : VSub Sg Γ₁ Γ₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ v = θ' v) → s.subst θ = s.subst θ'
  | .nil, _, _, _ => rfl
  | .cons t rest, _, _, hθ => by
      simp only [Spine.subst, t.subst_congr hθ, rest.subst_congr hθ]

/-- The same, for the branches of a case. -/
theorem Alts.subst_congr {Γ₁ Γ₂ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool} :
    ∀ (as : Alts Sg Γ₁ τ tags full) {θ θ' : VSub Sg Γ₁ Γ₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ v = θ' v) → as.subst θ = as.subst θ'
  | .deflt t, _, _, hθ => by simp only [Alts.subst, t.subst_congr hθ]
  | .nilFull, _, _, _ => rfl
  | .cons _ t rest, _, _, hθ => by
      simp only [Alts.subst, t.subst_congr hθ, rest.subst_congr hθ]

/-- The same, for a tail. -/
theorem Tail.subst_congr {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ₁ Ω τ) {θ θ' : VSub Sg Γ₁ Γ₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ v = θ' v) → b.subst θ = b.subst θ'
  | .ret t, _, _, hθ => by simp only [Tail.subst, t.subst_congr hθ]
  | .jmp _ args, _, _, hθ => by simp only [Tail.subst, args.subst_congr hθ]
  | .letT e b, _, _, hθ => by
      simp only [Tail.subst, e.subst_congr hθ, b.subst_congr (VSub.lift_congr hθ)]
  | .iteT c t e, _, _, hθ => by
      simp only [Tail.subst, c.subst_congr hθ, t.subst_congr hθ, e.subst_congr hθ]
  | .caseT e alts _, _, _, hθ => by
      simp only [Tail.subst, e.subst_congr hθ, alts.subst_congr hθ]
  | .label _ body rest, _, _, hθ => by
      simp only [Tail.subst, body.subst_congr (VSub.liftList_congr hθ _),
        rest.subst_congr hθ]

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.subst_congr {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (as : AltsT Sg Γ₁ Ω τ tags full) {θ θ' : VSub Sg Γ₁ Γ₂},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ v = θ' v) → as.subst θ = as.subst θ'
  | .deflt b, _, _, hθ => by simp only [AltsT.subst, b.subst_congr hθ]
  | .nilFull, _, _, _ => rfl
  | .cons _ b rest, _, _, hθ => by
      simp only [AltsT.subst, b.subst_congr hθ, rest.subst_congr hθ]

end

/-! ## A substitution after a renaming -/

/-- Carrying a substitution and a renaming under a binder commutes with composing
    them. -/
theorem VSub.lift_ren {Γ₁ Γ₂ Γ₃ : Ctx} {σ : Ty} {ρ : VRen Γ₁ Γ₂} {θ : VSub Sg Γ₂ Γ₃}
    {θ'' : VSub Sg Γ₁ Γ₃} (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), θ'' v = θ (ρ v)) :
    ∀ {τ : Ty} (v : (σ :: Γ₁) ∋ τ), VSub.lift θ'' v = VSub.lift θ (VRen.lift ρ v)
  | _, .head => rfl
  | _, .tail v => by simp [VSub.lift, VRen.lift, h v]

/-- The same, under a binder that binds a whole list. -/
theorem VSub.liftList_ren {Γ₁ Γ₂ Γ₃ : Ctx} {ρ : VRen Γ₁ Γ₂} {θ : VSub Sg Γ₂ Γ₃}
    {θ'' : VSub Sg Γ₁ Γ₃} (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), θ'' v = θ (ρ v)) :
    ∀ (σs : List Ty) {τ : Ty} (v : (σs ++ Γ₁) ∋ τ),
      VSub.liftList σs θ'' v = VSub.liftList σs θ (VRen.liftList σs ρ v)
  | [], _, v => h v
  | _ :: σs, _, v => VSub.lift_ren (VSub.liftList_ren h σs) v

mutual

/-- Renaming and then substituting is one substitution.  The renaming `ρ₀` on the right
    moves nothing; it is there because the same statement is proved for a `Tail`, where
    the label renaming really does survive the substitution. -/
theorem Term.subst_rename {Γ₁ Γ₂ Γ₃ : Ctx} {τ : Ty} :
    ∀ (t : Term Sg Γ₁ τ) {ρ : VRen Γ₁ Γ₂} {θ : VSub Sg Γ₂ Γ₃} {θ'' : VSub Sg Γ₁ Γ₃}
      {ρ₀ : VRen Γ₃ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = θ (ρ v)) →
      (∀ {σ : Ty} (v : Γ₃ ∋ σ), ρ₀ v = v) →
      (t.rename ρ).subst θ = (t.subst θ'').rename ρ₀
  | .var v, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, hθ v]
      exact (Term.rename_eq_self _ hρ₀).symm
  | .lam b, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst,
        b.subst_rename (VSub.lift_ren hθ) (VRen.lift_self hρ₀)]
  | .ap f a, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, f.subst_rename hθ hρ₀, a.subst_rename hθ hρ₀]
  | .lit _, _, _, _, _, _, _ => rfl
  | .global _, _, _, _, _, _, _ => rfl
  | .extern _, _, _, _, _, _, _ => rfl
  | .lazyMk e, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, e.subst_rename hθ hρ₀]
  | .lazyForce e, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, e.subst_rename hθ hρ₀]
  | .letE e b, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, e.subst_rename hθ hρ₀,
        b.subst_rename (VSub.lift_ren hθ) (VRen.lift_self hρ₀)]
  | .ite c t e, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, c.subst_rename hθ hρ₀, t.subst_rename hθ hρ₀,
        e.subst_rename hθ hρ₀]
  | .ctor _ _ _ args, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, args.subst_rename hθ hρ₀]
  | .proj e _ _ _ _, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, e.subst_rename hθ hρ₀]
  | .tagOf e _, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, e.subst_rename hθ hρ₀]
  | .caseTag e alts _, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst, e.subst_rename hθ hρ₀,
        alts.subst_rename hθ hρ₀]
  | .block b, _, _, _, _, hθ, hρ₀ => by
      simp only [Term.rename, Term.subst,
        b.subst_rename (κ := LRen.id) hθ hρ₀]

/-- The same, for a spine. -/
theorem Spine.subst_rename {Γ₁ Γ₂ Γ₃ : Ctx} {σs : List Ty} :
    ∀ (s : Spine Sg Γ₁ σs) {ρ : VRen Γ₁ Γ₂} {θ : VSub Sg Γ₂ Γ₃} {θ'' : VSub Sg Γ₁ Γ₃}
      {ρ₀ : VRen Γ₃ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = θ (ρ v)) →
      (∀ {σ : Ty} (v : Γ₃ ∋ σ), ρ₀ v = v) →
      (s.rename ρ).subst θ = (s.subst θ'').rename ρ₀
  | .nil, _, _, _, _, _, _ => rfl
  | .cons t rest, _, _, _, _, hθ, hρ₀ => by
      simp only [Spine.rename, Spine.subst, t.subst_rename hθ hρ₀,
        rest.subst_rename hθ hρ₀]

/-- The same, for the branches of a case. -/
theorem Alts.subst_rename {Γ₁ Γ₂ Γ₃ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool} :
    ∀ (as : Alts Sg Γ₁ τ tags full) {ρ : VRen Γ₁ Γ₂} {θ : VSub Sg Γ₂ Γ₃}
      {θ'' : VSub Sg Γ₁ Γ₃} {ρ₀ : VRen Γ₃ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = θ (ρ v)) →
      (∀ {σ : Ty} (v : Γ₃ ∋ σ), ρ₀ v = v) →
      (as.rename ρ).subst θ = (as.subst θ'').rename ρ₀
  | .deflt t, _, _, _, _, hθ, hρ₀ => by
      simp only [Alts.rename, Alts.subst, t.subst_rename hθ hρ₀]
  | .nilFull, _, _, _, _, _, _ => rfl
  | .cons _ t rest, _, _, _, _, hθ, hρ₀ => by
      simp only [Alts.rename, Alts.subst, t.subst_rename hθ hρ₀,
        rest.subst_rename hθ hρ₀]

/-- The same, for a tail: the label renaming is carried out to the front. -/
theorem Tail.subst_rename {Γ₁ Γ₂ Γ₃ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ₁ Ω₁ τ) {ρ : VRen Γ₁ Γ₂} {κ : LRen Ω₁ Ω₂} {θ : VSub Sg Γ₂ Γ₃}
      {θ'' : VSub Sg Γ₁ Γ₃} {ρ₀ : VRen Γ₃ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = θ (ρ v)) →
      (∀ {σ : Ty} (v : Γ₃ ∋ σ), ρ₀ v = v) →
      (b.rename ρ κ).subst θ = (b.subst θ'').rename ρ₀ κ
  | .ret t, _, _, _, _, _, hθ, hρ₀ => by
      simp only [Tail.rename, Tail.subst, t.subst_rename hθ hρ₀]
  | .jmp _ args, _, _, _, _, _, hθ, hρ₀ => by
      simp only [Tail.rename, Tail.subst, args.subst_rename hθ hρ₀]
  | .letT e b, _, _, _, _, _, hθ, hρ₀ => by
      simp only [Tail.rename, Tail.subst, e.subst_rename hθ hρ₀,
        b.subst_rename (VSub.lift_ren hθ) (VRen.lift_self hρ₀)]
  | .iteT c t e, _, _, _, _, _, hθ, hρ₀ => by
      simp only [Tail.rename, Tail.subst, c.subst_rename hθ hρ₀, t.subst_rename hθ hρ₀,
        e.subst_rename hθ hρ₀]
  | .caseT e alts _, _, _, _, _, _, hθ, hρ₀ => by
      simp only [Tail.rename, Tail.subst, e.subst_rename hθ hρ₀,
        alts.subst_rename hθ hρ₀]
  | .label _ body rest, _, _, _, _, _, hθ, hρ₀ => by
      simp only [Tail.rename, Tail.subst,
        body.subst_rename (VSub.liftList_ren hθ _) (VRen.liftList_self hρ₀ _),
        rest.subst_rename hθ hρ₀]

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.subst_rename {Γ₁ Γ₂ Γ₃ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (as : AltsT Sg Γ₁ Ω₁ τ tags full) {ρ : VRen Γ₁ Γ₂} {κ : LRen Ω₁ Ω₂}
      {θ : VSub Sg Γ₂ Γ₃} {θ'' : VSub Sg Γ₁ Γ₃} {ρ₀ : VRen Γ₃ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = θ (ρ v)) →
      (∀ {σ : Ty} (v : Γ₃ ∋ σ), ρ₀ v = v) →
      (as.rename ρ κ).subst θ = (as.subst θ'').rename ρ₀ κ
  | .deflt b, _, _, _, _, _, hθ, hρ₀ => by
      simp only [AltsT.rename, AltsT.subst, b.subst_rename hθ hρ₀]
  | .nilFull, _, _, _, _, _, _, _ => rfl
  | .cons _ b rest, _, _, _, _, _, hθ, hρ₀ => by
      simp only [AltsT.rename, AltsT.subst, b.subst_rename hθ hρ₀,
        rest.subst_rename hθ hρ₀]

end

/-! ## A renaming after a substitution -/

/-- Carrying a substitution and the renaming of its results under a binder. -/
theorem VSub.lift_ren2 {Γ₁ Γ₂ Γ₃ : Ctx} {σ : Ty} {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₂ Γ₃}
    {θ'' : VSub Sg Γ₁ Γ₃}
    (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), θ'' v = (θ v).rename ρ) :
    ∀ {τ : Ty} (v : (σ :: Γ₁) ∋ τ),
      VSub.lift θ'' v = ((VSub.lift θ) v).rename (VRen.lift ρ)
  | _, .head => by simp [VSub.lift, Term.rename, VRen.lift]
  | _, .tail v => by
      show (θ'' v).weaken = ((θ v).weaken).rename (VRen.lift ρ)
      rw [h v, Term.weaken, Term.weaken,
        Term.rename_rename (θ v) (ρ := ρ) (ρ' := VRen.weaken)
          (ρ'' := fun w => Var.tail (ρ w)) (fun _ => rfl),
        Term.rename_rename (θ v) (ρ := VRen.weaken) (ρ' := VRen.lift ρ)
          (ρ'' := fun w => Var.tail (ρ w)) (fun _ => rfl)]

/-- The same, under a binder that binds a whole list. -/
theorem VSub.liftList_ren2 {Γ₁ Γ₂ Γ₃ : Ctx} {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₂ Γ₃}
    {θ'' : VSub Sg Γ₁ Γ₃}
    (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), θ'' v = (θ v).rename ρ) :
    ∀ (σs : List Ty) {τ : Ty} (v : (σs ++ Γ₁) ∋ τ),
      VSub.liftList σs θ'' v = ((VSub.liftList σs θ) v).rename (VRen.liftList σs ρ)
  | [], _, v => h v
  | _ :: σs, _, v => VSub.lift_ren2 (VSub.liftList_ren2 h σs) v

mutual

/-- Substituting and then renaming is one substitution. -/
theorem Term.rename_subst {Γ₁ Γ₂ Γ₃ : Ctx} {τ : Ty} :
    ∀ (t : Term Sg Γ₁ τ) {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₂ Γ₃} {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).rename ρ) →
      (t.subst θ).rename ρ = t.subst θ''
  | .var v, _, _, _, hθ => by simp [Term.subst, hθ v]
  | .lam b, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, b.rename_subst (VSub.lift_ren2 hθ)]
  | .ap f a, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, f.rename_subst hθ, a.rename_subst hθ]
  | .lit _, _, _, _, _ => rfl
  | .global _, _, _, _, _ => rfl
  | .extern _, _, _, _, _ => rfl
  | .lazyMk e, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, e.rename_subst hθ]
  | .lazyForce e, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, e.rename_subst hθ]
  | .letE e b, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, e.rename_subst hθ,
        b.rename_subst (VSub.lift_ren2 hθ)]
  | .ite c t e, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, c.rename_subst hθ, t.rename_subst hθ,
        e.rename_subst hθ]
  | .ctor _ _ _ args, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, args.rename_subst hθ]
  | .proj e _ _ _ _, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, e.rename_subst hθ]
  | .tagOf e _, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, e.rename_subst hθ]
  | .caseTag e alts _, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, e.rename_subst hθ, alts.rename_subst hθ]
  | .block b, _, _, _, hθ => by
      simp only [Term.subst, Term.rename, b.rename_subst (κ := LRen.id) hθ (fun _ => rfl)]

/-- The same, for a spine. -/
theorem Spine.rename_subst {Γ₁ Γ₂ Γ₃ : Ctx} {σs : List Ty} :
    ∀ (s : Spine Sg Γ₁ σs) {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₂ Γ₃} {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).rename ρ) →
      (s.subst θ).rename ρ = s.subst θ''
  | .nil, _, _, _, _ => rfl
  | .cons t rest, _, _, _, hθ => by
      simp only [Spine.subst, Spine.rename, t.rename_subst hθ, rest.rename_subst hθ]

/-- The same, for the branches of a case. -/
theorem Alts.rename_subst {Γ₁ Γ₂ Γ₃ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool} :
    ∀ (as : Alts Sg Γ₁ τ tags full) {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₂ Γ₃}
      {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).rename ρ) →
      (as.subst θ).rename ρ = as.subst θ''
  | .deflt t, _, _, _, hθ => by simp only [Alts.subst, Alts.rename, t.rename_subst hθ]
  | .nilFull, _, _, _, _ => rfl
  | .cons _ t rest, _, _, _, hθ => by
      simp only [Alts.subst, Alts.rename, t.rename_subst hθ, rest.rename_subst hθ]

/-- The same, for a tail, whose label renaming has to move nothing. -/
theorem Tail.rename_subst {Γ₁ Γ₂ Γ₃ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ₁ Ω τ) {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₂ Γ₃} {κ : LRen Ω Ω}
      {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).rename ρ) →
      (∀ {ps : List Ty} (v : Ω ∋ₗ ps), κ v = v) →
      (b.subst θ).rename ρ κ = b.subst θ''
  | .ret t, _, _, _, _, hθ, _ => by
      simp only [Tail.subst, Tail.rename, t.rename_subst hθ]
  | .jmp l args, _, _, _, _, hθ, hκ => by
      simp only [Tail.subst, Tail.rename, hκ l, args.rename_subst hθ]
  | .letT e b, _, _, _, _, hθ, hκ => by
      simp only [Tail.subst, Tail.rename, e.rename_subst hθ,
        b.rename_subst (VSub.lift_ren2 hθ) hκ]
  | .iteT c t e, _, _, _, _, hθ, hκ => by
      simp only [Tail.subst, Tail.rename, c.rename_subst hθ, t.rename_subst hθ hκ,
        e.rename_subst hθ hκ]
  | .caseT e alts _, _, _, _, _, hθ, hκ => by
      simp only [Tail.subst, Tail.rename, e.rename_subst hθ, alts.rename_subst hθ hκ]
  | .label self body rest, _, _, _, _, hθ, hκ => by
      simp only [Tail.subst, Tail.rename,
        body.rename_subst (VSub.liftList_ren2 hθ _) (LRen.ext_self hκ self _),
        rest.rename_subst hθ (LRen.lift_self hκ)]

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.rename_subst {Γ₁ Γ₂ Γ₃ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (as : AltsT Sg Γ₁ Ω τ tags full) {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₂ Γ₃}
      {κ : LRen Ω Ω} {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).rename ρ) →
      (∀ {ps : List Ty} (v : Ω ∋ₗ ps), κ v = v) →
      (as.subst θ).rename ρ κ = as.subst θ''
  | .deflt b, _, _, _, _, hθ, hκ => by
      simp only [AltsT.subst, AltsT.rename, b.rename_subst hθ hκ]
  | .nilFull, _, _, _, _, _, _ => rfl
  | .cons _ b rest, _, _, _, _, hθ, hκ => by
      simp only [AltsT.subst, AltsT.rename, b.rename_subst hθ hκ,
        rest.rename_subst hθ hκ]

end

/-! ## A substitution after a substitution -/

/-- Carrying two substitutions under a binder commutes with composing them. -/
theorem VSub.lift_comp {Γ₁ Γ₂ Γ₃ : Ctx} {σ : Ty} {θ : VSub Sg Γ₁ Γ₂} {θ' : VSub Sg Γ₂ Γ₃}
    {θ'' : VSub Sg Γ₁ Γ₃} (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), θ'' v = (θ v).subst θ') :
    ∀ {τ : Ty} (v : (σ :: Γ₁) ∋ τ),
      VSub.lift θ'' v = ((VSub.lift θ) v).subst (VSub.lift θ')
  | _, .head => by simp [VSub.lift, Term.subst]
  | _, .tail v => by
      show (θ'' v).weaken = ((θ v).weaken).subst (VSub.lift θ')
      rw [h v, Term.weaken, Term.weaken,
        Term.rename_subst (θ v) (θ := θ') (ρ := VRen.weaken)
          (θ'' := fun w => (θ' w).rename VRen.weaken) (fun _ => rfl),
        Term.subst_rename (θ v) (ρ := VRen.weaken) (θ := VSub.lift θ')
          (θ'' := fun w => (θ' w).rename VRen.weaken) (ρ₀ := VRen.id)
          (fun _ => rfl) (fun _ => rfl)]
      exact (Term.rename_eq_self _ (fun _ => rfl)).symm

/-- The same, under a binder that binds a whole list. -/
theorem VSub.liftList_comp {Γ₁ Γ₂ Γ₃ : Ctx} {θ : VSub Sg Γ₁ Γ₂} {θ' : VSub Sg Γ₂ Γ₃}
    {θ'' : VSub Sg Γ₁ Γ₃} (h : ∀ {τ : Ty} (v : Γ₁ ∋ τ), θ'' v = (θ v).subst θ') :
    ∀ (σs : List Ty) {τ : Ty} (v : (σs ++ Γ₁) ∋ τ),
      VSub.liftList σs θ'' v = ((VSub.liftList σs θ) v).subst (VSub.liftList σs θ')
  | [], _, v => h v
  | _ :: σs, _, v => VSub.lift_comp (VSub.liftList_comp h σs) v

mutual

/-- Substituting twice is substituting once, by the composite. -/
theorem Term.subst_subst {Γ₁ Γ₂ Γ₃ : Ctx} {τ : Ty} :
    ∀ (t : Term Sg Γ₁ τ) {θ : VSub Sg Γ₁ Γ₂} {θ' : VSub Sg Γ₂ Γ₃}
      {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).subst θ') →
      (t.subst θ).subst θ' = t.subst θ''
  | .var v, _, _, _, hθ => by simp [Term.subst, hθ v]
  | .lam b, _, _, _, hθ => by
      simp only [Term.subst, b.subst_subst (VSub.lift_comp hθ)]
  | .ap f a, _, _, _, hθ => by
      simp only [Term.subst, f.subst_subst hθ, a.subst_subst hθ]
  | .lit _, _, _, _, _ => rfl
  | .global _, _, _, _, _ => rfl
  | .extern _, _, _, _, _ => rfl
  | .lazyMk e, _, _, _, hθ => by simp only [Term.subst, e.subst_subst hθ]
  | .lazyForce e, _, _, _, hθ => by simp only [Term.subst, e.subst_subst hθ]
  | .letE e b, _, _, _, hθ => by
      simp only [Term.subst, e.subst_subst hθ, b.subst_subst (VSub.lift_comp hθ)]
  | .ite c t e, _, _, _, hθ => by
      simp only [Term.subst, c.subst_subst hθ, t.subst_subst hθ, e.subst_subst hθ]
  | .ctor _ _ _ args, _, _, _, hθ => by simp only [Term.subst, args.subst_subst hθ]
  | .proj e _ _ _ _, _, _, _, hθ => by simp only [Term.subst, e.subst_subst hθ]
  | .tagOf e _, _, _, _, hθ => by simp only [Term.subst, e.subst_subst hθ]
  | .caseTag e alts _, _, _, _, hθ => by
      simp only [Term.subst, e.subst_subst hθ, alts.subst_subst hθ]
  | .block b, _, _, _, hθ => by simp only [Term.subst, b.subst_subst hθ]

/-- The same, for a spine. -/
theorem Spine.subst_subst {Γ₁ Γ₂ Γ₃ : Ctx} {σs : List Ty} :
    ∀ (s : Spine Sg Γ₁ σs) {θ : VSub Sg Γ₁ Γ₂} {θ' : VSub Sg Γ₂ Γ₃}
      {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).subst θ') →
      (s.subst θ).subst θ' = s.subst θ''
  | .nil, _, _, _, _ => rfl
  | .cons t rest, _, _, _, hθ => by
      simp only [Spine.subst, t.subst_subst hθ, rest.subst_subst hθ]

/-- The same, for the branches of a case. -/
theorem Alts.subst_subst {Γ₁ Γ₂ Γ₃ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool} :
    ∀ (as : Alts Sg Γ₁ τ tags full) {θ : VSub Sg Γ₁ Γ₂} {θ' : VSub Sg Γ₂ Γ₃}
      {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).subst θ') →
      (as.subst θ).subst θ' = as.subst θ''
  | .deflt t, _, _, _, hθ => by simp only [Alts.subst, t.subst_subst hθ]
  | .nilFull, _, _, _, _ => rfl
  | .cons _ t rest, _, _, _, hθ => by
      simp only [Alts.subst, t.subst_subst hθ, rest.subst_subst hθ]

/-- The same, for a tail. -/
theorem Tail.subst_subst {Γ₁ Γ₂ Γ₃ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ₁ Ω τ) {θ : VSub Sg Γ₁ Γ₂} {θ' : VSub Sg Γ₂ Γ₃}
      {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).subst θ') →
      (b.subst θ).subst θ' = b.subst θ''
  | .ret t, _, _, _, hθ => by simp only [Tail.subst, t.subst_subst hθ]
  | .jmp _ args, _, _, _, hθ => by simp only [Tail.subst, args.subst_subst hθ]
  | .letT e b, _, _, _, hθ => by
      simp only [Tail.subst, e.subst_subst hθ, b.subst_subst (VSub.lift_comp hθ)]
  | .iteT c t e, _, _, _, hθ => by
      simp only [Tail.subst, c.subst_subst hθ, t.subst_subst hθ, e.subst_subst hθ]
  | .caseT e alts _, _, _, _, hθ => by
      simp only [Tail.subst, e.subst_subst hθ, alts.subst_subst hθ]
  | .label _ body rest, _, _, _, hθ => by
      simp only [Tail.subst, body.subst_subst (VSub.liftList_comp hθ _),
        rest.subst_subst hθ]

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.subst_subst {Γ₁ Γ₂ Γ₃ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (as : AltsT Sg Γ₁ Ω τ tags full) {θ : VSub Sg Γ₁ Γ₂} {θ' : VSub Sg Γ₂ Γ₃}
      {θ'' : VSub Sg Γ₁ Γ₃},
      (∀ {σ : Ty} (v : Γ₁ ∋ σ), θ'' v = (θ v).subst θ') →
      (as.subst θ).subst θ' = as.subst θ''
  | .deflt b, _, _, _, hθ => by simp only [AltsT.subst, b.subst_subst hθ]
  | .nilFull, _, _, _, _ => rfl
  | .cons _ b rest, _, _, _, hθ => by
      simp only [AltsT.subst, b.subst_subst hθ, rest.subst_subst hθ]

end

/-! ## Substituting by the identity -/

/-- A substitution that changes nothing still changes nothing under a binder. -/
theorem VSub.lift_self {Γ : Ctx} {σ : Ty} {θ : VSub Sg Γ Γ}
    (h : ∀ {τ : Ty} (v : Γ ∋ τ), θ v = .var v) :
    ∀ {τ : Ty} (v : (σ :: Γ) ∋ τ), VSub.lift θ v = .var v
  | _, .head => rfl
  | _, .tail v => by simp [VSub.lift, h v, Term.weaken, Term.rename, VRen.weaken]

/-- The same, under a binder that binds a whole list. -/
theorem VSub.liftList_self {Γ : Ctx} {θ : VSub Sg Γ Γ}
    (h : ∀ {τ : Ty} (v : Γ ∋ τ), θ v = .var v) :
    ∀ (σs : List Ty) {τ : Ty} (v : (σs ++ Γ) ∋ τ), VSub.liftList σs θ v = .var v
  | [], _, v => h v
  | _ :: σs, _, v => VSub.lift_self (VSub.liftList_self h σs) v

mutual

/-- A substitution that gives every variable back itself changes nothing. -/
theorem Term.subst_eq_self {Γ : Ctx} {τ : Ty} :
    ∀ (t : Term Sg Γ τ) {θ : VSub Sg Γ Γ},
      (∀ {σ : Ty} (v : Γ ∋ σ), θ v = .var v) → t.subst θ = t
  | .var v, _, hθ => by simp only [Term.subst, hθ v]
  | .lam b, _, hθ => by simp only [Term.subst, b.subst_eq_self (VSub.lift_self hθ)]
  | .ap f a, _, hθ => by
      simp only [Term.subst, f.subst_eq_self hθ, a.subst_eq_self hθ]
  | .lit _, _, _ => rfl
  | .global _, _, _ => rfl
  | .extern _, _, _ => rfl
  | .lazyMk e, _, hθ => by simp only [Term.subst, e.subst_eq_self hθ]
  | .lazyForce e, _, hθ => by simp only [Term.subst, e.subst_eq_self hθ]
  | .letE e b, _, hθ => by
      simp only [Term.subst, e.subst_eq_self hθ, b.subst_eq_self (VSub.lift_self hθ)]
  | .ite c t e, _, hθ => by
      simp only [Term.subst, c.subst_eq_self hθ, t.subst_eq_self hθ, e.subst_eq_self hθ]
  | .ctor _ _ _ args, _, hθ => by simp only [Term.subst, args.subst_eq_self hθ]
  | .proj e _ _ _ _, _, hθ => by simp only [Term.subst, e.subst_eq_self hθ]
  | .tagOf e _, _, hθ => by simp only [Term.subst, e.subst_eq_self hθ]
  | .caseTag e alts _, _, hθ => by
      simp only [Term.subst, e.subst_eq_self hθ, alts.subst_eq_self hθ]
  | .block b, _, hθ => by simp only [Term.subst, b.subst_eq_self hθ]

/-- The same, for a spine. -/
theorem Spine.subst_eq_self {Γ : Ctx} {σs : List Ty} :
    ∀ (s : Spine Sg Γ σs) {θ : VSub Sg Γ Γ},
      (∀ {σ : Ty} (v : Γ ∋ σ), θ v = .var v) → s.subst θ = s
  | .nil, _, _ => rfl
  | .cons t rest, _, hθ => by
      simp only [Spine.subst, t.subst_eq_self hθ, rest.subst_eq_self hθ]

/-- The same, for the branches of a case. -/
theorem Alts.subst_eq_self {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool} :
    ∀ (as : Alts Sg Γ τ tags full) {θ : VSub Sg Γ Γ},
      (∀ {σ : Ty} (v : Γ ∋ σ), θ v = .var v) → as.subst θ = as
  | .deflt t, _, hθ => by simp only [Alts.subst, t.subst_eq_self hθ]
  | .nilFull, _, _ => rfl
  | .cons _ t rest, _, hθ => by
      simp only [Alts.subst, t.subst_eq_self hθ, rest.subst_eq_self hθ]

/-- The same, for a tail. -/
theorem Tail.subst_eq_self {Γ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ Ω τ) {θ : VSub Sg Γ Γ},
      (∀ {σ : Ty} (v : Γ ∋ σ), θ v = .var v) → b.subst θ = b
  | .ret t, _, hθ => by simp only [Tail.subst, t.subst_eq_self hθ]
  | .jmp _ args, _, hθ => by simp only [Tail.subst, args.subst_eq_self hθ]
  | .letT e b, _, hθ => by
      simp only [Tail.subst, e.subst_eq_self hθ, b.subst_eq_self (VSub.lift_self hθ)]
  | .iteT c t e, _, hθ => by
      simp only [Tail.subst, c.subst_eq_self hθ, t.subst_eq_self hθ, e.subst_eq_self hθ]
  | .caseT e alts _, _, hθ => by
      simp only [Tail.subst, e.subst_eq_self hθ, alts.subst_eq_self hθ]
  | .label _ body rest, _, hθ => by
      simp only [Tail.subst, body.subst_eq_self (VSub.liftList_self hθ _),
        rest.subst_eq_self hθ]

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.subst_eq_self {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (as : AltsT Sg Γ Ω τ tags full) {θ : VSub Sg Γ Γ},
      (∀ {σ : Ty} (v : Γ ∋ σ), θ v = .var v) → as.subst θ = as
  | .deflt b, _, hθ => by simp only [AltsT.subst, b.subst_eq_self hθ]
  | .nilFull, _, _ => rfl
  | .cons _ b rest, _, hθ => by
      simp only [AltsT.subst, b.subst_eq_self hθ, rest.subst_eq_self hθ]

end

/-! ## What the evaluator needs -/

/-- The identity substitution changes nothing. -/
theorem Term.subst_id {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : t.subst VSub.id = t :=
  t.subst_eq_self (fun _ => rfl)

/-- The identity substitution changes no tail. -/
theorem Tail.subst_id {Γ : Ctx} {Ω : LCtx} {τ : Ty} (b : Tail Sg Γ Ω τ) :
    b.subst VSub.id = b :=
  b.subst_eq_self (fun _ => rfl)

/-- **β is an extension of the environment**: substituting under a binder and then
    substituting the variable it binds is one substitution, the environment extended by
    the argument. -/
theorem Term.subst0_subst_lift {Γ₁ Γ₂ : Ctx} {σ τ : Ty}
    (b : Term Sg (σ :: Γ₁) τ) (θ : VSub Sg Γ₁ Γ₂) (a : Term Sg Γ₂ σ) :
    (b.subst θ.lift).subst0 a = b.subst (VSub.cons a θ) := by
  refine b.subst_subst (θ' := VSub.zero a) ?_
  intro ν v
  match v with
  | .head => rfl
  | .tail v =>
      show θ v = ((θ v).weaken).subst (VSub.zero a)
      rw [Term.weaken, Term.subst_rename (θ v) (ρ := VRen.weaken)
        (θ := VSub.zero a) (θ'' := VSub.id) (ρ₀ := VRen.id) (fun _ => rfl)
        (fun _ => rfl), Term.subst_id]
      exact ((θ v).rename_eq_self (fun _ => rfl)).symm

/-- The same, for the tail of a block. -/
theorem Tail.subst0_subst_lift {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {σ τ : Ty}
    (b : Tail Sg (σ :: Γ₁) Ω τ) (θ : VSub Sg Γ₁ Γ₂) (a : Term Sg Γ₂ σ) :
    (b.subst θ.lift).subst0 a = b.subst (VSub.cons a θ) := by
  refine b.subst_subst (θ' := VSub.zero a) ?_
  intro ν v
  match v with
  | .head => rfl
  | .tail v =>
      show θ v = ((θ v).weaken).subst (VSub.zero a)
      rw [Term.weaken, Term.subst_rename (θ v) (ρ := VRen.weaken)
        (θ := VSub.zero a) (θ'' := VSub.id) (ρ₀ := VRen.id) (fun _ => rfl)
        (fun _ => rfl), Term.subst_id]
      exact ((θ v).rename_eq_self (fun _ => rfl)).symm

end LakeJs.Expr

end
