module

public import LakeJs.SubstLemmas

@[expose] public section

/-!
# Label substitution commutes with value substitution

`LakeJs.SubstLemmas` is the algebra of the **variable** context: renaming, substitution,
and the four ways of composing them.  This module is the missing half — the algebra of
the **label** context — and its one purpose is the equation

```lean
(rest.lsubst0 jb).subst γ = (rest.subst γ).lsubst0 (jb.subst (VSub.liftList ps γ))
```

(`Tail.lsubst0_subst`): *inlining a shared tail and then closing the block is closing the
block and then inlining the shared tail.*  That is exactly the step the join-point
certificate generator of `LakeJs.CertGen` has to take — `StepT.labelJoin` fires on the
*closed* block, while the induction hypothesis speaks about the open one — and it is the
reason `Tail.letSpine` binds every argument of a jump with a `let` instead of copying the
ones that are a variable or a literal: a variable argument is atomic before the block is
closed and an arbitrary value after it, so a copying rule does not commute with `γ`.

The work is organised around one notion, `VSub.Square`: a substitution `θ`, two renamings
`ρ`, `ρ'` and a second substitution `θ'` *commute* when `θ' ∘ ρ = rename ρ' ∘ θ` holds on
variables.  Two squares generate everything needed — weakening by one variable, and
weakening by a whole list — and a square stays a square under `VSub.lift` and
`VSub.liftList`, which is what carries it under the binders of the grammar.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## A commuting square of two renamings and two substitutions -/

/-- **A commuting square.**  Substituting by `θ` and then renaming by `ρ'` is renaming by
    `ρ` and then substituting by `θ'`, as far as the variables are concerned; the syntax
    lemmas below lift that to terms, spines and tails. -/
structure VSub.Square {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} (θ : VSub Sg Γ₁ Γ₂) (ρ : VRen Γ₁ Γ₁')
    (ρ' : VRen Γ₂ Γ₂') (θ' : VSub Sg Γ₁' Γ₂') : Prop where
  /-- The square, on one variable. -/
  app : ∀ {ν : Ty} (v : Γ₁ ∋ ν), θ' (ρ v) = (θ v).rename ρ'

/-- A square stays a square under one binder. -/
theorem VSub.Square.lift {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} {σ : Ty} {θ : VSub Sg Γ₁ Γ₂}
    {ρ : VRen Γ₁ Γ₁'} {ρ' : VRen Γ₂ Γ₂'} {θ' : VSub Sg Γ₁' Γ₂'}
    (h : VSub.Square θ ρ ρ' θ') :
    VSub.Square (VSub.lift (σ := σ) θ) (VRen.lift ρ) (VRen.lift ρ') (VSub.lift θ') where
  app := by
    intro ν v
    match v with
    | .head => rfl
    | .tail w =>
        have hw : θ' (ρ w) = (θ w).rename ρ' := h.app w
        have e1 : ((θ w).rename ρ').rename (VRen.weaken (σ := σ))
            = (θ w).rename (fun x => Var.tail (ρ' x)) :=
          Term.rename_rename (θ w) (fun _ => rfl)
        have e2 : ((θ w).rename (VRen.weaken (σ := σ))).rename (VRen.lift ρ')
            = (θ w).rename (fun x => Var.tail (ρ' x)) :=
          Term.rename_rename (θ w) (fun _ => rfl)
        show (θ' (ρ w)).rename (VRen.weaken (σ := σ))
            = ((θ w).rename (VRen.weaken (σ := σ))).rename (VRen.lift ρ')
        rw [hw, e1, e2]

/-- A square stays a square under a binder that binds a whole list. -/
theorem VSub.Square.liftList {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} {θ : VSub Sg Γ₁ Γ₂}
    {ρ : VRen Γ₁ Γ₁'} {ρ' : VRen Γ₂ Γ₂'} {θ' : VSub Sg Γ₁' Γ₂'}
    (h : VSub.Square θ ρ ρ' θ') :
    ∀ (σs : List Ty),
      VSub.Square (VSub.liftList σs θ) (VRen.liftList σs ρ) (VRen.liftList σs ρ')
        (VSub.liftList σs θ')
  | [] => h
  | _ :: σs => VSub.Square.lift (VSub.Square.liftList h σs)

/-- **Weakening by one variable is a square**: going under a binder on both sides of a
    substitution is the same as weakening before or after it. -/
theorem VSub.square_weaken {Γ₁ Γ₂ : Ctx} {σ : Ty} (θ : VSub Sg Γ₁ Γ₂) :
    VSub.Square θ (VRen.weaken (σ := σ)) (VRen.weaken (σ := σ)) (VSub.lift θ) where
  app := fun _ => rfl

/-- **Weakening by a whole list of variables is a square.** -/
theorem VSub.square_weakenList {Γ₁ Γ₂ : Ctx} (θ : VSub Sg Γ₁ Γ₂) :
    ∀ (ps : List Ty),
      VSub.Square θ (VRen.weakenList ps) (VRen.weakenList ps) (VSub.liftList ps θ)
  | [] => ⟨fun v => (Term.rename_eq_self (θ v) (fun _ => rfl)).symm⟩
  | p :: ps => by
      refine ⟨fun {ν} v => ?_⟩
      have ih : (VSub.liftList ps θ) (VRen.weakenList ps v)
          = (θ v).rename (VRen.weakenList ps) := (VSub.square_weakenList θ ps).app v
      have e : ((θ v).rename (VRen.weakenList ps)).rename (VRen.weaken (σ := p))
          = (θ v).rename (VRen.weakenList (p :: ps)) :=
        Term.rename_rename (θ v) (fun _ => rfl)
      show ((VSub.liftList ps θ) (VRen.weakenList ps v)).rename (VRen.weaken (σ := p))
          = (θ v).rename (VRen.weakenList (p :: ps))
      rw [ih, e]

/-! ## A square commutes on the syntax -/

/-- **A square commutes on a term.** -/
theorem Term.subst_rename_comm {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} {τ : Ty} (t : Term Sg Γ₁ τ)
    {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₁ Γ₁'} {ρ' : VRen Γ₂ Γ₂'} {θ' : VSub Sg Γ₁' Γ₂'}
    (h : VSub.Square θ ρ ρ' θ') : (t.subst θ).rename ρ' = (t.rename ρ).subst θ' := by
  have h1 : (t.subst θ).rename ρ' = t.subst (fun v => (θ v).rename ρ') :=
    Term.rename_subst t (fun _ => rfl)
  have h2 : (t.rename ρ).subst θ' = (t.subst (fun v => θ' (ρ v))).rename VRen.id :=
    Term.subst_rename t (fun _ => rfl) (fun _ => rfl)
  have h3 : (t.subst (fun v => θ' (ρ v))).rename VRen.id = t.subst (fun v => θ' (ρ v)) :=
    Term.rename_eq_self _ (fun _ => rfl)
  have h4 : t.subst (fun v => (θ v).rename ρ') = t.subst (fun v => θ' (ρ v)) :=
    Term.subst_congr t (fun v => (h.app v).symm)
  rw [h1, h2, h3, h4]

/-- **A square commutes on a spine.** -/
theorem Spine.subst_rename_comm {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} {σs : List Ty} (s : Spine Sg Γ₁ σs)
    {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₁ Γ₁'} {ρ' : VRen Γ₂ Γ₂'} {θ' : VSub Sg Γ₁' Γ₂'}
    (h : VSub.Square θ ρ ρ' θ') : (s.subst θ).rename ρ' = (s.rename ρ).subst θ' := by
  have h1 : (s.subst θ).rename ρ' = s.subst (fun v => (θ v).rename ρ') :=
    Spine.rename_subst s (fun _ => rfl)
  have h2 : (s.rename ρ).subst θ' = (s.subst (fun v => θ' (ρ v))).rename VRen.id :=
    Spine.subst_rename s (fun _ => rfl) (fun _ => rfl)
  have h3 : (s.subst (fun v => θ' (ρ v))).rename VRen.id = s.subst (fun v => θ' (ρ v)) :=
    Spine.rename_eq_self _ (fun _ => rfl)
  have h4 : s.subst (fun v => (θ v).rename ρ') = s.subst (fun v => θ' (ρ v)) :=
    Spine.subst_congr s (fun v => (h.app v).symm)
  rw [h1, h2, h3, h4]

/-- **A square commutes on a tail**, whose labels nothing here touches. -/
theorem Tail.subst_rename_comm {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} {Ω : LCtx} {τ : Ty}
    (b : Tail Sg Γ₁ Ω τ) {θ : VSub Sg Γ₁ Γ₂} {ρ : VRen Γ₁ Γ₁'} {ρ' : VRen Γ₂ Γ₂'}
    {θ' : VSub Sg Γ₁' Γ₂'} (h : VSub.Square θ ρ ρ' θ') :
    (b.subst θ).rename ρ' LRen.id = (b.rename ρ LRen.id).subst θ' := by
  have h1 : (b.subst θ).rename ρ' LRen.id = b.subst (fun v => (θ v).rename ρ') :=
    Tail.rename_subst b (fun _ => rfl) (fun _ => rfl)
  have h2 : (b.rename ρ LRen.id).subst θ'
      = (b.subst (fun v => θ' (ρ v))).rename VRen.id LRen.id :=
    Tail.subst_rename b (fun _ => rfl) (fun _ => rfl)
  have h3 : (b.subst (fun v => θ' (ρ v))).rename VRen.id LRen.id
      = b.subst (fun v => θ' (ρ v)) :=
    Tail.rename_eq_self _ (fun _ => rfl) (fun _ => rfl)
  have h4 : b.subst (fun v => (θ v).rename ρ') = b.subst (fun v => θ' (ρ v)) :=
    Tail.subst_congr b (fun v => (h.app v).symm)
  rw [h1, h2, h3, h4]

/-! ## Two facts a jump needs -/

/-- **The parameters of a label are untouched by a substitution carried under them.**
    `Spine.vars` is the spine of the variables the binder itself binds, and a lifted
    substitution is the identity on those. -/
theorem Spine.vars_subst {Γ₁ Γ₂ : Ctx} (θ : VSub Sg Γ₁ Γ₂) :
    ∀ (σs : List Ty),
      (Spine.vars (Sg := Sg) (Γ := Γ₁) σs).subst (VSub.liftList σs θ)
        = Spine.vars (Γ := Γ₂) σs
  | [] => rfl
  | σ :: σs => by
      have ih : (Spine.vars (Sg := Sg) (Γ := Γ₁) σs).subst (VSub.liftList σs θ)
          = Spine.vars (Γ := Γ₂) σs := Spine.vars_subst θ σs
      have hsq :
          ((Spine.vars (Sg := Sg) (Γ := Γ₁) σs).subst (VSub.liftList σs θ)).rename
              (VRen.weaken (σ := σ))
            = ((Spine.vars (Sg := Sg) (Γ := Γ₁) σs).rename VRen.weaken).subst
                (VSub.lift (VSub.liftList σs θ)) :=
        Spine.subst_rename_comm _ (VSub.square_weaken _)
      show Spine.cons ((Term.var (Sg := Sg) Var.head).subst (VSub.lift (VSub.liftList σs θ)))
          (((Spine.vars (Sg := Sg) (Γ := Γ₁) σs).rename VRen.weaken).subst
            (VSub.lift (VSub.liftList σs θ)))
        = Spine.cons (Term.var Var.head)
            ((Spine.vars (Sg := Sg) (Γ := Γ₂) σs).rename VRen.weaken)
      rw [← hsq, ih]
      rfl

/-- **Weakening a tail by one label commutes with substituting its variables.** -/
theorem Tail.lweaken_subst {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (b : Tail Sg Γ₁ Ω τ) (θ : VSub Sg Γ₁ Γ₂) :
    (Tail.lweaken (ps := ps) b).subst θ = Tail.lweaken (b.subst θ) :=
  Tail.subst_rename b (θ'' := θ) (ρ₀ := VRen.id) (fun _ => rfl) (fun _ => rfl)

/-- **Binding the arguments of a jump commutes with substituting the variables.**  Every
    argument is bound by a `let`, so the operation recurses on the spine alone and
    nothing in it inspects the shape of an argument. -/
theorem Tail.letSpine_subst {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ {σs : List Ty} (args : Spine Sg Γ₁ σs) (jb : Tail Sg (σs ++ Γ₁) Ω τ)
      (γ : VSub Sg Γ₁ Γ₂),
      (Tail.letSpine args jb).subst γ
        = Tail.letSpine (args.subst γ) (jb.subst (VSub.liftList σs γ))
  | [], .nil, _, _ => rfl
  | σ :: σs, .cons a rest, jb, γ => by
      have ha : (a.rename (VRen.weakenList σs)).subst (VSub.liftList σs γ)
          = (a.subst γ).rename (VRen.weakenList σs) :=
        (Term.subst_rename_comm a (VSub.square_weakenList γ σs)).symm
      have ih : (Tail.letSpine rest
            (Tail.letT (a.rename (VRen.weakenList σs)) jb)).subst γ
          = Tail.letSpine (rest.subst γ)
              ((Tail.letT (a.rename (VRen.weakenList σs)) jb).subst
                (VSub.liftList σs γ)) :=
        Tail.letSpine_subst rest _ γ
      show (Tail.letSpine rest (Tail.letT (a.rename (VRen.weakenList σs)) jb)).subst γ
          = Tail.letSpine (rest.subst γ)
              (Tail.letT ((a.subst γ).rename (VRen.weakenList σs))
                (jb.subst (VSub.lift (VSub.liftList σs γ))))
      rw [ih]
      show Tail.letSpine (rest.subst γ)
          (Tail.letT ((a.rename (VRen.weakenList σs)).subst (VSub.liftList σs γ))
            (jb.subst (VSub.lift (VSub.liftList σs γ)))) = _
      rw [ha]

/-! ## A label substitution transported through a value substitution -/

/-- **`θ'` is `θ` closed by `γ`**: every block `θ` names, read under the parameters of
    its label and with the variables of the enclosing context substituted by `γ`. -/
structure LSub.Comm {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} (θ : LSub Sg Γ₁ Ω₁ Ω₂ τ)
    (γ : VSub Sg Γ₁ Γ₂) (θ' : LSub Sg Γ₂ Ω₁ Ω₂ τ) : Prop where
  /-- The relation, at one label. -/
  app : ∀ {ps : List Ty} (l : Ω₁ ∋ₗ ps), θ' l = (θ l).subst (VSub.liftList ps γ)

/-- Carrying both under one variable binder preserves the relation. -/
theorem LSub.Comm.vlift {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {σ τ : Ty} {θ : LSub Sg Γ₁ Ω₁ Ω₂ τ}
    {γ : VSub Sg Γ₁ Γ₂} {θ' : LSub Sg Γ₂ Ω₁ Ω₂ τ} (h : LSub.Comm θ γ θ') :
    LSub.Comm (LSub.vlift (σ := σ) θ) (VSub.lift γ) (LSub.vlift θ') where
  app := by
    intro ps l
    have hl : θ' l = (θ l).subst (VSub.liftList ps γ) := h.app l
    have hsq : ((θ l).subst (VSub.liftList ps γ)).rename
          (VRen.liftList ps (VRen.weaken (σ := σ))) LRen.id
        = ((θ l).rename (VRen.liftList ps VRen.weaken) LRen.id).subst
            (VSub.liftList ps (VSub.lift γ)) :=
      Tail.subst_rename_comm (θ l) ((VSub.square_weaken γ).liftList ps)
    show (θ' l).rename (VRen.liftList ps (VRen.weaken (σ := σ))) LRen.id
        = ((θ l).rename (VRen.liftList ps VRen.weaken) LRen.id).subst
            (VSub.liftList ps (VSub.lift γ))
    rw [hl, hsq]

/-- Carrying both under a binder that binds a whole list preserves the relation. -/
theorem LSub.Comm.vliftList {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty}
    {θ : LSub Sg Γ₁ Ω₁ Ω₂ τ} {γ : VSub Sg Γ₁ Γ₂} {θ' : LSub Sg Γ₂ Ω₁ Ω₂ τ}
    (h : LSub.Comm θ γ θ') (σs : List Ty) :
    LSub.Comm (LSub.vliftList σs θ) (VSub.liftList σs γ) (LSub.vliftList σs θ') where
  app := by
    intro ps l
    have hl : θ' l = (θ l).subst (VSub.liftList ps γ) := h.app l
    have hsq : ((θ l).subst (VSub.liftList ps γ)).rename
          (VRen.liftList ps (VRen.weakenList σs)) LRen.id
        = ((θ l).rename (VRen.liftList ps (VRen.weakenList σs)) LRen.id).subst
            (VSub.liftList ps (VSub.liftList σs γ)) :=
      Tail.subst_rename_comm (θ l) ((VSub.square_weakenList γ σs).liftList ps)
    show (θ' l).rename (VRen.liftList ps (VRen.weakenList σs)) LRen.id
        = ((θ l).rename (VRen.liftList ps (VRen.weakenList σs)) LRen.id).subst
            (VSub.liftList ps (VSub.liftList σs γ))
    rw [hl, hsq]

/-- Carrying both under one label binder preserves the relation. -/
theorem LSub.Comm.liftL {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {qs : List Ty} {τ : Ty}
    {θ : LSub Sg Γ₁ Ω₁ Ω₂ τ} {γ : VSub Sg Γ₁ Γ₂} {θ' : LSub Sg Γ₂ Ω₁ Ω₂ τ}
    (h : LSub.Comm θ γ θ') : LSub.Comm (LSub.lift (qs := qs) θ) γ (LSub.lift θ') where
  app := by
    intro ps l
    match l with
    | .head =>
        have hv : (Spine.vars (Sg := Sg) (Γ := Γ₁) qs).subst (VSub.liftList qs γ)
            = Spine.vars (Γ := Γ₂) qs := Spine.vars_subst γ qs
        show Tail.jmp (Ω := qs :: Ω₂) LVar.head (Spine.vars qs)
            = Tail.jmp LVar.head ((Spine.vars (Γ := Γ₁) qs).subst (VSub.liftList qs γ))
        rw [hv]
    | .tail l =>
        have hl : θ' l = (θ l).subst (VSub.liftList ps γ) := h.app l
        have hw : (Tail.lweaken (ps := qs) (θ l)).subst (VSub.liftList ps γ)
            = Tail.lweaken ((θ l).subst (VSub.liftList ps γ)) :=
          Tail.lweaken_subst _ _
        show Tail.lweaken (ps := qs) (θ' l)
            = (Tail.lweaken (ps := qs) (θ l)).subst (VSub.liftList ps γ)
        rw [hl, hw]

/-- Carrying both into the body of a label preserves the relation. -/
theorem LSub.Comm.ext {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {θ : LSub Sg Γ₁ Ω₁ Ω₂ τ}
    {γ : VSub Sg Γ₁ Γ₂} {θ' : LSub Sg Γ₂ Ω₁ Ω₂ τ} (h : LSub.Comm θ γ θ') (self : Bool)
    (ps : List Ty) :
    LSub.Comm (LSub.ext self ps θ) (VSub.liftList ps γ) (LSub.ext self ps θ') := by
  cases self with
  | false => exact h.vliftList ps
  | true => exact (h.vliftList ps).liftL

/-- **The substitution that inlines one block** is transported by closing that block. -/
theorem LSub.Comm.zero {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (jb : Tail Sg (ps ++ Γ₁) Ω τ) (γ : VSub Sg Γ₁ Γ₂) :
    LSub.Comm (LSub.zero jb) γ (LSub.zero (jb.subst (VSub.liftList ps γ))) where
  app := by
    intro qs l
    match l with
    | .head => rfl
    | .tail l =>
        have hv : (Spine.vars (Sg := Sg) (Γ := Γ₁) qs).subst (VSub.liftList qs γ)
            = Spine.vars (Γ := Γ₂) qs := Spine.vars_subst γ qs
        show Tail.jmp (Ω := Ω) l (Spine.vars qs)
            = Tail.jmp l ((Spine.vars (Γ := Γ₁) qs).subst (VSub.liftList qs γ))
        rw [hv]

/-! ## The commutation -/

mutual

/-- **Inlining blocks for labels commutes with substituting the variables.** -/
theorem Tail.lsubst_subst {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ₁ Ω₁ τ) {θ : LSub Sg Γ₁ Ω₁ Ω₂ τ} {γ : VSub Sg Γ₁ Γ₂}
      {θ' : LSub Sg Γ₂ Ω₁ Ω₂ τ},
      LSub.Comm θ γ θ' → (b.lsubst θ).subst γ = (b.subst γ).lsubst θ'
  | .ret _, _, _, _, _ => rfl
  | .jmp (ps := ps) l args, θ, γ, θ', h => by
      have e1 : (Tail.letSpine args (θ l)).subst γ
          = Tail.letSpine (args.subst γ) ((θ l).subst (VSub.liftList ps γ)) :=
        Tail.letSpine_subst args (θ l) γ
      have e2 : θ' l = (θ l).subst (VSub.liftList ps γ) := h.app l
      show (Tail.letSpine args (θ l)).subst γ = Tail.letSpine (args.subst γ) (θ' l)
      rw [e1, e2]
  | .letT e b, θ, γ, θ', h => by
      have ih : (b.lsubst θ.vlift).subst γ.lift = (b.subst γ.lift).lsubst θ'.vlift :=
        Tail.lsubst_subst b h.vlift
      show Tail.letT (e.subst γ) ((b.lsubst θ.vlift).subst γ.lift)
          = Tail.letT (e.subst γ) ((b.subst γ.lift).lsubst θ'.vlift)
      rw [ih]
  | .iteT c t e, θ, γ, θ', h => by
      have iht : (t.lsubst θ).subst γ = (t.subst γ).lsubst θ' := Tail.lsubst_subst t h
      have ihe : (e.lsubst θ).subst γ = (e.subst γ).lsubst θ' := Tail.lsubst_subst e h
      show Tail.iteT (c.subst γ) ((t.lsubst θ).subst γ) ((e.lsubst θ).subst γ)
          = Tail.iteT (c.subst γ) ((t.subst γ).lsubst θ') ((e.subst γ).lsubst θ')
      rw [iht, ihe]
  | .caseT e alts hc, θ, γ, θ', h => by
      have ih : (alts.lsubst θ).subst γ = (alts.subst γ).lsubst θ' :=
        AltsT.lsubst_subst alts h
      show Tail.caseT (e.subst γ) ((alts.lsubst θ).subst γ) hc
          = Tail.caseT (e.subst γ) ((alts.subst γ).lsubst θ') hc
      rw [ih]
  | .label (ps := ps) self body rest, θ, γ, θ', h => by
      have ihb : (body.lsubst (θ.ext self ps)).subst (VSub.liftList ps γ)
          = (body.subst (VSub.liftList ps γ)).lsubst (θ'.ext self ps) :=
        Tail.lsubst_subst body (h.ext self ps)
      have ihr : (rest.lsubst θ.lift).subst γ = (rest.subst γ).lsubst θ'.lift :=
        Tail.lsubst_subst rest h.liftL
      show Tail.label self ((body.lsubst (θ.ext self ps)).subst (VSub.liftList ps γ))
            ((rest.lsubst θ.lift).subst γ)
          = Tail.label self ((body.subst (VSub.liftList ps γ)).lsubst (θ'.ext self ps))
            ((rest.subst γ).lsubst θ'.lift)
      rw [ihb, ihr]
  termination_by b => sizeOf b

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.lsubst_subst {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (alts : AltsT Sg Γ₁ Ω₁ τ tags full) {θ : LSub Sg Γ₁ Ω₁ Ω₂ τ} {γ : VSub Sg Γ₁ Γ₂}
      {θ' : LSub Sg Γ₂ Ω₁ Ω₂ τ},
      LSub.Comm θ γ θ' → (alts.lsubst θ).subst γ = (alts.subst γ).lsubst θ'
  | .deflt b, θ, γ, θ', h => by
      have ih : (b.lsubst θ).subst γ = (b.subst γ).lsubst θ' := Tail.lsubst_subst b h
      show AltsT.deflt ((b.lsubst θ).subst γ) = AltsT.deflt ((b.subst γ).lsubst θ')
      rw [ih]
  | .nilFull, _, _, _, _ => rfl
  | .cons tag b rest, θ, γ, θ', h => by
      have ih : (b.lsubst θ).subst γ = (b.subst γ).lsubst θ' := Tail.lsubst_subst b h
      have ihr : (rest.lsubst θ).subst γ = (rest.subst γ).lsubst θ' :=
        AltsT.lsubst_subst rest h
      show AltsT.cons tag ((b.lsubst θ).subst γ) ((rest.lsubst θ).subst γ)
          = AltsT.cons tag ((b.subst γ).lsubst θ') ((rest.subst γ).lsubst θ')
      rw [ih, ihr]
  termination_by alts => sizeOf alts

end

/-- **Inlining a shared tail commutes with closing the block.**  This is the equation the
    join-point certificate generator needs: the block that `StepT.labelJoin` produces
    from the *closed* label is the closure of the block it produces from the open one. -/
theorem Tail.lsubst0_subst {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (rest : Tail Sg Γ₁ (ps :: Ω) τ) (jb : Tail Sg (ps ++ Γ₁) Ω τ) (γ : VSub Sg Γ₁ Γ₂) :
    (rest.lsubst0 jb).subst γ
      = (rest.subst γ).lsubst0 (jb.subst (VSub.liftList ps γ)) :=
  Tail.lsubst_subst rest (LSub.Comm.zero jb γ)

end LakeJs.Expr

end
