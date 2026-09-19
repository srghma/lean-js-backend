module

public import LakeJs.Expr

@[expose] public section

set_option autoImplicit false

/-!
# Renaming and substitution

A `Term` is intrinsically scoped and intrinsically typed, so each of these operations
keeps both: a renaming maps `Term Sg Γ₁ Ρ₁ τ` to `Term Sg Γ₂ Ρ₂ τ` — the same type,
different contexts — and a substitution likewise.

There are **three** contexts, and an operation for each.

* `VRen`/`VSub` move the **variables**.  `Term.subst0` replaces de Bruijn index `0` by a
  term and shifts the rest down; it is what an inliner and a β-step use.
* `LRen`/`LSub` move the **labels**, and they act on a `Tail` only.  `Tail.lsubst0`
  **inlines a join point**: it replaces every jump to the label just bound by the block
  it names, with the jump's arguments bound in front of it.  Because a label lives in a
  grammar and a context of its own, this traversal cannot confuse one with a variable,
  and it never has to look inside a `Term`.
* `RRen` moves the **recursions**.  There is deliberately no `RSub`: a self-reference is
  not a value, so there is nothing a recursion could be replaced *by*.  Weakening is all
  that is ever needed, and it is what carries a term into the body of a `Term.fix`.

A binder that binds a *list* of things — a join point, and the parameters of a
`Term.fix` — extends the context by `ps ++ Γ`, where de Bruijn index `0` is the **first**
argument; `VRen.liftList` and `VSub.liftList` carry an operation under such a binder.

## A jump binds its arguments

Inlining a join point at a jump by substituting the jump's arguments into the block would
duplicate work when the block reads an argument twice, and would duplicate it even
unevaluated, which is not call-by-value.  `Tail.letSpine` binds **every** argument with a
`let` instead, so a control transfer neither duplicates nor delays a computation.  The
bindings are made innermost-argument-first, which the language cannot tell apart from any
other order, being pure.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

/-! ## Renamings -/

/-- A renaming of variables: every variable of `Γ₁` is a variable of `Γ₂`, at the same
    type. -/
def VRen (Γ₁ Γ₂ : Ctx) : Type := ∀ {τ : Ty}, Γ₁ ∋ τ → Γ₂ ∋ τ

/-- A renaming of labels. -/
def LRen (Ω₁ Ω₂ : LCtx) : Type := ∀ {ps : List Ty}, Ω₁ ∋ₗ ps → Ω₂ ∋ₗ ps

/-- A renaming of recursions. -/
def RRen (Ρ₁ Ρ₂ : RCtx) : Type := ∀ {r : RSig}, Ρ₁ ∋ᵣ r → Ρ₂ ∋ᵣ r

/-- The identity renaming of variables. -/
def VRen.id {Γ : Ctx} : VRen Γ Γ := fun v => v

/-- The identity renaming of labels. -/
def LRen.id {Ω : LCtx} : LRen Ω Ω := fun v => v

/-- The identity renaming of recursions. -/
def RRen.id {Ρ : RCtx} : RRen Ρ Ρ := fun v => v

/-- **There is nothing to jump to in the empty label context**, so a tail written in it
    may be read in any other. -/
def LRen.empty {Ω : LCtx} : LRen [] Ω := fun v => nomatch v

/-- **There is nothing to call in the empty recursion context.** -/
def RRen.empty {Ρ : RCtx} : RRen [] Ρ := fun v => nomatch v

/-- Weakening by one variable. -/
def VRen.weaken {Γ : Ctx} {σ : Ty} : VRen Γ (σ :: Γ) := fun v => .tail v

/-- Weakening by one label. -/
def LRen.weaken {Ω : LCtx} {ps : List Ty} : LRen Ω (ps :: Ω) := fun v => .tail v

/-- Weakening by one recursion: what carries a term into the body of a `Term.fix`. -/
def RRen.weaken {Ρ : RCtx} {r : RSig} : RRen Ρ (r :: Ρ) := fun v => .tail v

/-- Carry a renaming of variables under one binder. -/
def VRen.lift {Γ₁ Γ₂ : Ctx} {σ : Ty} (ρ : VRen Γ₁ Γ₂) : VRen (σ :: Γ₁) (σ :: Γ₂) :=
  fun {_} v =>
    match v with
    | .head => .head
    | .tail v => .tail (ρ v)

/-- Carry a renaming of labels under one label binder. -/
def LRen.lift {Ω₁ Ω₂ : LCtx} {ps : List Ty} (κ : LRen Ω₁ Ω₂) :
    LRen (ps :: Ω₁) (ps :: Ω₂) :=
  fun {_} v =>
    match v with
    | .head => .head
    | .tail v => .tail (κ v)

/-- Carry a renaming of recursions under one `Term.fix`. -/
def RRen.lift {Ρ₁ Ρ₂ : RCtx} {r : RSig} (ξ : RRen Ρ₁ Ρ₂) : RRen (r :: Ρ₁) (r :: Ρ₂) :=
  fun {_} v =>
    match v with
    | .head => .head
    | .tail v => .tail (ξ v)

/-- Weakening by a whole list of variables. -/
def VRen.weakenList {Γ : Ctx} : (σs : List Ty) → VRen Γ (σs ++ Γ)
  | [] => VRen.id
  | _ :: σs => fun v => .tail (VRen.weakenList σs v)

/-- Exchange the two innermost labels. -/
def LRen.swap {Ω : LCtx} {ps qs : List Ty} : LRen (ps :: qs :: Ω) (qs :: ps :: Ω) :=
  fun {_} v =>
    match v with
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail v) => .tail (.tail v)

/-- Carry a renaming of variables under a binder that binds a whole list at once. -/
def VRen.liftList {Γ₁ Γ₂ : Ctx} : (σs : List Ty) → VRen Γ₁ Γ₂ → VRen (σs ++ Γ₁) (σs ++ Γ₂)
  | [], ρ => ρ
  | _ :: σs, ρ => VRen.lift (VRen.liftList σs ρ)

mutual

/-- Rename the variables and the recursions of a term. -/
def Term.rename {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {Ρ₁ Ρ₂ : RCtx} {τ : Ty},
    Term Sg Γ₁ Ρ₁ τ → VRen Γ₁ Γ₂ → RRen Ρ₁ Ρ₂ → Term Sg Γ₂ Ρ₂ τ
  | _, _, _, _, _, .var v, ρ, _ => .var (ρ v)
  | _, _, _, _, _, .lam b, ρ, ξ => .lam (b.rename ρ.lift ξ)
  | _, _, _, _, _, .ap f a, ρ, ξ => .ap (f.rename ρ ξ) (a.rename ρ ξ)
  | _, _, _, _, _, .lit l, _, _ => .lit l
  | _, _, _, _, _, .global r, _, _ => .global r
  | _, _, _, _, _, .extern e, _, _ => .extern e
  | _, _, _, _, _, .lazyMk e, ρ, ξ => .lazyMk (e.rename ρ ξ)
  | _, _, _, _, _, .lazyForce e, ρ, ξ => .lazyForce (e.rename ρ ξ)
  | _, _, _, _, _, .letE e b, ρ, ξ => .letE (e.rename ρ ξ) (b.rename ρ.lift ξ)
  | _, _, _, _, _, .ite c t e, ρ, ξ => .ite (c.rename ρ ξ) (t.rename ρ ξ) (e.rename ρ ξ)
  | _, _, _, _, _, .ctor i fs h args, ρ, ξ => .ctor i fs h (args.rename ρ ξ)
  | _, _, _, _, _, .proj e i j hOne h, ρ, ξ => .proj (e.rename ρ ξ) i j hOne h
  | _, _, _, _, _, .tagOf e h, ρ, ξ => .tagOf (e.rename ρ ξ) h
  | _, _, _, _, _, .structSize e, ρ, ξ => .structSize (e.rename ρ ξ)
  | _, _, _, _, _, .caseTag e alts h, ρ, ξ => .caseTag (e.rename ρ ξ) (alts.rename ρ ξ) h
  | _, _, _, _, _, .block t, ρ, ξ => .block (t.rename ρ LRen.id ξ)
  | _, _, _, _, _, .fix ps k measure body stuck, ρ, ξ =>
      .fix ps k (measure.rename (VRen.liftList ps ρ) ξ)
        (body.rename (VRen.liftList ps ρ) ξ.lift)
        (stuck.rename (VRen.liftList ps ρ) ξ)
  | _, _, _, _, _, .selfCall r args, ρ, ξ => .selfCall (ξ r) (args.rename ρ ξ)

/-- Rename a spine. -/
def Spine.rename {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {Ρ₁ Ρ₂ : RCtx} {σs : List Ty},
    Spine Sg Γ₁ Ρ₁ σs → VRen Γ₁ Γ₂ → RRen Ρ₁ Ρ₂ → Spine Sg Γ₂ Ρ₂ σs
  | _, _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, _, .cons t rest, ρ, ξ => .cons (t.rename ρ ξ) (rest.rename ρ ξ)

/-- Rename the branches of a case. -/
def Alts.rename {Sg : Sig} :
    ∀ {Γ₁ Γ₂ : Ctx} {Ρ₁ Ρ₂ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ₁ Ρ₁ σ τ tags full → VRen Γ₁ Γ₂ → RRen Ρ₁ Ρ₂ → Alts Sg Γ₂ Ρ₂ σ τ tags full
  | _, _, _, _, _, _, _, _, .deflt t, ρ, ξ => .deflt (t.rename ρ ξ)
  | _, _, _, _, _, _, _, _, .nilFull, _, _ => .nilFull
  | _, _, _, _, _, _, _, _, .cons tag fields h t rest, ρ, ξ =>
      .cons tag fields h (t.rename (VRen.liftList fields ρ) ξ) (rest.rename ρ ξ)

/-- Rename the variables, the labels and the recursions of a tail. -/
def Tail.rename {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ₁ Ρ₂ : RCtx} {τ : Ty},
    Tail Sg Γ₁ Ω₁ Ρ₁ τ → VRen Γ₁ Γ₂ → LRen Ω₁ Ω₂ → RRen Ρ₁ Ρ₂ → Tail Sg Γ₂ Ω₂ Ρ₂ τ
  | _, _, _, _, _, _, _, .ret t, ρ, _, ξ => .ret (t.rename ρ ξ)
  | _, _, _, _, _, _, _, .jmp l args, ρ, κ, ξ => .jmp (κ l) (args.rename ρ ξ)
  | _, _, _, _, _, _, _, .letT e b, ρ, κ, ξ => .letT (e.rename ρ ξ) (b.rename ρ.lift κ ξ)
  | _, _, _, _, _, _, _, .iteT c t e, ρ, κ, ξ =>
      .iteT (c.rename ρ ξ) (t.rename ρ κ ξ) (e.rename ρ κ ξ)
  | _, _, _, _, _, _, _, .caseT e alts h, ρ, κ, ξ =>
      .caseT (e.rename ρ ξ) (alts.rename ρ κ ξ) h
  | _, _, _, _, _, _, _, .join ps body rest, ρ, κ, ξ =>
      .join ps (body.rename (VRen.liftList ps ρ) κ ξ) (rest.rename ρ κ.lift ξ)

/-- Rename the branches of a dispatch inside a block. -/
def AltsT.rename {Sg : Sig} :
    ∀ {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ₁ Ρ₂ : RCtx} {σ τ : Ty} {tags : List Nat}
      {full : Bool},
    AltsT Sg Γ₁ Ω₁ Ρ₁ σ τ tags full → VRen Γ₁ Γ₂ → LRen Ω₁ Ω₂ → RRen Ρ₁ Ρ₂ →
      AltsT Sg Γ₂ Ω₂ Ρ₂ σ τ tags full
  | _, _, _, _, _, _, _, _, _, _, .deflt t, ρ, κ, ξ => .deflt (t.rename ρ κ ξ)
  | _, _, _, _, _, _, _, _, _, _, .nilFull, _, _, _ => .nilFull
  | _, _, _, _, _, _, _, _, _, _, .cons tag fields h t rest, ρ, κ, ξ =>
      .cons tag fields h (t.rename (VRen.liftList fields ρ) κ ξ) (rest.rename ρ κ ξ)

end

/-- Weaken a term by one variable. -/
def Term.weaken {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty} (t : Term Sg Γ Ρ τ) :
    Term Sg (σ :: Γ) Ρ τ := t.rename VRen.weaken RRen.id

/-- Weaken a term by one recursion: what carries it into the body of a `Term.fix`. -/
def Term.rweaken {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {r : RSig} {τ : Ty} (t : Term Sg Γ Ρ τ) :
    Term Sg Γ (r :: Ρ) τ := t.rename VRen.id RRen.weaken

/-- Weaken a tail by one variable. -/
def Tail.weaken {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty}
    (b : Tail Sg Γ Ω Ρ τ) : Tail Sg (σ :: Γ) Ω Ρ τ :=
  b.rename VRen.weaken LRen.id RRen.id

/-- Weaken a tail by one label. -/
def Tail.lweaken {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {ps : List Ty} {τ : Ty}
    (b : Tail Sg Γ Ω Ρ τ) : Tail Sg Γ (ps :: Ω) Ρ τ :=
  b.rename VRen.id LRen.weaken RRen.id

/-- **Read a jump-free tail in any label context.** -/
def Tail.lopen {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty}
    (b : Tail Sg Γ [] Ρ τ) : Tail Sg Γ Ω Ρ τ :=
  b.rename VRen.id LRen.empty RRen.id

/-! ## Substituting for variables -/

/-- A substitution: every variable of `Γ₁` is given a term of `Γ₂`, at the same type and
    in the same recursion context. -/
def VSub (Sg : Sig) (Γ₁ Γ₂ : Ctx) (Ρ : RCtx) : Type :=
  ∀ {τ : Ty}, Γ₁ ∋ τ → Term Sg Γ₂ Ρ τ

/-- The substitution that changes nothing. -/
def VSub.id {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} : VSub Sg Γ Γ Ρ := fun v => .var v

/-- Carry a substitution under one binder. -/
def VSub.lift {Sg : Sig} {Γ₁ Γ₂ : Ctx} {Ρ : RCtx} {σ : Ty} (θ : VSub Sg Γ₁ Γ₂ Ρ) :
    VSub Sg (σ :: Γ₁) (σ :: Γ₂) Ρ :=
  fun {_} v =>
    match v with
    | .head => .var .head
    | .tail v => (θ v).weaken

/-- Carry a substitution into the body of a `Term.fix`. -/
def VSub.rlift {Sg : Sig} {Γ₁ Γ₂ : Ctx} {Ρ : RCtx} {r : RSig} (θ : VSub Sg Γ₁ Γ₂ Ρ) :
    VSub Sg Γ₁ Γ₂ (r :: Ρ) :=
  fun v => (θ v).rweaken

/-- Carry a substitution under a binder that binds a whole list at once. -/
def VSub.liftList {Sg : Sig} {Γ₁ Γ₂ : Ctx} {Ρ : RCtx} :
    (σs : List Ty) → VSub Sg Γ₁ Γ₂ Ρ → VSub Sg (σs ++ Γ₁) (σs ++ Γ₂) Ρ
  | [], θ => θ
  | _ :: σs, θ => VSub.lift (VSub.liftList σs θ)

mutual

/-- Apply a substitution to a term. -/
def Term.subst {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {Ρ : RCtx} {τ : Ty},
    Term Sg Γ₁ Ρ τ → VSub Sg Γ₁ Γ₂ Ρ → Term Sg Γ₂ Ρ τ
  | _, _, _, _, .var v, θ => θ v
  | _, _, _, _, .lam b, θ => .lam (b.subst θ.lift)
  | _, _, _, _, .ap f a, θ => .ap (f.subst θ) (a.subst θ)
  | _, _, _, _, .lit l, _ => .lit l
  | _, _, _, _, .global r, _ => .global r
  | _, _, _, _, .extern e, _ => .extern e
  | _, _, _, _, .lazyMk e, θ => .lazyMk (e.subst θ)
  | _, _, _, _, .lazyForce e, θ => .lazyForce (e.subst θ)
  | _, _, _, _, .letE e b, θ => .letE (e.subst θ) (b.subst θ.lift)
  | _, _, _, _, .ite c t e, θ => .ite (c.subst θ) (t.subst θ) (e.subst θ)
  | _, _, _, _, .ctor i fs h args, θ => .ctor i fs h (args.subst θ)
  | _, _, _, _, .proj e i j hOne h, θ => .proj (e.subst θ) i j hOne h
  | _, _, _, _, .tagOf e h, θ => .tagOf (e.subst θ) h
  | _, _, _, _, .structSize e, θ => .structSize (e.subst θ)
  | _, _, _, _, .caseTag e alts h, θ => .caseTag (e.subst θ) (alts.subst θ) h
  | _, _, _, _, .block t, θ => .block (t.subst θ)
  | _, _, _, _, .fix ps k measure body stuck, θ =>
      .fix ps k (measure.subst (VSub.liftList ps θ))
        (body.subst (VSub.liftList ps θ.rlift))
        (stuck.subst (VSub.liftList ps θ))
  | _, _, _, _, .selfCall r args, θ => .selfCall r (args.subst θ)

/-- Apply a substitution to a spine. -/
def Spine.subst {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {Ρ : RCtx} {σs : List Ty},
    Spine Sg Γ₁ Ρ σs → VSub Sg Γ₁ Γ₂ Ρ → Spine Sg Γ₂ Ρ σs
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons t rest, θ => .cons (t.subst θ) (rest.subst θ)

/-- Apply a substitution to the branches of a case. -/
def Alts.subst {Sg : Sig} :
    ∀ {Γ₁ Γ₂ : Ctx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ₁ Ρ σ τ tags full → VSub Sg Γ₁ Γ₂ Ρ → Alts Sg Γ₂ Ρ σ τ tags full
  | _, _, _, _, _, _, _, .deflt t, θ => .deflt (t.subst θ)
  | _, _, _, _, _, _, _, .nilFull, _ => .nilFull
  | _, _, _, _, _, _, _, .cons tag fields h t rest, θ =>
      .cons tag fields h (t.subst (VSub.liftList fields θ)) (rest.subst θ)

/-- Apply a substitution to a tail.  The label context is untouched: a substitution
    replaces values, and a value is not a label. -/
def Tail.subst {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty},
    Tail Sg Γ₁ Ω Ρ τ → VSub Sg Γ₁ Γ₂ Ρ → Tail Sg Γ₂ Ω Ρ τ
  | _, _, _, _, _, .ret t, θ => .ret (t.subst θ)
  | _, _, _, _, _, .jmp l args, θ => .jmp l (args.subst θ)
  | _, _, _, _, _, .letT e b, θ => .letT (e.subst θ) (b.subst θ.lift)
  | _, _, _, _, _, .iteT c t e, θ => .iteT (c.subst θ) (t.subst θ) (e.subst θ)
  | _, _, _, _, _, .caseT e alts h, θ => .caseT (e.subst θ) (alts.subst θ) h
  | _, _, _, _, _, .join ps body rest, θ =>
      .join ps (body.subst (VSub.liftList ps θ)) (rest.subst θ)

/-- Apply a substitution to the branches of a dispatch inside a block. -/
def AltsT.subst {Sg : Sig} :
    ∀ {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool},
    AltsT Sg Γ₁ Ω Ρ σ τ tags full → VSub Sg Γ₁ Γ₂ Ρ → AltsT Sg Γ₂ Ω Ρ σ τ tags full
  | _, _, _, _, _, _, _, _, .deflt t, θ => .deflt (t.subst θ)
  | _, _, _, _, _, _, _, _, .nilFull, _ => .nilFull
  | _, _, _, _, _, _, _, _, .cons tag fields h t rest, θ =>
      .cons tag fields h (t.subst (VSub.liftList fields θ)) (rest.subst θ)

end

/-- The substitution that replaces de Bruijn index `0` by `a` and shifts the rest
    down. -/
def VSub.zero {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σ : Ty} (a : Term Sg Γ Ρ σ) :
    VSub Sg (σ :: Γ) Γ Ρ :=
  fun {_} v =>
    match v with
    | .head => a
    | .tail v => .var v

/-- **β**: the body of a binder, with the bound variable replaced by `a`. -/
def Term.subst0 {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty}
    (b : Term Sg (σ :: Γ) Ρ τ) (a : Term Sg Γ Ρ σ) : Term Sg Γ Ρ τ :=
  b.subst (VSub.zero a)

/-- The same, for a tail: what a `Tail.letT` reduces to. -/
def Tail.subst0 {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty}
    (b : Tail Sg (σ :: Γ) Ω Ρ τ) (a : Term Sg Γ Ρ σ) : Tail Sg Γ Ω Ρ τ :=
  b.subst (VSub.zero a)

/-- The substitution a spine is: the `i`-th parameter of a binder that binds a whole
    list at once goes to the `i`-th term of the spine. -/
def Spine.toSub {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} :
    ∀ {σs : List Ty}, Spine Sg Γ Ρ σs → VSub Sg (σs ++ Γ) Γ Ρ
  | [], .nil => VSub.id
  | _ :: _, .cons t rest => fun v =>
    match v with
    | .head => t
    | .tail v => rest.toSub v

/-- A term under a list binder, with the parameters replaced by the terms of a spine. -/
def Term.instList {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σs : List Ty} {τ : Ty}
    (t : Term Sg (σs ++ Γ) Ρ τ) (args : Spine Sg Γ Ρ σs) : Term Sg Γ Ρ τ :=
  t.subst args.toSub

/-- A tail under a list binder, with the parameters replaced by the terms of a spine. -/
def Tail.instList {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σs : List Ty} {τ : Ty}
    (b : Tail Sg (σs ++ Γ) Ω Ρ τ) (args : Spine Sg Γ Ρ σs) : Tail Sg Γ Ω Ρ τ :=
  b.subst args.toSub

/-! ## Binding the arguments of a jump -/

/-- The parameters of a list binder, as a spine of variables. -/
def Spine.vars {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} : (σs : List Ty) → Spine Sg (σs ++ Γ) Ρ σs
  | [] => .nil
  | _ :: σs => .cons (.var .head) ((Spine.vars (Γ := Γ) (Ρ := Ρ) σs).rename
      VRen.weaken RRen.id)

/-- A block under a list binder, given the arguments of a jump to it: **every** argument
    is bound by a `let` in front of the block.  The bindings are made
    innermost-argument-first; the language is pure, so no other order is observable. -/
def Tail.letSpine {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty} :
    ∀ {σs : List Ty}, Spine Sg Γ Ρ σs → Tail Sg (σs ++ Γ) Ω Ρ τ → Tail Sg Γ Ω Ρ τ
  | [], .nil, body => body
  | _ :: σs, .cons a rest, body =>
      Tail.letSpine rest (.letT (a.rename (VRen.weakenList σs) RRen.id) body)

/-! ## Substituting for labels

**Inlining a join point** replaces every jump to the label it binds by the block it
names, with the arguments of the jump bound in front of it, and leaves every other jump
alone, one label further out.  As with variables, the general operation is a
substitution: every label of `Ω₁` is given a block written in `Ω₂`, in the context its
arguments extend. -/

/-- A substitution of labels: every label of `Ω₁` is given the block it names, a tail of
    `Ω₂` in the context its arguments extend.  A label has no result type, so every block
    answers with the `τ` of the enclosing `Term.block`. -/
def LSub (Sg : Sig) (Γ : Ctx) (Ω₁ Ω₂ : LCtx) (Ρ : RCtx) (τ : Ty) : Type :=
  ∀ {ps : List Ty}, Ω₁ ∋ₗ ps → Tail Sg (ps ++ Γ) Ω₂ Ρ τ

/-- The substitution that changes nothing: every label goes to a jump to itself. -/
def LSub.id {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty} : LSub Sg Γ Ω Ω Ρ τ :=
  fun {ps} v => .jmp v (Spine.vars ps)

/-- Carry a label substitution under one variable binder. -/
def LSub.vlift {Sg : Sig} {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {σ : Ty} {τ : Ty}
    (θ : LSub Sg Γ Ω₁ Ω₂ Ρ τ) : LSub Sg (σ :: Γ) Ω₁ Ω₂ Ρ τ :=
  fun v => (θ v).rename (VRen.liftList _ VRen.weaken) LRen.id RRen.id

/-- Carry a label substitution under a binder that binds a whole list of variables. -/
def LSub.vliftList {Sg : Sig} {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {τ : Ty}
    (σs : List Ty) (θ : LSub Sg Γ Ω₁ Ω₂ Ρ τ) : LSub Sg (σs ++ Γ) Ω₁ Ω₂ Ρ τ :=
  fun v => (θ v).rename (VRen.liftList _ (VRen.weakenList σs)) LRen.id RRen.id

/-- Carry a label substitution under one label binder. -/
def LSub.lift {Sg : Sig} {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {qs : List Ty} {τ : Ty}
    (θ : LSub Sg Γ Ω₁ Ω₂ Ρ τ) : LSub Sg Γ (qs :: Ω₁) (qs :: Ω₂) Ρ τ :=
  fun v =>
    match v with
    | .head => LSub.id .head
    | .tail v => (θ v).lweaken

/-- The substitution that replaces the innermost label by the block `jb`. -/
def LSub.zero {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {ps : List Ty} {τ : Ty}
    (jb : Tail Sg (ps ++ Γ) Ω Ρ τ) : LSub Sg Γ (ps :: Ω) Ω Ρ τ :=
  fun v =>
    match v with
    | .head => jb
    | .tail v => LSub.id v

mutual

/-- Apply a label substitution to a tail.  A `Term` holds no labels, so the terms a tail
    contains are carried over untouched — except inside a `Term.block`, which opens a
    label context of its own and is therefore closed for this traversal. -/
def Tail.lsubst {Sg : Sig} : ∀ {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {τ : Ty},
    Tail Sg Γ Ω₁ Ρ τ → LSub Sg Γ Ω₁ Ω₂ Ρ τ → Tail Sg Γ Ω₂ Ρ τ
  | _, _, _, _, _, .ret t, _ => .ret t
  | _, _, _, _, _, .jmp l args, θ => Tail.letSpine args (θ l)
  | _, _, _, _, _, .letT e b, θ => .letT e (b.lsubst θ.vlift)
  | _, _, _, _, _, .iteT c t e, θ => .iteT c (t.lsubst θ) (e.lsubst θ)
  | _, _, _, _, _, .caseT e alts h, θ => .caseT e (alts.lsubst θ) h
  | _, _, _, _, _, .join ps body rest, θ =>
      .join ps (body.lsubst (LSub.vliftList ps θ)) (rest.lsubst θ.lift)

/-- Apply a label substitution to the branches of a dispatch inside a block. -/
def AltsT.lsubst {Sg : Sig} :
    ∀ {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool},
    AltsT Sg Γ Ω₁ Ρ σ τ tags full → LSub Sg Γ Ω₁ Ω₂ Ρ τ → AltsT Sg Γ Ω₂ Ρ σ τ tags full
  | _, _, _, _, _, _, _, _, .deflt t, θ => .deflt (t.lsubst θ)
  | _, _, _, _, _, _, _, _, .nilFull, _ => .nilFull
  | _, _, _, _, _, _, _, _, .cons tag fields h t rest, θ =>
      .cons tag fields h (t.lsubst (LSub.vliftList fields θ)) (rest.lsubst θ)

end

/-- **Inlining a join point**: the rest of the block, with every jump to the label just
    bound replaced by the block it names, the arguments of the jump bound in front of
    it.  A join point's body cannot jump back to it, so this terminates the label — there
    is nothing left to bind. -/
def Tail.lsubst0 {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {ps : List Ty} {τ : Ty}
    (rest : Tail Sg Γ (ps :: Ω) Ρ τ) (jb : Tail Sg (ps ++ Γ) Ω Ρ τ) : Tail Sg Γ Ω Ρ τ :=
  rest.lsubst (LSub.zero jb)

end LakeJs.Expr

end
