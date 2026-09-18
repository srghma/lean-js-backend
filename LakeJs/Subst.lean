module

public import LakeJs.Expr

@[expose] public section

/-!
# Renaming and substitution

Everything the evaluator of `LakeJs.Reduce` needs in order to take a step, and nothing
else.  A `Term` is intrinsically scoped and intrinsically typed, so each of these
operations keeps both: a renaming maps `Term Sg Γ₁ τ` to `Term Sg Γ₂ τ` — the same type,
a different context — and a substitution likewise.

There are two contexts, and an operation for each:

* `VRen`/`VSub` move the **variables**.  `Term.subst0` is the one that β-reduction uses:
  it replaces de Bruijn index `0` by a term and shifts the rest down.  A `Term` has no
  labels at all, so a substitution puts terms in wherever they land — no side condition
  is needed to go under a `ƛ`.
* `LRen`/`LSub` move the **labels**, and they only act on a `Tail`.  `Tail.lsubst0` is
  the one the reduction of a `Tail.label` uses: it replaces every jump to the label just
  bound by the block it names.  Because a label lives in a grammar and a context of its
  own, this traversal cannot confuse one with a variable, and it never has to look inside
  a `Term`.

A binder that binds a *list* of things (a label) extends the context by `ps ++ Γ`, where
de Bruijn index `0` is the **first** argument; `VRen.liftList` and `VSub.liftList` are
what carry an operation under such a binder.  `LakeJs.Curry` is the conversion between
that order and the order a curried `ƛ`-chain binds in, written once so that no pass has
to reverse a list by hand.

## A jump binds its arguments

Inlining a label at a jump would substitute the jump's arguments into the block — which
duplicates work when the block reads an argument twice, and duplicates it even
unevaluated, which is not call-by-value.  `Tail.letSpine` binds each non-atomic argument
with a `let` instead, so a control transfer neither duplicates nor delays a computation;
an argument that is a variable or a literal is substituted directly, since copying one of
those costs nothing.  The bindings are made innermost-argument-first, which the language
cannot tell apart from any other order, being pure.
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

/-- The identity renaming of variables. -/
def VRen.id {Γ : Ctx} : VRen Γ Γ := fun v => v

/-- The identity renaming of labels. -/
def LRen.id {Ω : LCtx} : LRen Ω Ω := fun v => v

/-- **There is nothing to jump to in the empty label context**, so a tail written in it
    may be read in any other. -/
def LRen.empty {Ω : LCtx} : LRen [] Ω := fun v => nomatch v

/-- Weakening by one variable. -/
def VRen.weaken {Γ : Ctx} {σ : Ty} : VRen Γ (σ :: Γ) := fun v => .tail v

/-- Weakening by one label. -/
def LRen.weaken {Ω : LCtx} {ps : List Ty} : LRen Ω (ps :: Ω) := fun v => .tail v

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

/-- Carry a renaming of labels into the **body** of a label: the label itself is in scope
    there exactly when it is a loop. -/
def LRen.ext {Ω₁ Ω₂ : LCtx} (self : Bool) (ps : List Ty) (κ : LRen Ω₁ Ω₂) :
    LRen (LCtx.ext self ps Ω₁) (LCtx.ext self ps Ω₂) :=
  match self with
  | true => κ.lift
  | false => κ

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

/-- Rename the variables of a term. -/
def Term.rename {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {τ : Ty},
    Term Sg Γ₁ τ → VRen Γ₁ Γ₂ → Term Sg Γ₂ τ
  | _, _, _, .var v, ρ => .var (ρ v)
  | _, _, _, .lam b, ρ => .lam (b.rename ρ.lift)
  | _, _, _, .ap f a, ρ => .ap (f.rename ρ) (a.rename ρ)
  | _, _, _, .lit l, _ => .lit l
  | _, _, _, .global r, _ => .global r
  | _, _, _, .extern e, _ => .extern e
  | _, _, _, .lazyMk e, ρ => .lazyMk (e.rename ρ)
  | _, _, _, .lazyForce e, ρ => .lazyForce (e.rename ρ)
  | _, _, _, .letE e b, ρ => .letE (e.rename ρ) (b.rename ρ.lift)
  | _, _, _, .ite c t e, ρ => .ite (c.rename ρ) (t.rename ρ) (e.rename ρ)
  | _, _, _, .ctor i fs h args, ρ => .ctor i fs h (args.rename ρ)
  | _, _, _, .proj e i j hOne h, ρ => .proj (e.rename ρ) i j hOne h
  | _, _, _, .tagOf e h, ρ => .tagOf (e.rename ρ) h
  | _, _, _, .caseTag e alts h, ρ => .caseTag (e.rename ρ) (alts.rename ρ) h
  | _, _, _, .block t, ρ => .block (t.rename ρ LRen.id)

/-- Rename a spine. -/
def Spine.rename {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {σs : List Ty},
    Spine Sg Γ₁ σs → VRen Γ₁ Γ₂ → Spine Sg Γ₂ σs
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons t rest, ρ => .cons (t.rename ρ) (rest.rename ρ)

/-- Rename the branches of a case. -/
def Alts.rename {Sg : Sig} :
    ∀ {Γ₁ Γ₂ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ₁ τ tags full → VRen Γ₁ Γ₂ → Alts Sg Γ₂ τ tags full
  | _, _, _, _, _, .deflt t, ρ => .deflt (t.rename ρ)
  | _, _, _, _, _, .nilFull, _ => .nilFull
  | _, _, _, _, _, .cons tag t rest, ρ => .cons tag (t.rename ρ) (rest.rename ρ)

/-- Rename the variables and the labels of a tail. -/
def Tail.rename {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty},
    Tail Sg Γ₁ Ω₁ τ → VRen Γ₁ Γ₂ → LRen Ω₁ Ω₂ → Tail Sg Γ₂ Ω₂ τ
  | _, _, _, _, _, .ret t, ρ, _ => .ret (t.rename ρ)
  | _, _, _, _, _, .jmp l args, ρ, κ => .jmp (κ l) (args.rename ρ)
  | _, _, _, _, _, .letT e b, ρ, κ => .letT (e.rename ρ) (b.rename ρ.lift κ)
  | _, _, _, _, _, .iteT c t e, ρ, κ =>
      .iteT (c.rename ρ) (t.rename ρ κ) (e.rename ρ κ)
  | _, _, _, _, _, .caseT e alts h, ρ, κ => .caseT (e.rename ρ) (alts.rename ρ κ) h
  | _, _, _, _, _, .label (ps := ps) self body rest, ρ, κ =>
      .label self (body.rename (VRen.liftList ps ρ) (κ.ext self ps)) (rest.rename ρ κ.lift)

/-- Rename the branches of a dispatch inside a block. -/
def AltsT.rename {Sg : Sig} :
    ∀ {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat} {full : Bool},
    AltsT Sg Γ₁ Ω₁ τ tags full → VRen Γ₁ Γ₂ → LRen Ω₁ Ω₂ → AltsT Sg Γ₂ Ω₂ τ tags full
  | _, _, _, _, _, _, _, .deflt t, ρ, κ => .deflt (t.rename ρ κ)
  | _, _, _, _, _, _, _, .nilFull, _, _ => .nilFull
  | _, _, _, _, _, _, _, .cons tag t rest, ρ, κ =>
      .cons tag (t.rename ρ κ) (rest.rename ρ κ)

end

/-- Weaken a term by one variable. -/
def Term.weaken {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (t : Term Sg Γ τ) :
    Term Sg (σ :: Γ) τ := t.rename VRen.weaken

/-- Weaken a tail by one variable. -/
def Tail.weaken {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {σ τ : Ty} (b : Tail Sg Γ Ω τ) :
    Tail Sg (σ :: Γ) Ω τ := b.rename VRen.weaken LRen.id

/-- Weaken a tail by one label. -/
def Tail.lweaken {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (b : Tail Sg Γ Ω τ) : Tail Sg Γ (ps :: Ω) τ := b.rename VRen.id LRen.weaken

/-- **Read a jump-free tail in any label context.** -/
def Tail.lopen {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {τ : Ty} (b : Tail Sg Γ [] τ) :
    Tail Sg Γ Ω τ := b.rename VRen.id LRen.empty

/-! ## Substituting for variables -/

/-- A substitution: every variable of `Γ₁` is given a term of `Γ₂`, at the same type. -/
def VSub (Sg : Sig) (Γ₁ Γ₂ : Ctx) : Type :=
  ∀ {τ : Ty}, Γ₁ ∋ τ → Term Sg Γ₂ τ

/-- The substitution that changes nothing. -/
def VSub.id {Sg : Sig} {Γ : Ctx} : VSub Sg Γ Γ := fun v => .var v

/-- Carry a substitution under one binder. -/
def VSub.lift {Sg : Sig} {Γ₁ Γ₂ : Ctx} {σ : Ty} (θ : VSub Sg Γ₁ Γ₂) :
    VSub Sg (σ :: Γ₁) (σ :: Γ₂) :=
  fun {_} v =>
    match v with
    | .head => .var .head
    | .tail v => (θ v).weaken

/-- Carry a substitution under a binder that binds a whole list at once. -/
def VSub.liftList {Sg : Sig} {Γ₁ Γ₂ : Ctx} :
    (σs : List Ty) → VSub Sg Γ₁ Γ₂ → VSub Sg (σs ++ Γ₁) (σs ++ Γ₂)
  | [], θ => θ
  | _ :: σs, θ => VSub.lift (VSub.liftList σs θ)

mutual

/-- Apply a substitution to a term. -/
def Term.subst {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {τ : Ty},
    Term Sg Γ₁ τ → VSub Sg Γ₁ Γ₂ → Term Sg Γ₂ τ
  | _, _, _, .var v, θ => θ v
  | _, _, _, .lam b, θ => .lam (b.subst θ.lift)
  | _, _, _, .ap f a, θ => .ap (f.subst θ) (a.subst θ)
  | _, _, _, .lit l, _ => .lit l
  | _, _, _, .global r, _ => .global r
  | _, _, _, .extern e, _ => .extern e
  | _, _, _, .lazyMk e, θ => .lazyMk (e.subst θ)
  | _, _, _, .lazyForce e, θ => .lazyForce (e.subst θ)
  | _, _, _, .letE e b, θ => .letE (e.subst θ) (b.subst θ.lift)
  | _, _, _, .ite c t e, θ => .ite (c.subst θ) (t.subst θ) (e.subst θ)
  | _, _, _, .ctor i fs h args, θ => .ctor i fs h (args.subst θ)
  | _, _, _, .proj e i j hOne h, θ => .proj (e.subst θ) i j hOne h
  | _, _, _, .tagOf e h, θ => .tagOf (e.subst θ) h
  | _, _, _, .caseTag e alts h, θ => .caseTag (e.subst θ) (alts.subst θ) h
  | _, _, _, .block t, θ => .block (t.subst θ)

/-- Apply a substitution to a spine. -/
def Spine.subst {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {σs : List Ty},
    Spine Sg Γ₁ σs → VSub Sg Γ₁ Γ₂ → Spine Sg Γ₂ σs
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons t rest, θ => .cons (t.subst θ) (rest.subst θ)

/-- Apply a substitution to the branches of a case. -/
def Alts.subst {Sg : Sig} :
    ∀ {Γ₁ Γ₂ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ₁ τ tags full → VSub Sg Γ₁ Γ₂ → Alts Sg Γ₂ τ tags full
  | _, _, _, _, _, .deflt t, θ => .deflt (t.subst θ)
  | _, _, _, _, _, .nilFull, _ => .nilFull
  | _, _, _, _, _, .cons tag t rest, θ => .cons tag (t.subst θ) (rest.subst θ)

/-- Apply a substitution to a tail.  The label context is untouched: a substitution
    replaces values, and a value is not a label. -/
def Tail.subst {Sg : Sig} : ∀ {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {τ : Ty},
    Tail Sg Γ₁ Ω τ → VSub Sg Γ₁ Γ₂ → Tail Sg Γ₂ Ω τ
  | _, _, _, _, .ret t, θ => .ret (t.subst θ)
  | _, _, _, _, .jmp l args, θ => .jmp l (args.subst θ)
  | _, _, _, _, .letT e b, θ => .letT (e.subst θ) (b.subst θ.lift)
  | _, _, _, _, .iteT c t e, θ => .iteT (c.subst θ) (t.subst θ) (e.subst θ)
  | _, _, _, _, .caseT e alts h, θ => .caseT (e.subst θ) (alts.subst θ) h
  | _, _, _, _, .label (ps := ps) self body rest, θ =>
      .label self (body.subst (VSub.liftList ps θ)) (rest.subst θ)

/-- Apply a substitution to the branches of a dispatch inside a block. -/
def AltsT.subst {Sg : Sig} :
    ∀ {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat} {full : Bool},
    AltsT Sg Γ₁ Ω τ tags full → VSub Sg Γ₁ Γ₂ → AltsT Sg Γ₂ Ω τ tags full
  | _, _, _, _, _, _, .deflt t, θ => .deflt (t.subst θ)
  | _, _, _, _, _, _, .nilFull, _ => .nilFull
  | _, _, _, _, _, _, .cons tag t rest, θ => .cons tag (t.subst θ) (rest.subst θ)

end

/-- The substitution that replaces de Bruijn index `0` by `a` and shifts the rest
    down. -/
def VSub.zero {Sg : Sig} {Γ : Ctx} {σ : Ty} (a : Term Sg Γ σ) : VSub Sg (σ :: Γ) Γ :=
  fun {_} v =>
    match v with
    | .head => a
    | .tail v => .var v

/-- **β**: the body of a binder, with the bound variable replaced by `a`. -/
def Term.subst0 {Sg : Sig} {Γ : Ctx} {σ τ : Ty}
    (b : Term Sg (σ :: Γ) τ) (a : Term Sg Γ σ) : Term Sg Γ τ :=
  b.subst (VSub.zero a)

/-- The same, for a tail: what a `Tail.letT` reduces to. -/
def Tail.subst0 {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {σ τ : Ty}
    (b : Tail Sg (σ :: Γ) Ω τ) (a : Term Sg Γ σ) : Tail Sg Γ Ω τ :=
  b.subst (VSub.zero a)

/-- The substitution a spine is: the `i`-th parameter of a binder that binds a whole
    list at once goes to the `i`-th term of the spine. -/
def Spine.toSub {Sg : Sig} {Γ : Ctx} :
    ∀ {σs : List Ty}, Spine Sg Γ σs → VSub Sg (σs ++ Γ) Γ
  | [], .nil => VSub.id
  | _ :: _, .cons t rest => fun v =>
    match v with
    | .head => t
    | .tail v => rest.toSub v

/-- A term under a list binder, with the parameters replaced by the terms of a spine. -/
def Term.instList {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}
    (t : Term Sg (σs ++ Γ) τ) (args : Spine Sg Γ σs) : Term Sg Γ τ :=
  t.subst args.toSub

/-- A tail under a list binder, with the parameters replaced by the terms of a spine. -/
def Tail.instList {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {σs : List Ty} {τ : Ty}
    (b : Tail Sg (σs ++ Γ) Ω τ) (args : Spine Sg Γ σs) : Tail Sg Γ Ω τ :=
  b.subst args.toSub

/-! ## Binding the arguments of a jump

Copying a variable or a literal costs nothing; copying anything else duplicates a
computation, and copying it *unevaluated* is not call-by-value either.  `Tail.letSpine`
is what a jump does with its arguments instead of substituting them: the atomic ones go
in directly, and each of the others is bound by a `let`, which the evaluator runs before
it runs the block. -/

/-- A term that may be copied freely: a variable or a literal. -/
def Term.atomic? {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty},
    Term Sg Γ τ → Option (Term Sg Γ τ)
  | _, _, .var v => some (.var v)
  | _, _, .lit l => some (.lit l)
  | _, _, _ => none

/-- The parameters of a list binder, as a spine of variables. -/
def Spine.vars {Sg : Sig} {Γ : Ctx} : (σs : List Ty) → Spine Sg (σs ++ Γ) σs
  | [] => .nil
  | _ :: σs => .cons (.var .head) ((Spine.vars (Γ := Γ) σs).rename VRen.weaken)

/-- A block under a list binder, given the arguments of a jump to it: an atomic argument
    is substituted, and every other one is bound by a `let`.  The bindings are made
    innermost-argument-first; the language is pure, so no other order is observable. -/
def Tail.letSpine {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ {σs : List Ty}, Spine Sg Γ σs → Tail Sg (σs ++ Γ) Ω τ → Tail Sg Γ Ω τ
  | [], .nil, body => body
  | _ :: σs, .cons a rest, body =>
      match a.atomic? with
      | some a0 =>
          Tail.letSpine rest (body.subst0 (a0.rename (VRen.weakenList σs)))
      | none =>
          Tail.letSpine rest (.letT (a.rename (VRen.weakenList σs)) body)

/-! ## Substituting for labels

Reducing a `Tail.label` replaces every jump to the label it binds by the block it names,
with the arguments of the jump bound in front of it — and leaves every other jump alone,
one label further out.  As with variables, the general operation is a substitution: every
label of `Ω₁` is given a block written in `Ω₂`, in the context its arguments extend. -/

/-- A substitution of labels: every label of `Ω₁` is given the block it names, a tail of
    `Ω₂` in the context its arguments extend.  A label has no result type, so every block
    answers with the `τ` of the enclosing `Term.block`. -/
def LSub (Sg : Sig) (Γ : Ctx) (Ω₁ Ω₂ : LCtx) (τ : Ty) : Type :=
  ∀ {ps : List Ty}, Ω₁ ∋ₗ ps → Tail Sg (ps ++ Γ) Ω₂ τ

/-- The substitution that changes nothing: every label goes to a jump to itself. -/
def LSub.id {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {τ : Ty} : LSub Sg Γ Ω Ω τ :=
  fun {ps} v => .jmp v (Spine.vars ps)

/-- Carry a label substitution under one variable binder. -/
def LSub.vlift {Sg : Sig} {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {σ : Ty} {τ : Ty}
    (θ : LSub Sg Γ Ω₁ Ω₂ τ) : LSub Sg (σ :: Γ) Ω₁ Ω₂ τ :=
  fun v => (θ v).rename (VRen.liftList _ VRen.weaken) LRen.id

/-- Carry a label substitution under a binder that binds a whole list of variables. -/
def LSub.vliftList {Sg : Sig} {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} (σs : List Ty)
    (θ : LSub Sg Γ Ω₁ Ω₂ τ) : LSub Sg (σs ++ Γ) Ω₁ Ω₂ τ :=
  fun v => (θ v).rename (VRen.liftList _ (VRen.weakenList σs)) LRen.id

/-- Carry a label substitution under one label binder. -/
def LSub.lift {Sg : Sig} {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {qs : List Ty} {τ : Ty}
    (θ : LSub Sg Γ Ω₁ Ω₂ τ) : LSub Sg Γ (qs :: Ω₁) (qs :: Ω₂) τ :=
  fun v =>
    match v with
    | .head => LSub.id .head
    | .tail v => (θ v).lweaken

/-- Carry a label substitution into the **body** of a label: the arguments are in scope
    there, and so is the label itself when it is a loop. -/
def LSub.ext {Sg : Sig} {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} (self : Bool) (ps : List Ty)
    (θ : LSub Sg Γ Ω₁ Ω₂ τ) :
    LSub Sg (ps ++ Γ) (LCtx.ext self ps Ω₁) (LCtx.ext self ps Ω₂) τ :=
  match self with
  | true => LSub.lift (LSub.vliftList ps θ)
  | false => LSub.vliftList ps θ

/-- The substitution that replaces the innermost label by the block `jb`. -/
def LSub.zero {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (jb : Tail Sg (ps ++ Γ) Ω τ) : LSub Sg Γ (ps :: Ω) Ω τ :=
  fun v =>
    match v with
    | .head => jb
    | .tail v => LSub.id v

mutual

/-- Apply a label substitution to a tail.  A `Term` holds no labels, so the terms a tail
    contains are carried over untouched. -/
def Tail.lsubst {Sg : Sig} : ∀ {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty},
    Tail Sg Γ Ω₁ τ → LSub Sg Γ Ω₁ Ω₂ τ → Tail Sg Γ Ω₂ τ
  | _, _, _, _, .ret t, _ => .ret t
  | _, _, _, _, .jmp l args, θ => Tail.letSpine args (θ l)
  | _, _, _, _, .letT e b, θ => .letT e (b.lsubst θ.vlift)
  | _, _, _, _, .iteT c t e, θ => .iteT c (t.lsubst θ) (e.lsubst θ)
  | _, _, _, _, .caseT e alts h, θ => .caseT e (alts.lsubst θ) h
  | _, _, _, _, .label (ps := ps) self body rest, θ =>
      .label self (body.lsubst (θ.ext self ps)) (rest.lsubst θ.lift)

/-- Apply a label substitution to the branches of a dispatch inside a block. -/
def AltsT.lsubst {Sg : Sig} :
    ∀ {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat} {full : Bool},
    AltsT Sg Γ Ω₁ τ tags full → LSub Sg Γ Ω₁ Ω₂ τ → AltsT Sg Γ Ω₂ τ tags full
  | _, _, _, _, _, _, .deflt t, θ => .deflt (t.lsubst θ)
  | _, _, _, _, _, _, .nilFull, _ => .nilFull
  | _, _, _, _, _, _, .cons tag t rest, θ => .cons tag (t.lsubst θ) (rest.lsubst θ)

end

/-- **The reduction of a shared tail**: the rest of the block, with every jump to the
    label just bound replaced by the block it names, the arguments of the jump bound in
    front of it. -/
def Tail.lsubst0 {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (rest : Tail Sg Γ (ps :: Ω) τ) (jb : Tail Sg (ps ++ Γ) Ω τ) : Tail Sg Γ Ω τ :=
  rest.lsubst (LSub.zero jb)

/-- **Entering a loop**: the block that a jump to a *self* label runs, namely the loop
    again, entered with the arguments of the jump.  This is what the reduction of a loop
    label substitutes for the label, and the reason a loop needs no unrolling rule of its
    own: re-entering it is jumping to it. -/
def Tail.loopEntry {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (body : Tail Sg (ps ++ Γ) (ps :: Ω) τ) : Tail Sg (ps ++ Γ) Ω τ :=
  .label true (body.rename (VRen.weakenList ps) LRen.id) (.jmp .head (Spine.vars ps))

end LakeJs.Expr

end
