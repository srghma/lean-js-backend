module

public import LakeJs.Expr

@[expose] public section

/-!
# Renaming, strengthening, and the support of a term

A `let` whose bound variable the body never mentions is waste: the emitted module holds
a `const` nobody reads.  Removing it means rebuilding the body in a *smaller* context —
the inverse of weakening — and that is what this file provides.

The tool is a **partial renaming**: a map from the variables of one context to the
variables of another, which may answer `none` for a variable it does not carry over.

* `Ren.drop` is the renaming that removes the variable bound by a `let`: it answers
  `none` for de Bruijn index 0 and shifts everything else down.  Applying it to the body
  of a `let` therefore succeeds exactly when the body never mentions the bound variable,
  which is the side condition of the dead-`let` rule in `LakeJs.Simp`.
* `Ren.liftList` carries a renaming under a list of binders, which is what the language's
  binding forms (`Term.lamN`, `Term.loop`, …) need — they bind a whole list at once.

Everything here keeps the types: a renaming maps `Term Sg Γ τ` to `Term Sg Δ τ`, at the
*same* type, so a strengthened term is still well-scoped, still well-typed and still
refers only to the declarations of the signature.

`Term.usesHead` and `Term.noUnusedLet` are the extrinsic check that goes with the rule:
the first says whether a body mentions the variable a binder just bound, and the second
that no `let` of a term is dead.  `LakeJsTest` asserts the second over the whole
generated corpus, which is the guarantee the emitted JavaScript needs — rather than
indexing `Term` itself by a usage mask, which would make an ordinary declaration that
ignores one of its parameters unrepresentable.
-/

namespace LakeJs.Rename

open LakeJs
open LakeJs.Expr

/-- Where a variable goes: to another variable, or to a **closed** term — one that is a
    term of *every* context, such as a literal, a reference to a top-level declaration or
    an extern.  The closed case is what lets one traversal do both jobs: strengthening
    (which only ever moves variables) and substituting a value for a variable, which is
    what the copy rules of `LakeJs.Simp` need.  A closed term may be put under any number
    of binders without being renamed, which is exactly why the substitution stays a
    renaming and no weakening is needed. -/
inductive RenTarget (Sg : Sig) (Δ : Ctx) (τ : Ty) where
  /-- The variable it becomes. -/
  | var : Var Δ τ → RenTarget Sg Δ τ
  /-- The closed term it becomes, read in whatever context it lands in. -/
  | closed : ((E : Ctx) → Term Sg E τ) → RenTarget Sg Δ τ
  /-- A variable of `Δ` *read at another type*: the term `JsOp.cast` builds from it.
      Reading a value at another type costs nothing at run time — it prints as the
      variable — so substituting one duplicates no work, and it travels under binders as
      the variable does. -/
  | castVar : ∀ {σ : Ty}, Var Δ σ → RenTarget Sg Δ τ

/-- A partial renaming from the variables of `Γ` to the variables of `Δ`, type by type.
    `none` means the variable has no counterpart, so a term that mentions it cannot be
    carried over. -/
structure Ren (Sg : Sig) (Γ Δ : Ctx) where
  /-- Where a variable goes. -/
  map : ∀ {τ : Ty}, Var Γ τ → Option (RenTarget Sg Δ τ)

namespace Ren

/-- The renaming that forgets the most recently bound variable: index 0 has no
    counterpart, and every other index shifts down by one. -/
def drop {Sg : Sig} {Γ : Ctx} {σ : Ty} : Ren Sg (σ :: Γ) Γ where
  map v := match v with
    | .head => none
    | .tail v => some (.var v)

/-- The renaming that replaces the most recently bound variable by another variable of
    the enclosing context: what `let x = y; b` needs. -/
def substVar {Sg : Sig} {Γ : Ctx} {σ : Ty} (w : Var Γ σ) : Ren Sg (σ :: Γ) Γ where
  map v := match v with
    | .head => some (.var w)
    | .tail v => some (.var v)

/-- The renaming that replaces the most recently bound variable by a closed term: what
    `let x = 1; b` and `let x = f; b` need. -/
def substClosed {Sg : Sig} {Γ : Ctx} {σ : Ty} (t : (E : Ctx) → Term Sg E σ) :
    Ren Sg (σ :: Γ) Γ where
  map v := match v with
    | .head => some (.closed t)
    | .tail v => some (.var v)

/-- The renaming that replaces the most recently bound variable by another variable of
    the enclosing context read at the bound type: what `let x = (y : τ); b` needs, where
    the `let` only reinterprets `y`. -/
def substCastVar {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (w : Var Γ σ) : Ren Sg (τ :: Γ) Γ where
  map v := match v with
    | .head => some (.castVar w)
    | .tail v => some (.var v)

/-- Carry a renaming under one binder. -/
def lift {Sg : Sig} {Γ Δ : Ctx} (r : Ren Sg Γ Δ) (σ : Ty) : Ren Sg (σ :: Γ) (σ :: Δ) where
  map v := match v with
    | .head => some (.var .head)
    | .tail v => (r.map v).map fun
        | .var w => .var (.tail w)
        | .closed t => .closed t
        | .castVar w => .castVar (.tail w)

/-- Carry a renaming under a whole list of binders, as `Term.lamN` and `Term.loop`
    bind one. -/
def liftList {Sg : Sig} {Γ Δ : Ctx} : (l : Ctx) → Ren Sg Γ Δ → Ren Sg (l ++ Γ) (l ++ Δ)
  | [], r => r
  | σ :: l, r => (liftList l r).lift σ

end Ren

mutual

/-- Apply a renaming to a term; `none` when the term mentions a variable the renaming
    drops. -/
def Term.rename? {Sg : Sig} {Γ Δ : Ctx} (r : Ren Sg Γ Δ) :
    ∀ {τ : Ty}, Term Sg Γ τ → Option (Term Sg Δ τ)
  | _, .var v => (r.map v).map fun
      | .var w => .var w
      | .closed t => t _
      | .castVar (σ := σ) w => .jsOp (.cast σ _) (.cons (.var w) .nil)
  | _, .lit l => some (.lit l)
  | _, .global g => some (.global g)
  | _, .extern e => some (.extern e)
  | _, .lamN (params := ps) b => (Term.rename? (Ren.liftList ps.reverse r) b).map .lamN
  | _, .apN f args => do
      let f' ← Term.rename? r f
      let args' ← Spine.rename? r args
      pure (.apN f' args')
  | _, .lamProd (params := ps) rets =>
      (Spine.rename? (Ren.liftList ps.reverse r) rets).map .lamProd
  | _, .callProd f args i => do
      let f' ← Term.rename? r f
      let args' ← Spine.rename? r args
      pure (.callProd f' args' i)
  | _, .jsOp op args => (Spine.rename? r args).map (.jsOp op)
  | _, .letE e b => do
      let e' ← Term.rename? r e
      let b' ← Term.rename? (r.lift _) b
      pure (.letE e' b')
  | _, .ite c t e => do
      let c' ← Term.rename? r c
      let t' ← Term.rename? r t
      let e' ← Term.rename? r e
      pure (.ite c' t' e')
  | _, .ctor i fs h args => (Spine.rename? r args).map (.ctor i fs h)
  | _, .proj e i j h => (Term.rename? r e).map (fun e' => .proj e' i j h)
  | _, .tagOf e h => (Term.rename? r e).map (fun e' => .tagOf e' h)
  | _, .caseTag s alts h => do
      let s' ← Term.rename? r s
      let alts' ← Alts.rename? r alts
      pure (.caseTag s' alts' h)
  | _, .loop (σs := σs) init body => do
      let init' ← Spine.rename? r init
      let body' ← Body.rename? (Ren.liftList σs.reverse r) body
      pure (.loop init' body')

/-- `Term.rename?`, on every term of a spine. -/
def Spine.rename? {Sg : Sig} {Γ Δ : Ctx} (r : Ren Sg Γ Δ) :
    ∀ {σs : List Ty}, Spine Sg Γ σs → Option (Spine Sg Δ σs)
  | _, .nil => some .nil
  | _, .cons t rest => do
      let t' ← Term.rename? r t
      let rest' ← Spine.rename? r rest
      pure (.cons t' rest')

/-- `Term.rename?`, on every branch of a case. -/
def Alts.rename? {Sg : Sig} {Γ Δ : Ctx} (r : Ren Sg Γ Δ) :
    ∀ {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Option (Alts Sg Δ τ tags)
  | _, _, .deflt t => (Term.rename? r t).map .deflt
  | _, _, .cons tag t rest => do
      let t' ← Term.rename? r t
      let rest' ← Alts.rename? r rest
      pure (.cons tag t' rest')

/-- `Term.rename?`, inside a loop body. -/
def Body.rename? {Sg : Sig} {Γ Δ : Ctx} (r : Ren Sg Γ Δ) :
    ∀ {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Option (Body Sg Δ σs τ)
  | _, _, .ret t => (Term.rename? r t).map .ret
  | _, _, .cont args => (Spine.rename? r args).map .cont
  | _, _, .letB e b => do
      let e' ← Term.rename? r e
      let b' ← Body.rename? (r.lift _) b
      pure (.letB e' b')
  | _, _, .iteB c t e => do
      let c' ← Term.rename? r c
      let t' ← Body.rename? r t
      let e' ← Body.rename? r e
      pure (.iteB c' t' e')

end

/-- The body of a binder, in the context without the variable it bound: `some b'` when
    the body never mentions that variable, `none` when it does. -/
def Term.strengthen? {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (b : Term Sg (σ :: Γ) τ) :
    Option (Term Sg Γ τ) :=
  Term.rename? Ren.drop b

/-- The body of a loop block, in the context without the variable the enclosing `letB`
    bound. -/
def Body.strengthen? {Sg : Sig} {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty}
    (b : Body Sg (σ :: Γ) σs τ) : Option (Body Sg Γ σs τ) :=
  Body.rename? Ren.drop b

/-- Does the body mention the variable the binder in front of it bound? -/
def Term.usesHead {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (b : Term Sg (σ :: Γ) τ) : Bool :=
  (Term.strengthen? b).isNone

/-- Does the block mention the variable the binder in front of it bound? -/
def Body.usesHead {Sg : Sig} {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty}
    (b : Body Sg (σ :: Γ) σs τ) : Bool :=
  (Body.strengthen? b).isNone

/-! ## The extrinsic check

`noUnusedLet` says that no `let` of a term binds a variable its body never mentions —
the property the dead-`let` rule of `LakeJs.Simp` establishes, and the one the emitted
JavaScript needs, since such a `let` prints as a `const` nobody reads. -/

mutual

/-- Is every `let` of this term read? -/
partial def Term.noUnusedLet {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Bool
  | _, _, .var _ | _, _, .lit _ | _, _, .global _ | _, _, .extern _ => true
  | _, _, .lamN b => Term.noUnusedLet b
  | _, _, .apN f args => Term.noUnusedLet f && Spine.noUnusedLet args
  | _, _, .lamProd rets => Spine.noUnusedLet rets
  | _, _, .callProd f args _ => Term.noUnusedLet f && Spine.noUnusedLet args
  | _, _, .jsOp _ args => Spine.noUnusedLet args
  | _, _, .letE e b => Term.usesHead b && Term.noUnusedLet e && Term.noUnusedLet b
  | _, _, .ite c t e => Term.noUnusedLet c && Term.noUnusedLet t && Term.noUnusedLet e
  | _, _, .ctor _ _ _ args => Spine.noUnusedLet args
  | _, _, .proj e _ _ _ => Term.noUnusedLet e
  | _, _, .tagOf e _ => Term.noUnusedLet e
  | _, _, .caseTag s alts _ => Term.noUnusedLet s && Alts.noUnusedLet alts
  | _, _, .loop init body => Spine.noUnusedLet init && Body.noUnusedLet body

/-- `Term.noUnusedLet`, on every term of a spine. -/
partial def Spine.noUnusedLet {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Bool
  | _, _, .nil => true
  | _, _, .cons t rest => Term.noUnusedLet t && Spine.noUnusedLet rest

/-- `Term.noUnusedLet`, on every branch of a case. -/
partial def Alts.noUnusedLet {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Bool
  | _, _, _, .deflt t => Term.noUnusedLet t
  | _, _, _, .cons _ t rest => Term.noUnusedLet t && Alts.noUnusedLet rest

/-- `Term.noUnusedLet`, inside a loop body. -/
partial def Body.noUnusedLet {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Bool
  | _, _, _, .ret t => Term.noUnusedLet t
  | _, _, _, .cont args => Spine.noUnusedLet args
  | _, _, _, .letB e b => Body.usesHead b && Term.noUnusedLet e && Body.noUnusedLet b
  | _, _, _, .iteB c t e => Term.noUnusedLet c && Body.noUnusedLet t && Body.noUnusedLet e

end

/-! ## Which variables a term reads

`Term.readsIndex i t` is the occurrence check that does *not* rebuild the term: it walks
the term counting binders and asks whether de Bruijn index `i` of the term's own context
is ever read.  That is what reports an unused *parameter*: a parameter belongs to the
type of the function, hence to its calling convention, so it cannot be dropped the way a
dead `let` can — it is reported, not refused. -/

mutual

/-- Is de Bruijn index `i` of the term's context read anywhere in the term?  `depth` is
    how many binders deep the traversal currently is. -/
partial def Term.readsIndexAt (i depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Bool
  | _, _, _, .var v => v.index == i + depth
  | _, _, _, .lit _ | _, _, _, .global _ | _, _, _, .extern _ => false
  | _, _, _, .lamN (params := ps) b => Term.readsIndexAt i (depth + ps.length) b
  | _, _, _, .apN f args => Term.readsIndexAt i depth f || Spine.readsIndexAt i depth args
  | _, _, _, .lamProd (params := ps) rets => Spine.readsIndexAt i (depth + ps.length) rets
  | _, _, _, .callProd f args _ =>
      Term.readsIndexAt i depth f || Spine.readsIndexAt i depth args
  | _, _, _, .jsOp _ args => Spine.readsIndexAt i depth args
  | _, _, _, .letE e b => Term.readsIndexAt i depth e || Term.readsIndexAt i (depth + 1) b
  | _, _, _, .ite c t e =>
      Term.readsIndexAt i depth c || Term.readsIndexAt i depth t || Term.readsIndexAt i depth e
  | _, _, _, .ctor _ _ _ args => Spine.readsIndexAt i depth args
  | _, _, _, .proj e _ _ _ => Term.readsIndexAt i depth e
  | _, _, _, .tagOf e _ => Term.readsIndexAt i depth e
  | _, _, _, .caseTag s alts _ =>
      Term.readsIndexAt i depth s || Alts.readsIndexAt i depth alts
  | _, _, _, .loop (σs := σs) init body =>
      Spine.readsIndexAt i depth init || Body.readsIndexAt i (depth + σs.length) body

/-- `Term.readsIndexAt`, on every term of a spine. -/
partial def Spine.readsIndexAt (i depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Bool
  | _, _, _, .nil => false
  | _, _, _, .cons t rest => Term.readsIndexAt i depth t || Spine.readsIndexAt i depth rest

/-- `Term.readsIndexAt`, on every branch of a case. -/
partial def Alts.readsIndexAt (i depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Bool
  | _, _, _, _, .deflt t => Term.readsIndexAt i depth t
  | _, _, _, _, .cons _ t rest =>
      Term.readsIndexAt i depth t || Alts.readsIndexAt i depth rest

/-- `Term.readsIndexAt`, inside a loop body. -/
partial def Body.readsIndexAt (i depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Bool
  | _, _, _, _, .ret t => Term.readsIndexAt i depth t
  | _, _, _, _, .cont args => Spine.readsIndexAt i depth args
  | _, _, _, _, .letB e b => Term.readsIndexAt i depth e || Body.readsIndexAt i (depth + 1) b
  | _, _, _, _, .iteB c t e =>
      Term.readsIndexAt i depth c || Body.readsIndexAt i depth t || Body.readsIndexAt i depth e

end

/-- Is de Bruijn index `i` of this term's context read? -/
def Term.readsIndex {Sg : Sig} {Γ : Ctx} {τ : Ty} (i : Nat) (t : Term Sg Γ τ) : Bool :=
  Term.readsIndexAt i 0 t

/-- The parameters of a function the body never reads, by their position in the
    parameter list.  A parameter of a `Term.lamN` at position `j` of `n` is de Bruijn
    index `n - 1 - j` of the body. -/
def Term.unusedParams {Sg : Sig} {Γ : Ctx} : ∀ {τ : Ty}, Term Sg Γ τ → List Nat
  | _, .lamN (params := ps) b =>
      let n := ps.length
      (List.range n).filter fun j => !Term.readsIndex (n - 1 - j) b
  | _, _ => []

end LakeJs.Rename
