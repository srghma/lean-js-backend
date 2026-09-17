import LakeJs.Simp

/-!
# Inlining a call of a top-level declaration

`@[inline] def foo a b := …` followed by `def bar := foo 1 2` should not leave a call in
the emitted module: `bar` should hold `foo`'s body with `1` and `2` in it.  That is what
this pass does, on `Term` rather than on the JavaScript, so the result is still a
well-scoped, well-typed term of the same signature and the passes downstream —
`LakeJs.Simp`, `LakeJs.Scalarise`, `LakeJs.Specialise` — see the inlined body and keep
optimising it.

## What a call becomes

A declaration the backend has already translated is a **closed** term
`Term Sg [] (.fn params ret)`, so a saturated call of it is `Term.apN (.global r) args`
with `args : Spine Sg Γ params`, and the body of the declaration is a term in
`params.reverse ++ []` — a context whose variables are exactly the parameters.  The
inlined call is therefore the body, read in `Γ` through the map that sends parameter `i`
to argument `i`: a `Ren` of `LakeJs.Rename`, applied with `Term.rename?`.

Two things follow, and they are the reason the pass is this short:

* **nothing is duplicated.**  `Ren` carries a variable or a *value* — a literal, a
  global, an extern, or one of those read at another type — and nothing else, so an
  argument that is a computation is not substituted and the call is left alone.  The
  terms the translation produces are in administrative normal form, so the arguments of
  a call are variables and literals in practice, and the pass fires;
* **nothing can go wrong in the types.**  `Ren` maps a variable to a target *at its own
  type*, and `Term.rename?` is type-preserving, so the inlined body is a term of the type
  the call had.  A wrong arity or a mismatched argument type cannot be built at all: the
  spine of the call has the parameter types of the declaration by construction.

## Which declarations are inlined

The table is built by `LakeJs.Compile`, which translates the declarations of a module
callees-first, so the body a call site inlines is the body *after* the callee's own
optimisation.  A declaration goes into the table when Lean marks it `@[inline]` or
`@[macro_inline]`, or when its body is small (`Term.nodeCount`), and never when it is
marked `@[noinline]`, when it is a member of a merged mutually-recursive group, when it
is an unboxed instance, or when its body still mentions its own name.  That last
condition is what makes the pass terminate: every entry of the table is a term that has
already been inlined into, and it never refers to itself, so expanding a call once is the
whole of the work.
-/

namespace LakeJs.Inline

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename
open LakeJs.Simp

/-! ## The table of inlinable declarations -/

/-- The declarations a call site may inline: the JavaScript name of each, and the closed
    term the backend translated it to. -/
abbrev Table (Sg : Sig) := List (String × Σ τ : Ty, Term Sg [] τ)

/-- The body a name is bound to, at the type the call site uses it at.  The signature's
    names are unique (`Sig.namesUnique`, checked in `LakeJs.Compile`), so at most one
    entry can match, and the type is checked rather than assumed. -/
def Table.lookup? {Sg : Sig} (tbl : Table Sg) (name : String) (τ : Ty) :
    Option (Term Sg [] τ) :=
  match List.find? (fun e => e.1 == name) tbl with
  | some e => Term.coerce? τ e.2.2
  | none => none

/-! ## Substituting the arguments of a call for the parameters -/

/-- Where each variable of a context goes: one `RenTarget` per entry, in order.  This is
    a `Ren` given by a list rather than by a function, which is what lets one be built
    from the spine of a call. -/
inductive Sub (Sg : Sig) (Δ : Ctx) : Ctx → Type
  | nil : Sub Sg Δ []
  | cons : ∀ {τ : Ty} {Γ : Ctx}, RenTarget Sg Δ τ → Sub Sg Δ Γ → Sub Sg Δ (τ :: Γ)

/-- Where a variable goes, under a `Sub`. -/
def Sub.get {Sg : Sig} {Δ : Ctx} :
    ∀ {Γ : Ctx} {τ : Ty}, Sub Sg Δ Γ → Var Γ τ → RenTarget Sg Δ τ
  | _, _, .cons t _, .head => t
  | _, _, .cons _ rest, .tail v => Sub.get rest v

/-- The total renaming a `Sub` is. -/
def Sub.toRen {Sg : Sig} {Γ Δ : Ctx} (s : Sub Sg Δ Γ) : Ren Sg Γ Δ where
  map v := some (s.get v)

/-- An argument that may be substituted for a parameter: a variable, a variable read at
    another type, or a closed value.  Each of them is a value, so substituting it — even
    for a parameter the body reads twice, or none at all — duplicates no work and drops
    none.  Anything else answers `none`, and the call it belongs to is left alone. -/
def argTarget? {Sg : Sig} {Γ : Ctx} {σ : Ty} (t : Term Sg Γ σ) :
    Option (RenTarget Sg Γ σ) :=
  match t with
  | .var w => some (.var w)
  | .jsOp (.cast _ _) (.cons (.var w) .nil) => some (.castVar w)
  | t => (LakeJs.Simp.closedValue? t).map RenTarget.closed

/-- The substitution a spine of arguments is, for the context a lambda over those
    parameters binds.  Inside `Term.lamN`, parameter `0` is the *deepest* variable, so
    the spine is consumed front to back onto the accumulator, which reverses it. -/
def subOfSpine {Sg : Sig} {Γ : Ctx} :
    ∀ {σs : List Ty} {acc : Ctx}, Spine Sg Γ σs → Sub Sg Γ acc →
      Option (Sub Sg Γ (σs.reverse ++ acc))
  | [], _, .nil, s => some s
  | σ :: _, acc, .cons t rest, s => do
      let tgt ← argTarget? t
      let r ← subOfSpine rest (Sub.cons tgt s)
      return (by
        show Sub Sg Γ ((σ :: _).reverse ++ acc)
        rw [List.reverse_cons, List.append_assoc]
        exact r)

/-- The body of `.lamN` under a list of binders, when the term is one. -/
def lamBody? {Sg : Sig} {params : List Ty} {ret : Ty} :
    Term Sg [] (.fn params ret) → Option (Term Sg (params.reverse ++ []) ret)
  | .lamN b => some b
  | _ => none

/-- A saturated call of an inlinable declaration, as the body of that declaration with
    the arguments of the call in place of its parameters. -/
def betaGlobal? {Sg : Sig} {Γ : Ctx} {params : List Ty} {ret : Ty} (tbl : Table Sg)
    (r : GlobalRef Sg (.fn params ret)) (args : Spine Sg Γ params) :
    Option (Term Sg Γ ret) := do
  let t ← tbl.lookup? r.name (.fn params ret)
  let body ← lamBody? t
  let sub ← subOfSpine (acc := []) args Sub.nil
  Term.rename? sub.toRen body

/-- A reference to a declaration whose body is a literal: the literal itself, read in
    whatever context the reference stands in.  A computation is *not* inlined this way —
    a nullary declaration is evaluated once when the module is loaded, and copying it to
    its uses would evaluate it once per use. -/
def litGlobal? {Sg : Sig} {Γ : Ctx} {τ : Ty} (tbl : Table Sg) (r : GlobalRef Sg τ) :
    Option (Term Sg Γ τ) := do
  let t ← tbl.lookup? r.name τ
  match t with
  | .lit l => some (.lit l)
  | _ => none

/-! ## The rules, one function per site

Each rule is a function of the *already inlined* parts, in the style of `LakeJs.Simp`, so
that it can be named and reasoned about on its own; `Term.inlineCalls` below is the
bottom-up walk that applies them. -/

/-- The rule of an application: a saturated call of a declaration of the table is that
    declaration's body. -/
def inlineApN {Sg : Sig} {Γ : Ctx} {ps : List Ty} {ret : Ty} (tbl : Table Sg)
    (f' : Term Sg Γ (.fn ps ret)) (args' : Spine Sg Γ ps) : Term Sg Γ ret :=
  match f' with
  | .global r =>
      match betaGlobal? tbl r args' with
      | some t => t
      | none => .apN (.global r) args'
  | f' => .apN f' args'

/-- The rule of a reference to a declaration: a constant whose body is a literal is that
    literal. -/
def inlineGlobal {Sg : Sig} {Γ : Ctx} {τ : Ty} (tbl : Table Sg) (r : GlobalRef Sg τ) :
    Term Sg Γ τ :=
  match litGlobal? tbl r with
  | some t => t
  | none => .global r

/-! ## The pass -/

mutual

/-- Inline the calls of the table's declarations, everywhere in a term. -/
def Term.inlineCalls {Sg : Sig} (tbl : Table Sg) :
    ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Term Sg Γ τ
  | _, _, .var v => .var v
  | _, _, .lit l => .lit l
  | _, _, .global r => inlineGlobal tbl r
  | _, _, .extern e => .extern e
  | _, _, .lamN b => .lamN (Term.inlineCalls tbl b)
  | _, _, .apN f args =>
      inlineApN tbl (Term.inlineCalls tbl f) (Spine.inlineCalls tbl args)
  | _, _, .lamProd rets => .lamProd (Spine.inlineCalls tbl rets)
  | _, _, .callProd f args i =>
      .callProd (Term.inlineCalls tbl f) (Spine.inlineCalls tbl args) i
  | _, _, .jsOp op args => .jsOp op (Spine.inlineCalls tbl args)
  | _, _, .letE e b => .letE (Term.inlineCalls tbl e) (Term.inlineCalls tbl b)
  | _, _, .ite c t u =>
      .ite (Term.inlineCalls tbl c) (Term.inlineCalls tbl t) (Term.inlineCalls tbl u)
  | _, _, .ctor i fs h args => .ctor i fs h (Spine.inlineCalls tbl args)
  | _, _, .proj e i j h => .proj (Term.inlineCalls tbl e) i j h
  | _, _, .tagOf e h => .tagOf (Term.inlineCalls tbl e) h
  | _, _, .caseTag s alts h => .caseTag (Term.inlineCalls tbl s) (Alts.inlineCalls tbl alts) h
  | _, _, .loop init body =>
      .loop (Spine.inlineCalls tbl init) (Body.inlineCalls tbl body)

/-- `Term.inlineCalls`, on every term of a spine. -/
def Spine.inlineCalls {Sg : Sig} (tbl : Table Sg) :
    ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Spine Sg Γ σs
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons (Term.inlineCalls tbl t) (Spine.inlineCalls tbl rest)

/-- `Term.inlineCalls`, on every branch of a case. -/
def Alts.inlineCalls {Sg : Sig} (tbl : Table Sg) :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Alts Sg Γ τ tags
  | _, _, _, .deflt t => .deflt (Term.inlineCalls tbl t)
  | _, _, _, .cons tag t rest =>
      .cons tag (Term.inlineCalls tbl t) (Alts.inlineCalls tbl rest)

/-- `Term.inlineCalls`, inside a loop body. -/
def Body.inlineCalls {Sg : Sig} (tbl : Table Sg) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Body Sg Γ σs τ
  | _, _, _, .ret t => .ret (Term.inlineCalls tbl t)
  | _, _, _, .cont args => .cont (Spine.inlineCalls tbl args)
  | _, _, _, .letB e b => .letB (Term.inlineCalls tbl e) (Body.inlineCalls tbl b)
  | _, _, _, .iteB c t u =>
      .iteB (Term.inlineCalls tbl c) (Body.inlineCalls tbl t) (Body.inlineCalls tbl u)

end

/-! ## How big a term is

The size of the body is what decides whether a declaration Lean said nothing about is
worth inlining: a small one costs less inlined than called, and a large one would be
copied to every call site. -/

mutual

/-- The number of nodes of a term. -/
def Term.nodeCount {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Nat
  | _, _, .var _ => 1
  | _, _, .lit _ => 1
  | _, _, .global _ => 1
  | _, _, .extern _ => 1
  | _, _, .lamN b => Term.nodeCount b + 1
  | _, _, .apN f args => Term.nodeCount f + Spine.nodeCount args + 1
  | _, _, .lamProd rets => Spine.nodeCount rets + 1
  | _, _, .callProd f args _ => Term.nodeCount f + Spine.nodeCount args + 1
  | _, _, .jsOp _ args => Spine.nodeCount args + 1
  | _, _, .letE e b => Term.nodeCount e + Term.nodeCount b + 1
  | _, _, .ite c t u => Term.nodeCount c + Term.nodeCount t + Term.nodeCount u + 1
  | _, _, .ctor _ _ _ args => Spine.nodeCount args + 1
  | _, _, .proj e _ _ _ => Term.nodeCount e + 1
  | _, _, .tagOf e _ => Term.nodeCount e + 1
  | _, _, .caseTag s alts _ => Term.nodeCount s + Alts.nodeCount alts + 1
  | _, _, .loop init body => Spine.nodeCount init + Body.nodeCount body + 1

/-- `Term.nodeCount`, summed over a spine. -/
def Spine.nodeCount {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Nat
  | _, _, .nil => 0
  | _, _, .cons t rest => Term.nodeCount t + Spine.nodeCount rest

/-- `Term.nodeCount`, summed over the branches of a case. -/
def Alts.nodeCount {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Nat
  | _, _, _, .deflt t => Term.nodeCount t
  | _, _, _, .cons _ t rest => Term.nodeCount t + Alts.nodeCount rest

/-- `Term.nodeCount`, inside a loop body. -/
def Body.nodeCount {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Nat
  | _, _, _, .ret t => Term.nodeCount t + 1
  | _, _, _, .cont args => Spine.nodeCount args + 1
  | _, _, _, .letB e b => Term.nodeCount e + Body.nodeCount b + 1
  | _, _, _, .iteB c t u => Term.nodeCount c + Body.nodeCount t + Body.nodeCount u + 1

end

mutual

/-- Does a term branch or loop?  Where Lean said nothing about a declaration, only a
    straight-line body — a chain of `let`s ending in an expression — is inlined: a loop
    copied to each of its call sites costs the whole loop once per site, and a branch
    copied into a position that is an expression has to be printed as a block inside an
    arrow function, which is bigger than the call it replaced. -/
def hasControlFlowTerm {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Bool
  | _, _, .var _ | _, _, .lit _ | _, _, .global _ | _, _, .extern _ => false
  | _, _, .lamN b => hasControlFlowTerm b
  | _, _, .apN f args => hasControlFlowTerm f || hasControlFlowSpine args
  | _, _, .lamProd rets => hasControlFlowSpine rets
  | _, _, .callProd f args _ => hasControlFlowTerm f || hasControlFlowSpine args
  | _, _, .jsOp _ args => hasControlFlowSpine args
  | _, _, .letE e b => hasControlFlowTerm e || hasControlFlowTerm b
  | _, _, .ite _ _ _ => true
  | _, _, .ctor _ _ _ args => hasControlFlowSpine args
  | _, _, .proj e _ _ _ => hasControlFlowTerm e
  | _, _, .tagOf e _ => hasControlFlowTerm e
  | _, _, .caseTag _ _ _ => true
  | _, _, .loop _ _ => true

/-- `hasControlFlowTerm`, over a spine. -/
def hasControlFlowSpine {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Bool
  | _, _, .nil => false
  | _, _, .cons t rest => hasControlFlowTerm t || hasControlFlowSpine rest

end

/-- Is a translated declaration worth inlining at its call sites, when Lean itself said
    nothing about it?  Its body has to be a lambda — a nullary declaration is a value
    computed once — small enough that copying it is cheaper than calling it, and free of
    branches and loops (`hasControlFlowTerm`). -/
def worthInlining {Sg : Sig} (limit : Nat) : (Σ τ : Ty, Term Sg [] τ) → Bool
  | ⟨.fn _ _, t@(.lamN _)⟩ => Term.nodeCount t ≤ limit && !hasControlFlowTerm t
  | _ => false

/-- The body of a declaration is a lambda over its parameters: only such a declaration
    can be inlined at a saturated call, which is the only call the pass rewrites. -/
def isLambda {Sg : Sig} : (Σ τ : Ty, Term Sg [] τ) → Bool
  | ⟨.fn _ _, .lamN _⟩ => true
  | _ => false

end LakeJs.Inline
