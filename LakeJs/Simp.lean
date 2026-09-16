module

public import LakeJs.Lookup

@[expose] public section

namespace LakeJs.Simp

/-!
# A peephole optimiser on `Term`

The translation of an LCNF declaration is faithful but verbose: LCNF names every
intermediate value, so a body that is morally `renderExpr` arrives here as
`let v = fun x => (let r = renderExpr x; r); v`.  This pass removes exactly the noise
that shape creates, and nothing else:

* **`let x = e; x`** is `e` — the bound variable is the body, so no substitution is
  needed and nothing can be duplicated;
* **`fun x0 … xn => f(x0, …, xn)`** is `f`, when `f` is a top-level declaration or an
  extern.  Those two are the only heads that mean the same thing in every context, so
  they are the only ones this rule can move out of the binders without a renaming.

Both rules preserve the type of the term — they are functions
`Term Sg Γ τ → Term Sg Γ τ` — so the result is still well-scoped, still well-typed and
still refers only to declarations of the signature.  This is the sense in which keeping
the types (rather than reading the erased phases of the compiler) buys something: an
optimisation cannot silently produce an ill-typed program, because an ill-typed program
is not a `Term`.
-/


/-- Is this spine the `n` parameters of an enclosing lambda, in order?  Inside
    `Term.lamN`, parameter `j` of `n` is de Bruijn index `n - 1 - j`. -/
def isIdentitySpine {Sg : Sig} {Γ : Ctx} (n : Nat) : {σs : List Ty} → Spine Sg Γ σs → Nat → Bool
  | _, .nil, j => j == n
  | _, .cons t rest, j =>
      match t with
      | .var v => v.index == n - 1 - j && isIdentitySpine n rest (j + 1)
      | _ => false

/-- The body of a lambda, when it is the application of a *context-independent* head —
    a global or an extern — to the lambda's own parameters in order.  The head is then
    the lambda itself, one binder out. -/
def etaApp? {Sg : Sig} {Γ : Ctx} {ps : List Ty} {ret : Ty} :
    Term Sg (ps.reverse ++ Γ) ret → Option (Term Sg Γ (.fn ps ret))
  | .apN (params := ps') f spine =>
      if isIdentitySpine ps.length spine 0 then
        match f with
        | .global r =>
            if h : ps' = ps then some (h ▸ (Term.global r : Term Sg Γ (.fn ps' ret)))
            else none
        | .extern e =>
            if h : ps' = ps then some (h ▸ (Term.extern e : Term Sg Γ (.fn ps' ret)))
            else none
        | _ => none
      else none
  | _ => none

/-- The head of a lambda whose body is its own parameters applied to a global or an
    extern, possibly read at another type.  Reading a value at another type costs nothing
    at run time, so the reading moves out of the binders together with the head. -/
def etaTarget? {Sg : Sig} {Γ : Ctx} {ps : List Ty} {ret : Ty} :
    Term Sg (ps.reverse ++ Γ) ret → Option (Term Sg Γ (.fn ps ret))
  | .prim (.cast σ' τ') (.cons inner .nil) =>
      (etaApp? (ps := ps) (ret := σ') inner).map fun g =>
        .prim (.cast (.fn ps σ') (.fn ps τ')) (.cons g .nil)
  | b => etaApp? (ps := ps) b

/-- Read a term at the type a `JsPrim.cast` expects.  The cast's source type is the type
    the bound value had, so this is the identity in every case the rule that uses it can
    produce; the fallback keeps the function total. -/
def Term.coerceCast {Sg : Sig} {Γ : Ctx} {ρ : Ty} (σ : Ty) (t : Term Sg Γ ρ) :
    Term Sg Γ σ :=
  match Term.coerce? σ t with
  | some t' => t'
  | none => .prim (.cast ρ σ) (.cons t .nil)

/-- The body of a `let` when it is the bound variable read at another type.  What comes
    back is how to rebuild that reading from the bound value itself, so the `let`
    disappears and the reinterpretation stays. -/
def castOfHead? {Sg : Sig} {Γ : Ctx} {σ τ : Ty} :
    Term Sg (σ :: Γ) τ → Option (Term Sg Γ σ → Term Sg Γ τ)
  | .prim (.cast σ' τ') (.cons (.var .head) .nil) =>
      some (fun e => .prim (.cast σ' τ') (.cons (Term.coerceCast σ' e) .nil))
  | _ => none

mutual

/-- Simplify a term, bottom up. -/
def Term.simp {Sg : Sig} : ∀ {Γ τ}, Term Sg Γ τ → Term Sg Γ τ
  | _, _, .var v => .var v
  | _, _, .lit l => .lit l
  | _, _, .global r => .global r
  | _, _, .extern e => .extern e
  | _, _, .proj e i j h => .proj (Term.simp e) i j h
  | _, _, .tagOf e h => .tagOf (Term.simp e) h
  | _, _, .ite c t e => .ite (Term.simp c) (Term.simp t) (Term.simp e)
  | _, _, .letE e b =>
      let e' := Term.simp e
      let b' := Term.simp b
      -- `let x = e; cast x` is `cast e`: the cast is not a value, it is how the
      -- translation records that it read the value at another type
      match castOfHead? b' with
      | some rebuild => rebuild e'
      | none =>
        match b' with
        -- `let x = e; x` is `e`
        | .var .head => e'
        | b' => .letE e' b'
  | _, _, .prim op args => .prim op (Spine.simp args)
  | _, _, .lamProd rets => .lamProd (Spine.simp rets)
  | _, _, .callProd f args i => .callProd (Term.simp f) (Spine.simp args) i
  | _, _, .lamN (params := ps) b =>
      let b' := Term.simp b
      match etaTarget? (ps := ps) b' with
      | some t => t
      | none => .lamN b'
  | _, _, .apN f args => .apN (Term.simp f) (Spine.simp args)
  | _, _, .ctor i fs h args => .ctor i fs h (Spine.simp args)
  | _, _, .caseTag s alts h => .caseTag (Term.simp s) (Alts.simp alts) h
  | _, _, .loop init body => .loop (Spine.simp init) (Body.simp body)

/-- `Term.simp`, on every term of a spine. -/
def Spine.simp {Sg : Sig} : ∀ {Γ σs}, Spine Sg Γ σs → Spine Sg Γ σs
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons (Term.simp t) (Spine.simp rest)

/-- `Term.simp`, on every branch of a case. -/
def Alts.simp {Sg : Sig} : ∀ {Γ τ} {tags : List Nat}, Alts Sg Γ τ tags → Alts Sg Γ τ tags
  | _, _, _, .deflt t => .deflt (Term.simp t)
  | _, _, _, .cons tag t rest => .cons tag (Term.simp t) (Alts.simp rest)

/-- `Term.simp`, inside a loop body. -/
def Body.simp {Sg : Sig} : ∀ {Γ σs τ}, Body Sg Γ σs τ → Body Sg Γ σs τ
  | _, _, _, .ret t => .ret (Term.simp t)
  | _, _, _, .cont args => .cont (Spine.simp args)
  | _, _, _, .letB e b => .letB (Term.simp e) (Body.simp b)
  | _, _, _, .iteB c t e => .iteB (Term.simp c) (Body.simp t) (Body.simp e)

end

end LakeJs.Simp
