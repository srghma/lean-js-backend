import LakeJs.Lookup
import LakeJs.Rename

/-!
# A peephole optimiser on `Term`

The translation of an LCNF declaration is faithful but verbose: LCNF names every
intermediate value, so a body that is morally `renderExpr` arrives here as
`let v = fun x => (let r = renderExpr x; r); v`.  This pass removes exactly the noise
that shape creates, and nothing else:

* **`let x = e; x`** is `e` — the bound variable is the body, so no substitution is
  needed and nothing can be duplicated;
* **`let x = e; b`** is `b`, when `b` never mentions `x` — every `Term` is a pure,
  total value, so dropping one that is never read changes nothing but the output.  The
  body has to be rebuilt in the smaller context, which is `Term.strengthen?` of
  `LakeJs.Rename`, and that rebuilding *is* the side condition: it succeeds exactly when
  the variable does not occur.  This is the rule that keeps a `const` nobody reads out
  of the emitted module;
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

namespace LakeJs.Simp

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename

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
  | .jsOp (.cast σ' τ') (.cons inner .nil) =>
      (etaApp? (ps := ps) (ret := σ') inner).map fun g =>
        .jsOp (.cast (.fn ps σ') (.fn ps τ')) (.cons g .nil)
  | b => etaApp? (ps := ps) b

/-- Read a term at the type a `JsOp.cast` expects.  The cast's source type is the type
    the bound value had, so this is the identity in every case the rule that uses it can
    produce; the fallback keeps the function total. -/
def Term.coerceCast {Sg : Sig} {Γ : Ctx} {ρ : Ty} (σ : Ty) (t : Term Sg Γ ρ) :
    Term Sg Γ σ :=
  match Term.coerce? σ t with
  | some t' => t'
  | none => .jsOp (.cast ρ σ) (.cons t .nil)

/-- A **closed** value: a literal, a top-level declaration, an extern, or one of those
    read at another type.  A closed term is a term of every context, so it may be put
    under any number of binders unchanged, and each of these prints as itself, so
    duplicating one costs nothing at run time. -/
def closedValue? {Sg : Sig} {Γ : Ctx} : {σ : Ty} → Term Sg Γ σ → Option ((E : Ctx) → Term Sg E σ)
  | _, .lit l => some (fun _ => .lit l)
  | _, .global r => some (fun _ => .global r)
  | _, .extern e => some (fun _ => .extern e)
  | _, .jsOp (.cast σ' τ') (.cons inner .nil) =>
      -- a cast prints as its argument, so reading a closed value at another type is
      -- itself a closed value, and duplicating it costs nothing at run time
      (closedValue? inner).map fun t E => .jsOp (.cast σ' τ') (.cons (t E) .nil)
  | _, _ => none

/-- A bound value that may be substituted for the variable it binds: a *copy* — a
    variable or a closed value (`closedValue?`).  Each of them is a value, so
    substituting it duplicates no work, and a closed one may be put under any number of
    binders unchanged.  `none` is a value that has to stay where it is. -/
def copyOfValue? {Sg : Sig} {Γ : Ctx} {σ : Ty} :
    Term Sg Γ σ → Option (Ren Sg (σ :: Γ) Γ)
  | .var w => some (Ren.substVar w)
  | .jsOp (.cast _ _) (.cons (.var w) .nil) => some (Ren.substCastVar w)
  | t =>
      match closedValue? t with
      | some v => some (Ren.substClosed v)
      | none => none

/-- The body of a `let` when it is the bound variable read at another type.  What comes
    back is how to rebuild that reading from the bound value itself, so the `let`
    disappears and the reinterpretation stays. -/
def castOfHead? {Sg : Sig} {Γ : Ctx} {σ τ : Ty} :
    Term Sg (σ :: Γ) τ → Option (Term Sg Γ σ → Term Sg Γ τ)
  | .jsOp (.cast σ' τ') (.cons (.var .head) .nil) =>
      some (fun e => .jsOp (.cast σ' τ') (.cons (Term.coerceCast σ' e) .nil))
  | _ => none

/-! ## The truncation of `Nat` subtraction, where the guard rules it out

`Nat` subtraction truncates, so `a - b` is `Math.max(0, a - b)` in general.  Where the
program has just tested `n === 0` and taken the other branch, `n - 1` cannot truncate,
and the `Math.max` is waste.  `nonZeroGuard?` recognises the test and
`Term.assumeNonZero` rewrites the branch it guards: the *only* change it makes is
`Nat.sub n 1` (the extern `lean_nat_sub`) into `JsOp.natSubExact n 1`, at one named
variable, so it is exact rather than a "fast arithmetic" option.  Both operations have
the same type, so the rewritten branch is the same `Term Sg Γ τ`.
-/

/-- The `j`-th term of a spine, at the type the spine gives it. -/
def Spine.get? {Sg : Sig} {Γ : Ctx} : {σs : List Ty} → Spine Sg Γ σs → Nat → Option (SomeTerm Sg Γ)
  | _, .nil, _ => none
  | _, .cons t _, 0 => some ⟨_, t⟩
  | _, .cons _ rest, j + 1 => Spine.get? rest j

/-- Field `j` of a value that is *built* right here: reading a field of a constructor
    application is the field itself, and the fields not read are dropped — every `Term`
    is a pure, total value, so dropping one changes nothing but the output.  This is
    what removes the object a scalarised loop would otherwise rebuild. -/
def projOfCtor? {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (e : Term Sg Γ σ) (i j : Nat) :
    Option (Term Sg Γ τ) :=
  match e with
  | .ctor i' _ _ args =>
      if i' == i then (Spine.get? args j).bind fun t => Term.coerce? τ t.2 else none
  | _ => none

/-- The variable a condition branches on, seen through casts. -/
def condVar? {Sg : Sig} {Γ : Ctx} : {τ : Ty} → Term Sg Γ τ → Option Nat
  | _, .var v => some v.index
  | _, .jsOp (.cast _ _) (.cons inner .nil) => condVar? inner
  | _, _ => none

/-- The natural-number literal a term is, seen through casts. -/
def natLit? {Sg : Sig} {Γ : Ctx} : {τ : Ty} → Term Sg Γ τ → Option Nat
  | _, .lit (.nat n) => some n
  | _, .jsOp (.cast _ _) (.cons inner .nil) => natLit? inner
  | _, _ => none

/-- The variable of a test `v === 0`, whichever side of the test it is on. -/
def zeroTestOf? {Sg : Sig} {Γ : Ctx} {σ τ : Ty}
    (a : Term Sg Γ σ) (b : Term Sg Γ τ) : Option Nat :=
  match condVar? a, natLit? b with
  | some i, some 0 => some i
  | _, _ =>
    match natLit? a, condVar? b with
    | some 0, some i => some i
    | _, _ => none

/-- The variable a boolean tests against `0`, as a de Bruijn index: the guard under
    which the *other* branch knows the variable is not zero. -/
def nonZeroGuard? {Sg : Sig} {Γ : Ctx} : {τ : Ty} → Term Sg Γ τ → Option Nat
  | _, .apN (.extern .lean_nat_dec_eq) (.cons a (.cons b .nil)) => zeroTestOf? a b
  | _, .apN (.extern .lean_nat_beq) (.cons a (.cons b .nil)) => zeroTestOf? a b
  -- the test arrives as a `Decidable` read as the boolean it decides, which is a cast
  | _, .jsOp (.cast _ _) (.cons inner .nil) => nonZeroGuard? inner
  | _, _ => none

mutual

/-- Rewrite `n - 1` from the truncating subtraction to the plain one, for the variable
    at de Bruijn index `i`, which the enclosing guard has shown is not zero. -/
def Term.assumeNonZero {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Term Sg Γ τ
  | _, _, .apN (.extern .lean_nat_sub) (.cons (.var v) (.cons (.lit (.nat 1)) .nil)) =>
      if v.index == i then
        .jsOp .natSubExact (.cons (.var v) (.cons (.lit (.nat 1)) .nil))
      else
        .callExtern .lean_nat_sub (.cons (.var v) (.cons (.lit (.nat 1)) .nil))
  | _, _, .var v => .var v
  | _, _, .lit l => .lit l
  | _, _, .global r => .global r
  | _, _, .extern e => .extern e
  | _, _, .jsOp op args => .jsOp op (Spine.assumeNonZero i args)
  | _, _, .lazyMk e => .lazyMk (Term.assumeNonZero i e)
  | _, _, .lazyForce e => .lazyForce (Term.assumeNonZero i e)
  | _, _, .proj e j k h => .proj (Term.assumeNonZero i e) j k h
  | _, _, .tagOf e h => .tagOf (Term.assumeNonZero i e) h
  | _, _, .ite c t e =>
      .ite (Term.assumeNonZero i c) (Term.assumeNonZero i t) (Term.assumeNonZero i e)
  | _, _, .letE e b => .letE (Term.assumeNonZero i e) (Term.assumeNonZero (i + 1) b)
  | _, _, .lamN (params := ps) b => .lamN (Term.assumeNonZero (i + ps.length) b)
  | _, _, .apN f args => .apN (Term.assumeNonZero i f) (Spine.assumeNonZero i args)
  | _, _, .lamProd (params := ps) rets => .lamProd (Spine.assumeNonZero (i + ps.length) rets)
  | _, _, .callProd f args k =>
      .callProd (Term.assumeNonZero i f) (Spine.assumeNonZero i args) k
  | _, _, .ctor j fs h args => .ctor j fs h (Spine.assumeNonZero i args)
  | _, _, .caseTag s alts h => .caseTag (Term.assumeNonZero i s) (Alts.assumeNonZero i alts) h
  | _, _, .loop (σs := σs) init body =>
      .loop (Spine.assumeNonZero i init) (Body.assumeNonZero (i + σs.length) body)
  | _, _, .joinPoint (params := ps) body rest =>
      .joinPoint (Term.assumeNonZero (i + ps.length) body) (Term.assumeNonZero (i + 1) rest)
  | _, _, .jump v args => .jump v (Spine.assumeNonZero i args)

/-- `Term.assumeNonZero`, on every term of a spine. -/
def Spine.assumeNonZero {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Spine Sg Γ σs
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons (Term.assumeNonZero i t) (Spine.assumeNonZero i rest)

/-- `Term.assumeNonZero`, on every branch of a case. -/
def Alts.assumeNonZero {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Alts Sg Γ τ tags
  | _, _, _, .deflt t => .deflt (Term.assumeNonZero i t)
  | _, _, _, .cons tag t rest => .cons tag (Term.assumeNonZero i t) (Alts.assumeNonZero i rest)

/-- `Term.assumeNonZero`, inside a loop body. -/
def Body.assumeNonZero {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Body Sg Γ σs τ
  | _, _, _, .ret t => .ret (Term.assumeNonZero i t)
  | _, _, _, .cont args => .cont (Spine.assumeNonZero i args)
  | _, _, _, .letB e b => .letB (Term.assumeNonZero i e) (Body.assumeNonZero (i + 1) b)
  | _, _, _, .iteB c t e =>
      .iteB (Term.assumeNonZero i c) (Body.assumeNonZero i t) (Body.assumeNonZero i e)
  | _, _, _, .joinPointB (params := ps) body rest =>
      .joinPointB (Term.assumeNonZero (i + ps.length) body)
        (Body.assumeNonZero (i + 1) rest)

end

mutual

/-- The translation often binds the test before branching on it
    (`let c = n === 0; if (c) … else …`).  This carries the fact down to that branch:
    `b` is the de Bruijn index of the boolean the `let` bound and `i` that of the `Nat`
    it tests, and the `else` of the first branch on `b` is rewritten. -/
def Term.guardNonZero {Sg : Sig} (b i : Nat) :
    ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Term Sg Γ τ
  | _, _, .ite c t e =>
      if condVar? c == some b then .ite c t (Term.assumeNonZero i e) else .ite c t e
  | _, _, .letE e body => .letE e (Term.guardNonZero (b + 1) (i + 1) body)
  | _, _, t => t

/-- `Term.guardNonZero`, inside a loop body. -/
def Body.guardNonZero {Sg : Sig} (b i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Body Sg Γ σs τ
  | _, _, _, .iteB c t e =>
      if condVar? c == some b then .iteB c t (Body.assumeNonZero i e) else .iteB c t e
  | _, _, _, .letB e body => .letB e (Body.guardNonZero (b + 1) (i + 1) body)
  | _, _, _, body => body

end

/-! ## One function per rewrite site

The rules of each binding form are collected into a function of the *already simplified*
parts, so that each of them can be named, reasoned about and proved to be a reduction of
the relation in `LakeJs/Reduce.lean`.  `Term.simp` below is then just the bottom-up walk
that applies them. -/

/-- The rules of a projection: reading a field of a value built right here is the field
    itself. -/
def simpProj {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (e' : Term Sg Γ σ) (i j : Nat)
    (h : σ.fieldTy? i j = some τ) : Term Sg Γ τ :=
  match projOfCtor? e' i j with
  | some t => t
  | none => .proj e' i j h

/-- The rules of a conditional: the `else` of a test against `0` knows the value is not
    zero, so the truncating subtraction in it is the plain one. -/
def simpIte {Sg : Sig} {Γ : Ctx} {τ : Ty} (c' : Term Sg Γ (.prim .bool))
    (t' u' : Term Sg Γ τ) : Term Sg Γ τ :=
  match nonZeroGuard? c' with
  | some i => .ite c' t' (Term.assumeNonZero i u')
  | none => .ite c' t' u'

/-- What the body of a `let` becomes when the bound value is a test against `0`: the
    branch the test guards knows the value it tests is not zero. -/
def guardedBody {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (e' : Term Sg Γ σ)
    (b0 : Term Sg (σ :: Γ) τ) : Term Sg (σ :: Γ) τ :=
  match nonZeroGuard? e' with
  | some i => Term.guardNonZero 0 (i + 1) b0
  | none => b0

/-- The rules of a `let` that remain once the guard has been taken into account: the
    `let` that is read straight back, the dead `let` and the copy. -/
def simpLetBody {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (e' : Term Sg Γ σ)
    (b' : Term Sg (σ :: Γ) τ) : Term Sg Γ τ :=
  match b' with
  | .var .head => e'
  | b' =>
    match Term.strengthen? b' with
    | some b'' => b''
    | none =>
      match copyOfValue? e' with
      | some r =>
          match Term.rename? r b' with
          | some b'' => b''
          | none => .letE e' b'
      | none => .letE e' b'

/-- The rules of a `let`: the cast of the bound variable, the guard it establishes, the
    `let` that is read straight back, the dead `let` and the copy. -/
def simpLetE {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (e' : Term Sg Γ σ)
    (b0 : Term Sg (σ :: Γ) τ) : Term Sg Γ τ :=
  match castOfHead? b0 with
  | some rebuild => rebuild e'
  | none => simpLetBody e' (guardedBody e' b0)

/-- The rules of a lambda: eta-contraction, where the body applies a context-independent
    head to the lambda's own parameters in order. -/
def simpLamN {Sg : Sig} {Γ : Ctx} {ps : List Ty} {ret : Ty}
    (b' : Term Sg (ps.reverse ++ Γ) ret) : Term Sg Γ (.fn ps ret) :=
  match etaTarget? (ps := ps) b' with
  | some t => t
  | none => .lamN b'

/-- `guardedBody`, for a loop block. -/
def guardedBodyB {Sg : Sig} {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} (e' : Term Sg Γ σ)
    (b0 : Body Sg (σ :: Γ) σs τ) : Body Sg (σ :: Γ) σs τ :=
  match nonZeroGuard? e' with
  | some i => Body.guardNonZero 0 (i + 1) b0
  | none => b0

/-- The rules of a `let` inside a loop block that remain once the guard has been taken
    into account: the dead binding and the copy. -/
def simpLetBBody {Sg : Sig} {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} (e' : Term Sg Γ σ)
    (b' : Body Sg (σ :: Γ) σs τ) : Body Sg Γ σs τ :=
  match Body.strengthen? b' with
  | some b'' => b''
  | none =>
    match copyOfValue? e' with
    | some r =>
        match Body.rename? r b' with
        | some b'' => b''
        | none => .letB e' b'
    | none => .letB e' b'

/-- The rules of a `let` inside a loop block: the guard, the dead binding and the copy. -/
def simpLetB {Sg : Sig} {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} (e' : Term Sg Γ σ)
    (b0 : Body Sg (σ :: Γ) σs τ) : Body Sg Γ σs τ :=
  simpLetBBody e' (guardedBodyB e' b0)

/-- The rules of a conditional inside a loop block. -/
def simpIteB {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty} (c' : Term Sg Γ (.prim .bool))
    (t' u' : Body Sg Γ σs τ) : Body Sg Γ σs τ :=
  match nonZeroGuard? c' with
  | some i => .iteB c' t' (Body.assumeNonZero i u')
  | none => .iteB c' t' u'

mutual

/-- Simplify a term, bottom up. -/
def Term.simp {Sg : Sig} : ∀ {Γ τ}, Term Sg Γ τ → Term Sg Γ τ
  | _, _, .var v => .var v
  | _, _, .lit l => .lit l
  | _, _, .global r => .global r
  | _, _, .extern e => .extern e
  | _, _, .proj e i j h => simpProj (Term.simp e) i j h
  | _, _, .tagOf e h => .tagOf (Term.simp e) h
  -- the `else` of `n === 0` knows `n` is not zero, so `n - 1` cannot truncate there
  | _, _, .ite c t e => simpIte (Term.simp c) (Term.simp t) (Term.simp e)
  | _, _, .letE e b => simpLetE (Term.simp e) (Term.simp b)
  | _, _, .jsOp op args => .jsOp op (Spine.simp args)
  | _, _, .lazyMk e => .lazyMk (Term.simp e)
  | _, _, .lazyForce e => .lazyForce (Term.simp e)
  | _, _, .lamProd rets => .lamProd (Spine.simp rets)
  | _, _, .callProd f args i => .callProd (Term.simp f) (Spine.simp args) i
  | _, _, .lamN (params := ps) b => simpLamN (ps := ps) (Term.simp b)
  | _, _, .apN f args => .apN (Term.simp f) (Spine.simp args)
  | _, _, .ctor i fs h args => .ctor i fs h (Spine.simp args)
  | _, _, .caseTag s alts h => .caseTag (Term.simp s) (Alts.simp alts) h
  | _, _, .loop init body => .loop (Spine.simp init) (Body.simp body)
  | _, _, .joinPoint body rest => .joinPoint (Term.simp body) (Term.simp rest)
  | _, _, .jump v args => .jump v (Spine.simp args)

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
  | _, _, _, .letB e b => simpLetB (Term.simp e) (Body.simp b)
  | _, _, _, .iteB c t e => simpIteB (Term.simp c) (Body.simp t) (Body.simp e)
  | _, _, _, .joinPointB body rest => .joinPointB (Term.simp body) (Body.simp rest)

end

/-- Simplify to a fixed point of the rules, in practice two passes: a rule may only
    expose the redex another rule matches once the first has fired — substituting a
    literal into the test of a branch is what lets the guard rules see it. -/
def Term.simpAll {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Term Sg Γ τ :=
  Term.simp (Term.simp t)

end LakeJs.Simp
