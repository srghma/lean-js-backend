module
public import LakeJs.Ty
public import LakeJs.Layout
public import LakeJs.Externs
@[expose] public section

/-!
# `Term`: the well-scoped, simply-typed core the backend compiles to

`Term Sg Γ τ` is the intermediate language of the JavaScript backend.  It is
*intrinsically* scoped (a variable is a de Bruijn index into `Γ`, so a free variable is
unrepresentable), *intrinsically* typed (its function space is the simply-typed one of
`LakeJs.Ty`), and *intrinsically* linked (a reference to a top-level declaration is an
index into the module signature `Sg`, so a call to a name the module does not declare is
unrepresentable).

Four consequences matter for the backend, and they are the reason the language looks the
way it does:

* **An Omega-style self-application is not a `Term`.**  `Term.ap` asks for a function of
  type `.fn [σ] τ` and an argument of type `σ`, so `x x` would need `σ = .fn [σ] τ`,
  which `Ty.ne_arrow_self` (in `LakeJs.TermTotal`) shows is impossible.  There is no
  fixed-point combinator and no recursive `Term` constructor either.
* **Recursion is a loop.**  The only way a `Term` repeats work is `Term.loop`, whose body
  is a `Body`: a block that either answers (`Body.ret`) or goes round again with new
  values for the loop variables (`Body.cont`).  That is exactly a JavaScript `while`
  loop with an accumulator per parameter, which is what `LakeJs.EmitJs` prints.
* **Every name a term mentions is declared.**  `Term.global` takes a `GlobalRef Sg τ`,
  a de Bruijn index into the signature of the module being emitted, and the type `τ` it
  is used at is the type the signature gives it.  There is no way to build a call to an
  undeclared name, or to call a declared one at the wrong type.
* **Every operation is applied at its own type.**  `JsPrim` is *indexed* by the list of
  its argument types and by its result type, and `Externs` (the catalogue of the
  functions Lean implements with `@[extern]`, in `LakeJs.Externs`) by its type, so
  `Term.prim` and `Term.extern` cannot be applied to the wrong number of arguments or to
  arguments of the wrong type.

So a declaration only reaches this language if the backend has already turned its
recursion into iteration, and a declaration Lean did not prove terminating never gets
that far: `LakeJs.Totality` refuses it before the translation starts.
-/

abbrev Ctx := List Ty

-- Variable index in context
inductive Var : Ctx → Ty → Type
  | head : ∀ {Γ τ}, Var (τ :: Γ) τ
  | tail : ∀ {Γ τ1 τ2}, Var Γ τ1 → Var (τ2 :: Γ) τ1

-- Membership notation: Γ ∋ τ
infix:40 " ∋ " => Var

-- Macro to expand a natural number literal into nested Var.tail / Var.head
syntax "var_get_elem" (ppSpace term) : term
macro_rules | `(term| var_get_elem $n) => match n.1.toNat with
| 0     => `(term| Var.head)
| n + 1 => `(term| Var.tail (var_get_elem $(Lean.quote n)))

-- Sugar: ♯0 expands to Var.head, ♯1 expands to Var.tail Var.head, etc.
macro "v♯" n:term:90 : term => `(var_get_elem $n)

/-- The de Bruijn index of a variable: how many binders out it is. -/
def Var.index : ∀ {Γ : Ctx} {τ : Ty}, Γ ∋ τ → Nat
  | _, _, .head => 0
  | _, _, .tail v => Var.index v + 1

/-! ## The signature of a module

A `Term` is written against a fixed list of top-level declarations — the ones the
emitted JavaScript module binds, plus the ones it imports from the runtime.  A reference
to one of them is a `GlobalRef`, an index into that list, so the *name* and the *type* of
a global are read off the signature rather than being written at the use site.
-/

/-- One top-level declaration a term may refer to: the JavaScript name it is bound to,
    and its type. -/
structure GlobalDecl where
  /-- The JavaScript identifier the declaration is bound to. -/
  name : String
  /-- Its type. -/
  ty : Ty

/-- The signature of the module being emitted: every top-level name a `Term` of it may
    mention. -/
abbrev Sig := List GlobalDecl -- TODO names should be unique

/-- A reference to a declaration of the signature — a de Bruijn index into `Sg`, whose
    type is the one the signature gives it.  There is no other way to name a global, so
    a `Term` cannot call a name that is not declared, nor call a declared one at a type
    it does not have. -/
inductive GlobalRef : Sig → Ty → Type
  | here  : ∀ {g : GlobalDecl} {Sg : Sig}, GlobalRef (g :: Sg) g.ty
  | there : ∀ {g : GlobalDecl} {Sg : Sig} {τ : Ty}, GlobalRef Sg τ → GlobalRef (g :: Sg) τ

/-- The JavaScript name a reference resolves to. -/
def GlobalRef.name : ∀ {Sg : Sig} {τ : Ty}, GlobalRef Sg τ → String
  | _, _, .here (g := g) => g.name
  | _, _, .there r => r.name

/-- Look a name up in a signature, whatever type it was declared at.  Looking one up
    *at* a given type is this together with `decide (σ = τ)`: `Ty` has ordinary
    decidable equality (`LakeJs.Ty`), so no partial equality of types is needed. -/
def GlobalRef.findAny? : (Sg : Sig) → (name : String) → Option (Σ τ : Ty, GlobalRef Sg τ)
  | [], _ => none
  | g :: Sg, nm =>
    if g.name == nm then some ⟨g.ty, GlobalRef.here⟩
    else (GlobalRef.findAny? Sg nm).map fun r => ⟨r.1, .there r.2⟩

/-! ## Literals -/

/-- A constant of a terminal type. -/
inductive Lit : Ty → Type
  | nat    : Nat → Lit (.prim .nat)
  | int    : Int → Lit (.prim .int)
  | bool   : Bool → Lit (.prim .bool)
  | str    : String → Lit (.prim .string)
  | char   : Char → Lit (.prim .char)
  /-- A `Float`, spelled by its decimal rendering so that the printer stays
      deterministic. -/
  | float  : String → Lit (.prim .float)

/-! ## Primitive operations

`JsPrim σs τ` is an operation the backend prints inline — an operator or a method of the
JavaScript standard library — *together with its type*: it takes arguments of types `σs`
and answers with a `τ`.  Applying one to the wrong number of arguments, or to arguments
of the wrong types, is therefore not a `Term`; the printer needs no fallback for an
arity it does not know, because there is none. -/

inductive JsPrim : List Ty → Ty → Type where
  /-- `a + b` on numbers of type `τ`. -/
  | add (τ : Ty) : JsPrim [τ, τ] τ
  /-- `a - b`, without the `Nat` truncation. -/
  | sub (τ : Ty) : JsPrim [τ, τ] τ
  /-- `Math.max(0, a - b)`: subtraction on `Nat`. -/
  | natSub : JsPrim [.nat, .nat] .nat
  | mul (τ : Ty) : JsPrim [τ, τ] τ
  | div (τ : Ty) : JsPrim [τ, τ] τ
  | mod (τ : Ty) : JsPrim [τ, τ] τ
  | lt (τ : Ty) : JsPrim [τ, τ] .bool
  | le (τ : Ty) : JsPrim [τ, τ] .bool
  | gt (τ : Ty) : JsPrim [τ, τ] .bool
  | ge (τ : Ty) : JsPrim [τ, τ] .bool
  /-- `a === b`. -/
  | beq (τ : Ty) : JsPrim [τ, τ] .bool
  /-- `a !== b`. -/
  | bne (τ : Ty) : JsPrim [τ, τ] .bool
  | and : JsPrim [.bool, .bool] .bool
  | or : JsPrim [.bool, .bool] .bool
  | not : JsPrim [.bool] .bool
  /-- `a + b` on strings. -/
  | strAppend : JsPrim [.string, .string] .string
  /-- `a.length`. -/
  | strLength : JsPrim [.string] .nat
  /-- `a.charAt(i)`. -/
  | strGet : JsPrim [.string, .nat] .char
  /-- `(a) | 0`: the 32-bit truncation Lean's `Int` arithmetic gets. -/
  | toInt32 : JsPrim [.int] .int
  /-- `a.length` of an array. -/
  | arraySize (α : Ty) : JsPrim [.array α] .nat
  /-- `a[i]`. -/
  | arrayGet (α : Ty) : JsPrim [.array α, .nat] α
  /-- `[...a, x]`. -/
  | arrayPush (α : Ty) : JsPrim [.array α, α] (.array α)
  /-- `[]`. -/
  | arrayEmpty (α : Ty) : JsPrim [] (.array α)
  /-- `a[a.length - 1]`. -/
  | arrayBack (α : Ty) : JsPrim [.array α] α
  /-- `String(a)`. -/
  | toStr (τ : Ty) : JsPrim [τ] .string
  /-- `Math.abs(a)`. -/
  | natAbs : JsPrim [.int] .nat
  /-- The argument itself, read at another type: a coercion that costs nothing at run
      time, such as the one between a `Decidable` and the boolean it decides, or the one
      between a value of a type parameter (`Ty.typeParam`) and the type the context
      knows it to have.  It prints as the argument, so the reinterpretation is visible
      in the term and invisible in the output. -/
  | cast (σ τ : Ty) : JsPrim [σ] τ

/-! ## Terms -/

mutual

/-- A well-scoped, simply-typed term of the module whose signature is `Sg`. -/
inductive Term (Sg : Sig) : Ctx → Ty → Type
  | var : ∀ {Γ τ}, Γ ∋ τ → Term Sg Γ τ
  -- Lambda.  `Ty.fn` is uncurried, so a lambda binds *all* the parameters of its type at
  -- once: `Term.lam`/`Term.ap` below are the one-parameter special case, which is what
  -- `ƛ` and `⬝` still mean.
  | lamN : ∀ {Γ params ret}, Term Sg (params.reverse ++ Γ) ret → Term Sg Γ (.fn params ret)
  | apN  : ∀ {Γ params ret}, Term Sg Γ (.fn params ret) → Spine Sg Γ params → Term Sg Γ ret
  /-- A lambda that answers with several values at once: its body is the list of them,
      and it prints as `(v0, v1) => { return [e0, e1]; }`.  This is the only way to
      build a `Ty.fn_returnsProd`, so such a function always does return a tuple. -/
  | lamProd : ∀ {Γ params r1 rs},
      Spine Sg (params.reverse ++ Γ) (r1 :: rs) → Term Sg Γ (.fn_returnsProd params r1 rs)
  /-- Call a function that answers with several values at once and keep the `i`-th of
      them: `f(a, b)[i]`.  The index is a `Fin`, so it is in range, and the type of the
      term is the type that result has — a component of a tuple cannot be read at the
      wrong type, and a tuple cannot be handled other than by reading its components. -/
  | callProd : ∀ {Γ params r1 rs},
      Term Sg Γ (.fn_returnsProd params r1 rs) → Spine Sg Γ params →
      (i : Fin (rs.length + 1)) → Term Sg Γ ((r1 :: rs).get i)
  /-- A constant. -/
  | lit : ∀ {Γ τ}, Lit τ → Term Sg Γ τ
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ τ}, GlobalRef Sg τ → Term Sg Γ τ
  /-- A function Lean implements with `@[extern]`, named by the catalogue
      `LakeJs.Externs` and therefore carrying its own type. -/
  | extern : ∀ {Γ τ}, Externs τ → Term Sg Γ τ
  /-- A primitive operation, printed inline, applied to exactly the arguments its type
      asks for. -/
  | prim : ∀ {Γ σs τ}, JsPrim σs τ → Spine Sg Γ σs → Term Sg Γ τ
  /-- `let x = e; body` — `x` is de Bruijn index 0 of `body`. -/
  | letE : ∀ {Γ σ τ}, Term Sg Γ σ → Term Sg (σ :: Γ) τ → Term Sg Γ τ
  /-- `c ? t : e`. -/
  | ite : ∀ {Γ τ}, Term Sg Γ (.prim .bool) → Term Sg Γ τ → Term Sg Γ τ → Term Sg Γ τ
  /-- A tagged value: `{ tag: 1, _1: …, _2: … }`, built **at a type whose layout says
      so**.  `h` is the evidence that `τ` has a constructor number `i`, and which
      fields it has; the arguments are then a spine of exactly those types.  So a
      constructor cannot be built at a type that has no such constructor, with a field
      missing, a field too many, the fields in the wrong order, or a field of the wrong
      type — and no name is written anywhere: the tag is the constructor's position and
      a field is its own position. -/
  | ctor : ∀ {Γ τ}, (i : Nat) → (fields : FieldLayout) →
      (h : τ.ctorFields? i = some fields) → Spine Sg Γ fields → Term Sg Γ τ
  /-- A field of a tagged value: `e._2`.  `h` is the evidence that constructor `i` of
      `σ` has a field `j`, *of type `τ`* — so the type of a projection is the type the
      layout gives that field, and a field the type does not have cannot be read. -/
  | proj : ∀ {Γ σ τ}, Term Sg Γ σ → (i j : Nat) →
      (h : σ.fieldTy? i j = some τ) → Term Sg Γ τ
  /-- The runtime tag of a value whose type has a layout: `e.tag`, a number.  It is how
      a dispatch tests which constructor it has. -/
  | tagOf : ∀ {Γ σ}, Term Sg Γ σ → (h : σ.isTagged = true) → Term Sg Γ (.prim .nat)
  /-- A dispatch on the tag of a value.  Every branch answers with the same type; the
      fields of the scrutinee are reached with `Term.proj`, so a branch binds nothing.
      `h` says that every tag branched on is a constructor of `σ` and that none is
      repeated, and `Alts` always ends in a default branch, so a case can neither test
      an impossible tag nor fall off the end. -/
  | caseTag : ∀ {Γ σ τ tags}, Term Sg Γ σ → Alts Sg Γ τ tags →
      (h : σ.caseOk tags = true) → Term Sg Γ τ
  /-- The only repetition in the language: start the loop variables at `init` and run
      `body` until it answers.  Inside `body`, de Bruijn index `i` counts from the *last*
      loop variable, i.e. the context is `σs.reverse ++ Γ`. -/
  | loop : ∀ {Γ σs τ},
      (init : Spine Sg Γ σs) → (body : Body Sg (σs.reverse ++ Γ) σs τ) → Term Sg Γ τ

/-- A list of terms, typed by the list of their types: the arguments of a call, the
    results of a `Term.lamProd`, the initial values of a loop. -/
inductive Spine (Sg : Sig) : Ctx → List Ty → Type
  | nil  : ∀ {Γ}, Spine Sg Γ []
  | cons : ∀ {Γ σ σs}, Term Sg Γ σ → Spine Sg Γ σs → Spine Sg Γ (σ :: σs)

/-- The branches of a `Term.caseTag`, keyed by constructor tag and indexed by the list
    of tags they test, in order.  A list always ends in `Alts.deflt`: a case has a
    default branch whatever else it has, so no dispatch can fall off the end of its
    branches.  (Where the branches are exhaustive the default is the last constructor's
    own branch.) -/
inductive Alts (Sg : Sig) : Ctx → Ty → List Nat → Type
  | deflt : ∀ {Γ τ}, Term Sg Γ τ → Alts Sg Γ τ []
  | cons  : ∀ {Γ τ tags}, (tag : Nat) → Term Sg Γ τ → Alts Sg Γ τ tags →
      Alts Sg Γ τ (tag :: tags)

/-- The body of a `Term.loop`: a block in context `Γ` whose loop variables have types
    `σs` and which answers with a `τ`. -/
inductive Body (Sg : Sig) : Ctx → List Ty → Ty → Type
  /-- Leave the loop with this value. -/
  | ret  : ∀ {Γ σs τ}, Term Sg Γ τ → Body Sg Γ σs τ
  /-- Go round again with these values for the loop variables — a tail call. -/
  | cont : ∀ {Γ σs τ}, Spine Sg Γ σs → Body Sg Γ σs τ
  /-- `let x = e;` in front of the rest of the block. -/
  | letB : ∀ {Γ σ σs τ}, Term Sg Γ σ → Body Sg (σ :: Γ) σs τ → Body Sg Γ σs τ
  /-- `if (c) { … } else { … }`, both arms being blocks. -/
  | iteB : ∀ {Γ σs τ},
      Term Sg Γ (.prim .bool) → Body Sg Γ σs τ → Body Sg Γ σs τ → Body Sg Γ σs τ

end

/-- The one-parameter lambda: `Ty.arrow σ τ` is `Ty.fn [σ] τ`, so this is `Term.lamN`
    with a single parameter. -/
def Term.lam {Sg : Sig} {Γ : Ctx} {τ1 τ2 : Ty} (b : Term Sg (τ1 :: Γ) τ2) :
    Term Sg Γ (τ1 ⇒ τ2) :=
  .lamN (params := [τ1]) b

/-- The one-argument application, the counterpart of `Term.lam`. -/
def Term.ap {Sg : Sig} {Γ : Ctx} {τ1 τ2 : Ty}
    (f : Term Sg Γ (τ1 ⇒ τ2)) (a : Term Sg Γ τ1) : Term Sg Γ τ2 :=
  .apN f (.cons a .nil)

-- Notation
prefix:100 "ƛ " => Term.lam
infixl:70 " ⬝ " => Term.ap

macro "♯" n:term:90 : term => `(Term.var (v♯ $n))

namespace Term

-- Shortcut for Church Numeral Type: (α ⇒ α) ⇒ α ⇒ α
abbrev NatTy (α : Ty) : Ty := (α ⇒ α) ⇒ α ⇒ α

-- 1. Identity Function: ƛx. x
-- Type: τ ⇒ τ  (in empty context [])
def id {Sg : Sig} {τ : Ty} : Term Sg [] (τ ⇒ τ) :=
  ƛ ♯0

-- 2. Constant Function: ƛx. ƛy. x
-- Type: τ1 ⇒ τ2 ⇒ τ1  (in empty context [])
def const {Sg : Sig} {τ1 τ2 : Ty} : Term Sg [] (τ1 ⇒ τ2 ⇒ τ1) :=
  ƛ (ƛ ♯1)

-- 3. Church Numerals
-- Zero: ƛf. ƛx. x
def zero {Sg : Sig} {α : Ty} : Term Sg [] (NatTy α) :=
  ƛ (ƛ ♯0)

-- One: ƛf. ƛx. f x
def one {Sg : Sig} {α : Ty} : Term Sg [] (NatTy α) :=
  ƛ (ƛ (♯1 ⬝ ♯0))

-- Two: ƛf. ƛx. f (f x)
def two {Sg : Sig} {α : Ty} : Term Sg [] (NatTy α) :=
  ƛ (ƛ (♯1 ⬝ (♯1 ⬝ ♯0)))

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
def succ {Sg : Sig} {α : Ty} : Term Sg [] (NatTy α ⇒ NatTy α) :=
  ƛ (             -- n is ♯2 (NatTy α)
    ƛ (           -- f is ♯1 (α ⇒ α)
      ƛ (         -- x is ♯0 (α)
        ♯1 ⬝ ((♯2 ⬝ ♯1) ⬝ ♯0)
      )
    )
  )

-- 5. Terms with Free Variables

-- A term with 2 free variables: (♯1 ⬝ ♯0)
-- Context has 2 types: Γ = [α, α ⇒ β]
--   - ♯0 has type α       (free var 0)
--   - ♯1 has type α ⇒ β   (free var 1)
def freeTerm {Sg : Sig} {α β : Ty} : Term Sg [α, α ⇒ β] β :=
  ♯1 ⬝ ♯0

-- A term with 1 free variable: ƛy. (y ⬝ ♯1)
-- Top context has 1 type: Γ = [α] (free var x0)
-- Inside ƛ, context becomes: (α ⇒ β) :: [α]
--   - ♯0 is bound variable y of type α ⇒ β
--   - ♯1 is free variable x0 of type α
def boundAndFree {Sg : Sig} {α β : Ty} : Term Sg [α] ((α ⇒ β) ⇒ β) :=
  ƛ (♯0 ⬝ ♯1)

/-! ## A loop, for comparison with the recursion it replaces

`SnapshotsPBOPure/Tco01.lean` is `def test (n : Nat) : Nat := match n with | 0 => n
| n + 1 => test n`.  Lean proves it terminating, so the backend accepts it, and what it
becomes here is the loop below: one loop variable, one exit, one tail call. -/

/-- The user's example of a function answering with a tuple:
    `def foo : Int × Float → Int × Float → Int × Float` prints as
    `(v0, v1) => (v2, v3) => { return [1, 1.0]; }`. -/
def fooReturnsProd {Sg : Sig} :
    Term Sg [] (.fn [Ty.int, Ty.float] (.fn_returnsProd [Ty.int, Ty.float] Ty.int [Ty.float])) :=
  .lamN (params := [Ty.int, Ty.float])
    (.lamProd (params := [Ty.int, Ty.float])
      (.cons (.lit (.int 1)) (.cons (.lit (.float "1.0")) .nil)))

/-- `test` of `Tco01`, by hand: `loop n { if (n === 0) return n; continue with n - 1 }`. -/
def tco01 {Sg : Sig} : Term Sg [] (.fn [.nat] .nat) :=
  .lamN (params := [Ty.nat])
    (.loop (σs := [Ty.nat]) (.cons (♯0) .nil)
      (.iteB (.prim (.beq Ty.nat) (.cons (♯0) (.cons (.lit (.nat 0)) .nil)))
        (.ret (♯0))
        (.cont (.cons (.prim .natSub (.cons (♯0) (.cons (.lit (.nat 1)) .nil))) .nil))))

end Term

/-- The number of arguments in a spine. -/
def Spine.length {Sg : Sig} {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs) : Nat :=
  match s with
  | .nil => 0
  | .cons _ rest => rest.length + 1

/-- The number of branches of a case, the default branch included. -/
def Alts.length {Sg : Sig} {Γ : Ctx} {τ : Ty} {tags : List Nat} (a : Alts Sg Γ τ tags) :
    Nat :=
  match a with
  | .deflt _ => 1
  | .cons _ _ rest => rest.length + 1
