module
public import LakeJs.Ty
public import LakeJs.Layout
public import LakeJs.Externs
public import LakeJs.LeanPrimTyLit
@[expose] public section

/-!
# `Term`: the well-scoped, simply-typed core the front end compiles to

`Term Sg Γ τ` is the intermediate language the Lean front end produces.  It is a
**Lean** language — the first step of the compilation, before anything about a target is
decided — and it is:

* *intrinsically scoped*: a variable is a de Bruijn index into `Γ`, so a free variable is
  unrepresentable;
* *intrinsically typed*: its function space is the **curried** simply-typed one of
  `LakeJs.Ty`, so `σ ⇒ τ` takes one argument and answers with one value;
* *intrinsically linked*: a reference to a top-level declaration is an index into the
  module signature `Sg`, whose names are unique by construction, so a call to a name the
  module does not declare is unrepresentable;
* *intrinsically separated*: a **label** lives in a grammar of its own, `Tail`, in a
  context of its own, `Ω`, so the only thing that can be done with one is to jump to it
  — a label cannot be mistaken for a value, and a value cannot be jumped to.

## Blocks and labels: one mechanism, not two

A loop and a join point used to be two constructs of `Term`: `Term.loop`, with a `Body`
that either answered or went round again, and `Term.joinPoint`, a block the rest of the
term could jump to but not jump *back* into.  They are now **one**: a `Tail.label`.

* A `Term` has no jumps at all — there is no label context on `Term`, so a label cannot
  leak into a closure, into an argument, or into what a `let` binds.
* The one way a term uses labels is `Term.block`, which opens a **tail grammar**, `Tail`,
  in the *empty* label context.  Every position of a `Tail` is a tail position of the
  block, which is why a `Tail.jmp` is allowed there and nowhere else: a jump is the last
  thing the block does, and it never comes back.  The old `LakeJs.TailPos` check — "is
  every jump in tail position?" — is therefore not a check any more, it is the grammar.
* `Tail.label self body rest` binds one label, taking the arguments `ps`.  With
  `self = false` it is a **shared tail**: `body` cannot jump to it, so control passes
  through it once per jump — `l: { … }` with `break l` in the target.  With `self = true`
  it is a **loop**: `body` may jump to the label it is the body of — `l: while (true) { …
  }` with `continue l`.  The old `Term.loop init body` is
  `Tail.label true body (Tail.jmp .head init)`, and the old `Term.joinPoint body rest` is
  `Tail.label false body rest`.
* A label has **no result type**.  It answers with the type the whole block answers with,
  because a jump never returns to its jump site.  A block of a *different* type is a
  value, and a value is bound by a `Term.letE` of a `Term.block` — which is what a
  value-producing join point always meant.
* A jump to a non-innermost label is an index other than zero in `Ω`, so `break outer`
  and `continue outer` need no third context.

Four consequences matter, and they are the reason the language looks the way it does.

* **An Omega-style self-application is not a `Term`.**  `Term.ap` asks for a function of
  type `σ ⇒ τ` and an argument of type `σ`, so `x x` would need `σ = σ ⇒ τ`, which no
  finite type satisfies.  There is no fixed-point combinator and no recursive `Term`
  constructor either.
* **Recursion is a self-label.**  The only way a term repeats work is a `Tail.label`
  whose `self` flag is `true`, jumped to from its own body.
* **Every name a term mentions is declared.**  `Term.global` takes a `GlobalRef`, an
  index into the signature of the module being compiled, and the type it is used at is
  the type the signature gives it.
* **Every operation is applied at its own type.**  `Extern` (the catalogue of the
  functions Lean implements with `@[extern]`, in `LakeJs.Externs`) is *indexed* by the
  list of its argument types and by its result type, so `Term.extern` cannot be applied
  to arguments of the wrong types.

There is **no function that answers with nothing**: the language is pure, the only
reason to call such a function would be an effect, and a unit-like type is erased before
a `Ty` is built.  There is likewise no function of *no* arguments: a delayed value is
`Ty.lazy`, built by `Term.lazyMk` and run by `Term.lazyForce`.

## What the language deliberately does *not* claim

* **`Ty.lazy` is a delay, not a `Thunk`.**  `Term.lazyForce (Term.lazyMk e)` runs `e`,
  and running it twice runs `e` twice: there is no memoisation, exactly as there is none
  in the `() => …` of the target.  A Lean `Thunk`, which does memoise, is therefore
  **not** representable as a `Ty.lazy`, and the front end may not translate one into one;
  a memoising delay would be a second type former with a store in the evaluator.
* **Non-recursiveness is a property of one `Term`, not of a program.**  `Sig` gives the
  top-level declarations *types*, not bodies, so nothing here prevents two globals from
  calling each other; that invariant belongs to the program level (`LakeJs.Totality` on
  the LCNF side, `LakeJs.Program` when it returns).
* **`GlobalDecl.name` is an unvalidated `String`.**  A signature cannot declare a name
  twice (`Sig.h_names_unique`), but nothing says a name is a legal identifier of the
  target or avoids its reserved words.  If the emitter mangles names, the uniqueness
  proof has to be re-established for the mangled ones.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)

/-! ## Variables -/

/-- The types of the values in scope, innermost first. -/
abbrev Ctx := List Ty

/-- A variable: a de Bruijn index into the context, carrying the type it is bound at. -/
inductive Var : Ctx → Ty → Type
  | head : ∀ {Γ τ}, Var (τ :: Γ) τ
  | tail : ∀ {Γ τ1 τ2}, Var Γ τ1 → Var (τ2 :: Γ) τ1

/-- Membership notation: `Γ ∋ τ`. -/
infix:40 " ∋ " => Var

/-- Expand a natural number literal into nested `Var.tail` / `Var.head`. -/
syntax "var_get_elem" (ppSpace term) : term
macro_rules | `(term| var_get_elem $n) => match n.1.toNat with
| 0     => `(term| Var.head)
| n + 1 => `(term| Var.tail (var_get_elem $(Lean.quote n)))

/-- Sugar: `v♯0` is `Var.head`, `v♯1` is `Var.tail Var.head`, … -/
macro "v♯" n:term:90 : term => `(var_get_elem $n)

/-- The de Bruijn index of a variable: how many binders out it is. -/
def Var.index : ∀ {Γ : Ctx} {τ : Ty}, Γ ∋ τ → Nat
  | _, _, .head => 0
  | _, _, .tail v => Var.index v + 1

/-! ## Labels have a context of their own

A label is not a value: it cannot be passed, stored or returned, and the only thing that
may be done with one is to jump to it.  That is not a discipline checked after the fact
— it is the shape of the language.  A label is bound in `Ω`, a context whose entries are
the *argument types* a jump to it supplies, and the only constructor that reads `Ω` is
`Tail.jmp`.  A `Term` has no `Ω` at all, so a value can never name a label.

A label has **no result type**: jumping to it does not come back, so the block it is part
of answers with the type the enclosing `Term.block` answers with.
-/

/-- The labels in scope, innermost first; an entry is what a jump to that label
    supplies. -/
abbrev LCtx := List (List Ty)

/-- A label in scope: a de Bruijn index into `Ω`, separate from the index of a
    variable. -/
inductive LVar : LCtx → List Ty → Type
  | head : ∀ {Ω ps}, LVar (ps :: Ω) ps
  | tail : ∀ {Ω ps qs}, LVar Ω ps → LVar (qs :: Ω) ps

/-- Membership notation for labels: `Ω ∋ₗ ps`. -/
infix:40 " ∋ₗ " => LVar

/-- The de Bruijn index of a label. -/
def LVar.index : ∀ {Ω : LCtx} {ps : List Ty}, Ω ∋ₗ ps → Nat
  | _, _, .head => 0
  | _, _, .tail v => LVar.index v + 1

/-- The label context the **body** of a label is written in: the label itself is in scope
    there exactly when it is a loop (`self = true`), and then a jump to it is a
    `continue`. -/
abbrev LCtx.ext (self : Bool) (ps : List Ty) (Ω : LCtx) : LCtx :=
  cond self (ps :: Ω) Ω

/-! ## The signature of a module

A `Term` is written against a fixed list of top-level declarations — the ones the
compiled module binds, plus the ones it imports from the runtime.  A reference to one of
them is a `GlobalRef`, an index into that list, so the *name* and the *type* of a global
are read off the signature rather than written at the use site.
-/

/-- One top-level declaration a term may refer to: the name it is bound to, and its
    type.

    There is deliberately **no** `isInlined` field: whether a declaration is inlined is a
    property of the *translation* into this language, not of the language, and an
    inlined declaration simply does not reach a signature.  See
    `HOW_TO_SUPPORT_INLINABLE_FUNCTIONS.md`. -/
structure GlobalDecl where
  /-- The identifier the declaration is bound to. -/
  name : String
  /-- Its type. -/
  ty : Ty
  deriving DecidableEq

/-- Are all of these names different? -/
def declNamesUnique : List GlobalDecl → Bool
  | [] => true
  | d :: ds => !ds.any (fun e => e.name == d.name) && declNamesUnique ds

/-- The signature of the module being compiled: every top-level name a `Term` of it may
    mention, **each of them declared once**.  The proof is a field, so a signature that
    declares a name twice cannot be built; `by decide` discharges it for a signature
    written out. -/
structure Sig where
  /-- The declarations, in order. -/
  decls : List GlobalDecl
  /-- No name is declared twice. -/
  h_names_unique : declNamesUnique decls = true := by decide

/-- The names a signature declares. -/
def Sig.names (Sg : Sig) : List String := Sg.decls.map GlobalDecl.name

/-- A reference to a declaration of the signature — a de Bruijn index into it, whose
    type is the one the signature gives it.  There is no other way to name a global, so
    a `Term` cannot call a name that is not declared, nor call a declared one at a type
    it does not have. -/
inductive GlobalRef : List GlobalDecl → Ty → Type
  | here  : ∀ {g : GlobalDecl} {ds : List GlobalDecl}, GlobalRef (g :: ds) g.ty
  | there : ∀ {g : GlobalDecl} {ds : List GlobalDecl} {τ : Ty},
      GlobalRef ds τ → GlobalRef (g :: ds) τ

/-- The name a reference resolves to. -/
def GlobalRef.name : ∀ {ds : List GlobalDecl} {τ : Ty}, GlobalRef ds τ → String
  | _, _, .here (g := g) => g.name
  | _, _, .there r => r.name

/-- The name of a reference is one of the names the signature declares. -/
theorem GlobalRef.name_mem :
    ∀ {ds : List GlobalDecl} {τ : Ty} (r : GlobalRef ds τ),
      r.name ∈ ds.map GlobalDecl.name
  | _ :: _, _, .here => by simp [GlobalRef.name]
  | _ :: _, _, .there r => by
      have := GlobalRef.name_mem r
      simp [GlobalRef.name] at this ⊢
      exact Or.inr this

/-- **In a signature the name of a reference determines its type**: two references with
    the same name are references at the same type.  This is what the uniqueness field of
    `Sig` is for. -/
theorem GlobalRef.ty_unique_of_namesUnique :
    ∀ {ds : List GlobalDecl}, declNamesUnique ds = true → ∀ {σ τ : Ty}
      (r : GlobalRef ds σ) (s : GlobalRef ds τ), r.name = s.name → σ = τ
  | _ :: _, _, _, _, .here, .here, _ => rfl
  | _ :: _, h, _, _, .here, .there s, hname => by
      exfalso
      simp [declNamesUnique] at h
      have hmem := GlobalRef.name_mem s
      simp [List.mem_map] at hmem
      obtain ⟨d, hd, hdn⟩ := hmem
      simp [GlobalRef.name] at hname
      exact h.1 d hd (hdn.trans hname.symm)
  | _ :: _, h, _, _, .there r, .here, hname => by
      exfalso
      simp [declNamesUnique] at h
      have hmem := GlobalRef.name_mem r
      simp [List.mem_map] at hmem
      obtain ⟨d, hd, hdn⟩ := hmem
      simp [GlobalRef.name] at hname
      exact h.1 d hd (hdn.trans hname)
  | _ :: ds, h, _, _, .there r, .there s, hname => by
      have h' : declNamesUnique ds = true := by
        simp [declNamesUnique] at h; exact h.2
      exact GlobalRef.ty_unique_of_namesUnique h' r s
        (by simpa [GlobalRef.name] using hname)

/-- Look a name up in a signature, whatever type it was declared at.  Looking one up
    *at* a given type is this together with `decide (σ = τ)`. -/
def GlobalRef.findAny? :
    (ds : List GlobalDecl) → (name : String) → Option (Σ τ : Ty, GlobalRef ds τ)
  | [], _ => none
  | g :: ds, nm =>
    if g.name == nm then some ⟨g.ty, GlobalRef.here⟩
    else (GlobalRef.findAny? ds nm).map fun r => ⟨r.1, .there r.2⟩

/-! ## Terms -/

mutual

/-- A well-scoped, simply-typed term of the module whose signature is `Sg`, in the
    variable context `Γ`.  A term has **no** label context: a jump is a `Tail`, never a
    `Term`, so no value position of the language can hold one. -/
inductive Term (Sg : Sig) : Ctx → Ty → Type
  /-- A variable of `Γ`. -/
  | var : ∀ {Γ τ}, Γ ∋ τ → Term Sg Γ τ
  /-- `fun x => body`: **one** parameter, since every function is curried. -/
  | lam : ∀ {Γ σ τ}, Term Sg (σ :: Γ) τ → Term Sg Γ (σ ⇒ τ)
  /-- `f a`: **one** argument. -/
  | ap  : ∀ {Γ σ τ}, Term Sg Γ (σ ⇒ τ) → Term Sg Γ σ → Term Sg Γ τ
  /-- A constant of a terminal type. -/
  | lit : ∀ {Γ} {p : LeanPrimTy}, LeanPrimLit p → Term Sg Γ (.prim p)
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ τ}, GlobalRef Sg.decls τ → Term Sg Γ τ
  /-- A function Lean implements with `@[extern]`, named by the catalogue
      `LakeJs.Externs`, at the curried type its argument list gives it. -/
  | extern : ∀ {Γ σs τ}, Externs σs τ → Term Sg Γ (Ty.arrows σs τ)
  /-- Delay a value.  This is what a Lean `fun (_ : Unit) => e` becomes: the parameter is
      the one value of a unit type, which carries nothing at run time and is erased, so
      what is left is a delayed value — and `Ty.lazy` is exactly that.

      **Unmemoised**: `Ty.lazy` is a delay, not a Lean `Thunk` (forcing it twice runs it
      twice — see the header). -/
  | lazyMk : ∀ {Γ τ}, Term Sg Γ τ → Term Sg Γ (.lazy τ)
  /-- Run a delayed value: what an application `f ()` becomes once the unit argument is
      erased. -/
  | lazyForce : ∀ {Γ τ}, Term Sg Γ (.lazy τ) → Term Sg Γ τ
  /-- `let x = e; body` — `x` is de Bruijn index 0 of `body`. -/
  | letE : ∀ {Γ σ τ}, Term Sg Γ σ → Term Sg (σ :: Γ) τ → Term Sg Γ τ
  /-- `if c then t else e`. -/
  | ite : ∀ {Γ τ}, Term Sg Γ (.prim .bool) → Term Sg Γ τ → Term Sg Γ τ → Term Sg Γ τ
  /-- A tagged value, built **at a type whose layout says so**.  `h` is the evidence that
      `τ` has a constructor number `i`, and which fields it has; the arguments are then a
      spine of exactly those types.  So a constructor cannot be built at a type that has
      no such constructor, with a field missing, a field too many, the fields in the
      wrong order, or a field of the wrong type. -/
  | ctor : ∀ {Γ τ}, (i : Nat) → (fields : FieldLayout) →
      (h : τ.ctorFields? i = some fields) → Spine Sg Γ fields → Term Sg Γ τ
  /-- A field of a tagged value.  `h` is the evidence that constructor `i` of `σ` has a
      field `j`, *of type `τ`*, so a field the type does not have cannot be read.

      `hOne` is what makes the read **sound**: `σ` has exactly one constructor, so the
      constructor the value was built with is the one this projection speaks about.
      Without it, `(none).1` at `Option Nat` would be a closed, well-typed term that the
      evaluator cannot run — reading a field the value does not carry.  A field of a
      type with several constructors is reached through a `Term.caseTag` on the tag
      instead.  See `PROJ_SOUNDNESS.md` (option C). -/
  | proj : ∀ {Γ σ τ}, Term Sg Γ σ → (i j : Nat) →
      (hOne : σ.numCtors? = some 1) →
      (h : σ.fieldTy? i j = some τ) → Term Sg Γ τ
  /-- The runtime tag of a value whose type has a layout: how a dispatch tests which
      constructor it has. -/
  | tagOf : ∀ {Γ σ}, Term Sg Γ σ → (h : σ.isTagged = true) → Term Sg Γ (.prim .nat)
  /-- A dispatch on the tag of a value.  Every branch answers with the same type; the
      fields of the scrutinee are reached with `Term.proj`, so a branch binds nothing.
      `h` says that every tag branched on is a constructor of `σ` and that none is
      repeated, so a case cannot test an impossible tag; and a case cannot fall off the
      end of its branches either, because `Alts` ends *either* in a default branch
      (`full = false`) *or* in nothing at all with a branch for every constructor
      (`full = true`, `Ty.caseOkFull`). -/
  | caseTag : ∀ {Γ σ τ tags full}, Term Sg Γ σ → Alts Sg Γ τ tags full →
      (h : σ.caseOkAlts full tags = true) → Term Sg Γ τ
  /-- **A block**: the one way a term uses labels.  Its tail is written in the *empty*
      label context, so a block is closed for jumps — a `break` or a `continue` of the
      target never crosses the boundary of the function it is in, and here it never
      crosses the boundary of the block either. -/
  | block : ∀ {Γ τ}, Tail Sg Γ [] τ → Term Sg Γ τ

/-- A list of terms, typed by the list of their types: the arguments of a primitive
    operation, the arguments of a jump, the fields of a constructor. -/
inductive Spine (Sg : Sig) : Ctx → List Ty → Type
  | nil  : ∀ {Γ}, Spine Sg Γ []
  | cons : ∀ {Γ σ σs}, Term Sg Γ σ → Spine Sg Γ σs → Spine Sg Γ (σ :: σs)

/-- The branches of a `Term.caseTag`, keyed by constructor tag and indexed by the list of
    tags they test, in order, and by whether the list is **exhaustive**.  A list ends
    either in `Alts.deflt`, a default branch, or — when `full = true` — in
    `Alts.nilFull`, which is only usable at a `Ty.caseOkFull`, i.e. when every
    constructor has a branch of its own.  Either way no dispatch can fall off the end of
    its branches. -/
inductive Alts (Sg : Sig) : Ctx → Ty → List Nat → Bool → Type
  /-- The default branch a dispatch ends with. -/
  | deflt : ∀ {Γ τ}, Term Sg Γ τ → Alts Sg Γ τ [] false
  /-- The end of an **exhaustive** dispatch: no default branch, because every
      constructor has a branch of its own (`Ty.caseOkFull`). -/
  | nilFull : ∀ {Γ τ}, Alts Sg Γ τ [] true
  | cons  : ∀ {Γ τ tags full}, (tag : Nat) → Term Sg Γ τ → Alts Sg Γ τ tags full →
      Alts Sg Γ τ (tag :: tags) full

/-- A **tail**: a basic block of the block grammar, in the variable context `Γ` and the
    label context `Ω`, answering with `τ`.  Every position of a `Tail` is a tail position
    of the enclosing `Term.block`, which is why a jump is allowed here and nowhere
    else. -/
inductive Tail (Sg : Sig) : Ctx → LCtx → Ty → Type
  /-- Answer with this value: the block is done. -/
  | ret : ∀ {Γ Ω τ}, Term Sg Γ τ → Tail Sg Γ Ω τ
  /-- Jump to a label in scope, with one argument per parameter.  A jump never comes
      back, so it stands at **any** answer type: it is the whole of the rest of this
      block. -/
  | jmp : ∀ {Γ Ω ps τ}, Ω ∋ₗ ps → Spine Sg Γ ps → Tail Sg Γ Ω τ
  /-- `let x = e;` in front of the rest of the block. -/
  | letT : ∀ {Γ Ω σ τ}, Term Sg Γ σ → Tail Sg (σ :: Γ) Ω τ → Tail Sg Γ Ω τ
  /-- A two-way branch, both arms being blocks. -/
  | iteT : ∀ {Γ Ω τ},
      Term Sg Γ (.prim .bool) → Tail Sg Γ Ω τ → Tail Sg Γ Ω τ → Tail Sg Γ Ω τ
  /-- A dispatch on the tag of a value, every arm being a block. -/
  | caseT : ∀ {Γ Ω σ τ tags full}, Term Sg Γ σ → AltsT Sg Γ Ω τ tags full →
      (h : σ.caseOkAlts full tags = true) → Tail Sg Γ Ω τ
  /-- **One label**, taking the arguments `ps`, in scope in `rest` as label index `0`.

      `self = false` is a *shared tail*: `body` does not have the label in scope, so
      control passes through it once per jump — `l: { … }` with `break l`.
      `self = true` is a *loop*: `body` may jump to the label it is the body of —
      `l: while (true) { … }` with `continue l`, and this is the one construct of the
      language that repeats work.

      Inside `body`, de Bruijn index `0` is the **first** argument of the label, i.e. the
      variable context is `ps ++ Γ`. -/
  | label : ∀ {Γ Ω ps τ}, (self : Bool) →
      (body : Tail Sg (ps ++ Γ) (LCtx.ext self ps Ω) τ) →
      (rest : Tail Sg Γ (ps :: Ω) τ) → Tail Sg Γ Ω τ

/-- The branches of a `Tail.caseT`: `Alts`, with a block in place of each term, so that a
    branch may answer *or* jump. -/
inductive AltsT (Sg : Sig) : Ctx → LCtx → Ty → List Nat → Bool → Type
  /-- The default branch a dispatch ends with. -/
  | deflt : ∀ {Γ Ω τ}, Tail Sg Γ Ω τ → AltsT Sg Γ Ω τ [] false
  /-- The end of an **exhaustive** dispatch: no default branch. -/
  | nilFull : ∀ {Γ Ω τ}, AltsT Sg Γ Ω τ [] true
  | cons : ∀ {Γ Ω τ tags full}, (tag : Nat) → Tail Sg Γ Ω τ →
      AltsT Sg Γ Ω τ tags full → AltsT Sg Γ Ω τ (tag :: tags) full

end

/-- A **shared tail**: a label whose body cannot jump to it — `l: { … }` with `break l`
    in the target, and what a join point of the old grammar was. -/
abbrev Tail.joinLabel {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (body : Tail Sg (ps ++ Γ) Ω τ) (rest : Tail Sg Γ (ps :: Ω) τ) : Tail Sg Γ Ω τ :=
  .label false body rest

/-- A **loop**: a label whose body may jump to it — `l: while (true) { … }` with
    `continue l` in the target. -/
abbrev Tail.loopLabel {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (body : Tail Sg (ps ++ Γ) (ps :: Ω) τ) (rest : Tail Sg Γ (ps :: Ω) τ) :
    Tail Sg Γ Ω τ :=
  .label true body rest

/-- Apply a curried term to a spine, one argument at a time: `f a₁ … aₙ`. -/
def Term.appSpine {Sg : Sig} {Γ : Ctx} :
    ∀ {σs : List Ty} {τ : Ty},
      Term Sg Γ (Ty.arrows σs τ) → Spine Sg Γ σs → Term Sg Γ τ
  | [], _, f, .nil => f
  | _ :: _, _, f, .cons a rest => Term.appSpine (.ap f a) rest

/-- A Lean function the runtime implements, applied to exactly the arguments it takes:
    iterated `Term.ap` of `Term.extern`. -/
def Term.callExtern {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}
    (e : Externs σs τ) (args : Spine Sg Γ σs) : Term Sg Γ τ :=
  Term.appSpine (.extern e) args

-- Notation
prefix:100 "ƛ " => Term.lam
infixl:70 " ⬝ " => Term.ap

/-- Sugar: `♯0` is the innermost variable, `♯1` the one before it, … -/
macro "♯" n:term:90 : term => `(Term.var (v♯ $n))

namespace Term

/-- The Church numeral type over `α`: `(α ⇒ α) ⇒ α ⇒ α`. -/
abbrev NatTy (α : Ty) : Ty := (α ⇒ α) ⇒ α ⇒ α

/-- The identity function, `fun x => x`. -/
def idTerm {Sg : Sig} {τ : Ty} : Term Sg [] (τ ⇒ τ) :=
  ƛ ♯0

/-- The constant function, `fun x y => x`. -/
def const {Sg : Sig} {τ1 τ2 : Ty} : Term Sg [] (τ1 ⇒ τ2 ⇒ τ1) :=
  ƛ (ƛ ♯1)

/-- The Church numeral zero, `fun f x => x`. -/
def zero {Sg : Sig} {α : Ty} : Term Sg [] (NatTy α) :=
  ƛ (ƛ ♯0)

/-- The Church numeral one, `fun f x => f x`. -/
def one {Sg : Sig} {α : Ty} : Term Sg [] (NatTy α) :=
  ƛ (ƛ (♯1 ⬝ ♯0))

/-- The Church numeral two, `fun f x => f (f x)`. -/
def two {Sg : Sig} {α : Ty} : Term Sg [] (NatTy α) :=
  ƛ (ƛ (♯1 ⬝ (♯1 ⬝ ♯0)))

/-- The Church successor, `fun n f x => f (n f x)`. -/
def succ {Sg : Sig} {α : Ty} : Term Sg [] (NatTy α ⇒ NatTy α) :=
  ƛ (ƛ (ƛ (♯1 ⬝ ((♯2 ⬝ ♯1) ⬝ ♯0))))

/-- A term with two free variables, in the context `[α, α ⇒ β]`. -/
def freeTerm {Sg : Sig} {α β : Ty} : Term Sg [α, α ⇒ β] β :=
  ♯1 ⬝ ♯0

/-- A term with one free variable: `fun y => y x₀`, in the context `[α]`. -/
def boundAndFree {Sg : Sig} {α β : Ty} : Term Sg [α] ((α ⇒ β) ⇒ β) :=
  ƛ (♯0 ⬝ ♯1)

/-! ## A loop, for comparison with the recursion it replaces

`SnapshotsPBOPure/Tco01.lean` is `def test (n : Nat) : Nat := match n with | 0 => n
| n + 1 => test n`.  Lean proves it terminating, so the front end accepts it, and what it
becomes here is the block below: one label, taken with `self = true`, one argument, one
exit and one jump back. -/

/-- `test` of `Tco01`, by hand: a block whose one label is a loop. -/
def tco01 {Sg : Sig} : Term Sg [] (.nat ⇒ .nat) :=
  ƛ (.block
      (.label (ps := [Ty.nat]) true
        (.iteT (callExtern (.prim2 .lean_nat_dec_eq)
            (.cons (♯0) (.cons (.lit (.nat 0)) .nil)))
          (.ret (♯0))
          (.jmp .head (.cons (callExtern (.prim2 .lean_nat_sub)
            (.cons (♯0) (.cons (.lit (.nat 1)) .nil))) .nil)))
        (.jmp .head (.cons (♯0) .nil))))

/-- The same loop, written with a **dispatch** instead of a two-way branch: the branch
    for each constructor of the scrutinee is a block of its own (`Tail.caseT`), and the
    list of branches is **exhaustive** — there is no default branch, because every
    constructor has one (`AltsT.nilFull`, `Ty.caseOkFull`). -/
def tco01Case {Sg : Sig} : Term Sg [] (.nat ⇒ .nat) :=
  ƛ (.block
      (.label (ps := [Ty.nat]) true
        (.caseT
          (callExtern (.prim2 .lean_nat_dec_eq)
            (.cons (♯0) (.cons (.lit (.nat 0)) .nil)))
          (.cons 1 (.ret (♯0))
            (.cons 0
              (.jmp .head (.cons (callExtern (.prim2 .lean_nat_sub)
                (.cons (♯0) (.cons (.lit (.nat 1)) .nil))) .nil))
              .nilFull))
          (by decide))
        (.jmp .head (.cons (♯0) .nil))))

/-- An **exhaustive** dispatch of terms: `Bool` has two constructors and both have a
    branch, so the case needs no default branch at all. -/
def notTerm {Sg : Sig} : Term Sg [Ty.bool] Ty.bool :=
  .caseTag (♯0)
    (.cons 0 (.lit (.bool true)) (.cons 1 (.lit (.bool false)) .nilFull))
    (by decide)

/-- A shared tail, by hand: bind a label of one `Nat` argument and jump to it from both
    arms of a branch — the block a dispatch would otherwise duplicate.  This is what a
    join point of the old grammar was, and it is now a `Tail.label` with `self = false`
    inside a `Term.block`. -/
def sharedTail {Sg : Sig} : Term Sg [Ty.bool] Ty.nat :=
  .block
    (.label (ps := [Ty.nat]) false (.ret (♯0))
      (.iteT (♯0)
        (.jmp .head (.cons (.lit (.nat 1)) .nil))
        (.jmp .head (.cons (.lit (.nat 2)) .nil))))

/-- **A shared tail that continues an enclosing loop**, which the two-construct grammar
    could not express: the label bound inside the loop's body jumps back to the loop.
    Both are `Tail.label`, so a jump to either is the same thing. -/
def sharedTailInLoop {Sg : Sig} : Term Sg [Ty.nat] Ty.nat :=
  .block
    (.label (ps := [Ty.nat]) true
      (.label (ps := [Ty.nat]) false
        (.jmp .head (.cons (♯0) .nil))
        (.iteT (callExtern (.prim2 .lean_nat_dec_eq)
            (.cons (♯0) (.cons (.lit (.nat 0)) .nil)))
          (.ret (♯0))
          (.jmp .head (.cons (callExtern (.prim2 .lean_nat_sub)
            (.cons (♯0) (.cons (.lit (.nat 1)) .nil))) .nil))))
      (.jmp .head (.cons (♯0) .nil)))

end Term

/-- The number of arguments in a spine. -/
def Spine.length {Sg : Sig} {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs) : Nat :=
  match s with
  | .nil => 0
  | .cons _ rest => rest.length + 1

/-- The number of branches of a case, the default branch included. -/
def Alts.length {Sg : Sig} {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool}
    (a : Alts Sg Γ τ tags full) : Nat :=
  match a with
  | .deflt _ => 1
  | .nilFull => 0
  | .cons _ _ rest => rest.length + 1

/-- The number of branches of a dispatch inside a block. -/
def AltsT.length {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat} {full : Bool}
    (a : AltsT Sg Γ Ω τ tags full) : Nat :=
  match a with
  | .deflt _ => 1
  | .nilFull => 0
  | .cons _ _ rest => rest.length + 1

end LakeJs.Expr

end
