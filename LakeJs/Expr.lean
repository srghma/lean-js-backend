module
public import LakeJs.Ty
public import LakeJs.Layout
public import LakeJs.Externs
public import LakeJs.LeanPrimTyLit
public import LakeJs.Den
@[expose] public section

/-!
# `Term`: the one grammar, terminating by construction

`Term Sg Γ Ρ τ` is the intermediate language the Lean front end produces.  It is a
**Lean** language — the first step of the compilation, before anything about a target is
decided — and it is:

* *intrinsically scoped*: a variable is a de Bruijn index into `Γ`, so a free variable is
  unrepresentable;
* *intrinsically typed*: its function space is the **curried** simply-typed one of
  `LakeJs.Ty`, so `σ ⇒ τ` takes one argument and answers with one value.  In particular
  `x x` is not typeable, so there is no fixed-point combinator;
* *intrinsically linked*: a reference to a top-level declaration is an index into the
  module signature `Sg`, whose names are unique by construction, so a call to a name the
  module does not declare is unrepresentable;
* *intrinsically separated*: a **label** lives in a grammar of its own, `Tail`, in a
  context of its own, `Ω`, so the only thing that can be done with one is to jump to it
  — a label cannot be mistaken for a value, and a value cannot be jumped to;
* *intrinsically measured*: the one way to repeat work is `Term.fix`, which carries its
  own lexicographic termination measure, and the one way to call back into it is
  `Term.selfCall`, which has no syntax for saying anything about that measure.

## The recursion discipline, and why four of the six kinds are unrepresentable

Lean's reference manual lists six kinds of recursive definition.  This grammar admits the
first two and **cannot express** the other four:

| kind | in `Term` |
| :-- | :-- |
| structurally recursive | `Term.fix` with the measure read off the recursion subject (`Term.structSize`) |
| well-founded recursive | `Term.fix` with the measure the transcribed `termination_by` tuple |
| partial fixpoint | unrepresentable: there is no constructor for an unmeasured fixpoint |
| coinductive / inductive fixpoint | unrepresentable: `Ty` has no coinductive former and `Term` has no unmeasured fixpoint |
| `partial` | unrepresentable: same |
| `unsafe` | unrepresentable: same |

The seal is the shape of the two constructors.  `Term.fix ps k measure body stuck` carries
a **`k`-component lexicographic measure** — a spine of `k` terms of type `nat`, living in
`ps ++ Γ`, so it reads the arguments and the enclosing environment and nothing else.  It
is what Lean's `termination_by n m => (n, m)` says, transcribed.

The recursion is **guarded**: the evaluator recomputes the measure at each self call and
only recurses when the new value is lexicographically strictly smaller than the value the
current activation was entered with; when it is not, the call answers `stuck`.  So

* the recursion terminates *by construction* — `LakeJs.Lex.LexRun` is built from `Nat.rec`
  and the bound only descends, which is why the evaluator is a total Lean function and why
  the kernel computes it;
* and the front end is never asked for an iteration count.  Its whole termination job is
  to transcribe the measure Lean already proved decreasing.  A measure that is *wrong*
  cannot produce a wrong answer, only an **observable** `stuck` one.

Inside `body`, the recursion is in scope only as an entry of the recursion context `Ρ`,
whose `RSig` records the *argument types and the result type and nothing else*.  There is
no measure slot in it, so `Term.selfCall` has no syntax for supplying, naming, inspecting,
restoring or raising a bound: the value it is measured against is the one the evaluator
holds.  A divergent term is therefore not something the translation rejects — it is
something that cannot be written down.

Note also that the body's context is `ps ++ Γ`: the bound is invisible to the body.

A self call may stand in **any** position, not only a tail one: the recursion environment
of the evaluator holds a plain Lean function, so a recursion under a constructor or under
an extern call is as ordinary as a tail call.

## Blocks and labels: join points only

A `Term` has no jumps at all — there is no label context on `Term`, so a label cannot leak
into a closure, into an argument, or into what a `let` binds.  The one way a term uses
labels is `Term.block`, which opens the **tail grammar**, `Tail`, in the *empty* label
context.  Every position of a `Tail` is a tail position of the block, which is why a
`Tail.jmp` is allowed there and nowhere else.

`Tail.join ps body rest` binds one **join point**, taking the arguments `ps`.  Its body is
typed in the *outer* label context `Ω`, so it cannot jump back to itself: a block is a
finite nest of join points and repeats no work.  The old grammar's `Tail.label` with
`self = true` — the loop, and the only source of divergence there was — has no counterpart
here, and neither does the certificate machinery that had to bound it.

## What else the language deliberately does *not* have

* **No `IO`, and no effect at all.**  `Ty` has no effectful former, and `Externs` is the
  catalogue of the *pure* `@[extern]` functions, so an `IO`-returning declaration has no
  image in this language.
* **No failure.**  Every operation answers with a value: an exhausted recursion, an
  out-of-range index and a lookup a schema would have ruled out all answer with
  `Ty.dflt`.  That is what lets the evaluator be an ordinary total Lean function.
* **`Ty.lazy` is a delay, not a `Thunk`.**  `Term.lazyForce (Term.lazyMk e)` runs `e`, and
  running it twice runs `e` twice: there is no memoisation.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)

/-! ## Variables -/

/-- The types of the values in scope, innermost first. -/
abbrev Ctx := List Ty

/-- **A typed de Bruijn index, up to a projection**: constructive evidence that some
    entry of `xs` occurs in it *whose image under `f` is `b`*, together with *where*.

    Every scope of the language is an instance of this one family.  The three scopes
    whose index *is* the entry — variables, labels and recursions — take `f := id`, and
    are packaged as `DeBruijn`.  The signature of the module takes `f := GlobalDecl.ty`:
    its entries are declarations, but a reference to one is indexed by the declaration's
    **type**, and that projection is exactly what `f` supplies. -/
inductive DeBruijnProj {α β : Type} (f : α → β) : List α → β → Type
  /-- The entry just bound. -/
  | head : ∀ {x : α} {xs : List α}, DeBruijnProj f (x :: xs) (f x)
  /-- An entry bound further out. -/
  | tail : ∀ {x : α} {xs : List α} {b : β},
      DeBruijnProj f xs b → DeBruijnProj f (x :: xs) b

/-- How many binders out an index is. -/
def DeBruijnProj.index {α β : Type} {f : α → β} :
    ∀ {xs : List α} {b : β}, DeBruijnProj f xs b → Nat
  | _, _, .head => 0
  | _, _, .tail v => DeBruijnProj.index v + 1

/-- The entry of `xs` an index points at. -/
def DeBruijnProj.entry {α β : Type} {f : α → β} :
    ∀ {xs : List α} {b : β}, DeBruijnProj f xs b → α
  | x :: _, _, .head => x
  | _ :: _, _, .tail v => DeBruijnProj.entry v

/-- The entry an index points at is one of the entries. -/
theorem DeBruijnProj.entry_mem {α β : Type} {f : α → β} :
    ∀ {xs : List α} {b : β} (v : DeBruijnProj f xs b), v.entry ∈ xs
  | _ :: _, _, .head => by simp [DeBruijnProj.entry]
  | _ :: _, _, .tail v => by
      have := DeBruijnProj.entry_mem v
      simp [DeBruijnProj.entry]
      exact Or.inr this

/-- The index of an entry is an index at that entry's image. -/
theorem DeBruijnProj.f_entry {α β : Type} {f : α → β} :
    ∀ {xs : List α} {b : β} (v : DeBruijnProj f xs b), f v.entry = b
  | _ :: _, _, .head => rfl
  | _ :: _, _, .tail v => DeBruijnProj.f_entry v

/-- **A typed de Bruijn index**: constructive evidence that `x` occurs in `xs`, together
    with *where* — the special case of `DeBruijnProj` whose projection is the identity. -/
abbrev DeBruijn {α : Type} (xs : List α) (x : α) : Type := DeBruijnProj id xs x

/-- The entry just bound. -/
@[match_pattern] abbrev DeBruijn.head {α : Type} {x : α} {xs : List α} :
    DeBruijn (x :: xs) x := DeBruijnProj.head

/-- An entry bound further out. -/
@[match_pattern] abbrev DeBruijn.tail {α : Type} {x y : α} {xs : List α}
    (v : DeBruijn xs x) : DeBruijn (y :: xs) x := DeBruijnProj.tail v

/-- How many binders out an index is. -/
abbrev DeBruijn.index {α : Type} {xs : List α} {x : α} (v : DeBruijn xs x) : Nat :=
  DeBruijnProj.index v

/-- A variable: a de Bruijn index into the context, carrying the type it is bound at. -/
abbrev Var (Γ : Ctx) (τ : Ty) : Type := DeBruijn Γ τ

/-- The variable just bound. -/
abbrev Var.head {Γ : Ctx} {τ : Ty} : Var (τ :: Γ) τ := DeBruijn.head

/-- A variable bound further out. -/
abbrev Var.tail {Γ : Ctx} {τ1 τ2 : Ty} (v : Var Γ τ1) : Var (τ2 :: Γ) τ1 :=
  DeBruijn.tail v

/-- Membership notation: `Γ ∋ τ`. -/
infix:40 " ∋ " => Var

/-- Expand a natural number literal into nested `Var.tail` / `Var.head`. -/
syntax "var_get_elem" (ppSpace term) : term
macro_rules | `(term| var_get_elem $n) => match n.1.toNat with
| 0     => `(term| DeBruijn.head)
| n + 1 => `(term| DeBruijn.tail (var_get_elem $(Lean.quote n)))

/-- Sugar: `v♯0` is `Var.head`, `v♯1` is `Var.tail Var.head`, … -/
macro "v♯" n:term:90 : term => `(var_get_elem $n)

/-- The de Bruijn index of a variable: how many binders out it is. -/
abbrev Var.index {Γ : Ctx} {τ : Ty} (v : Var Γ τ) : Nat := DeBruijn.index v

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
    variable — the same family, at a different entry type. -/
abbrev LVar (Ω : LCtx) (ps : List Ty) : Type := DeBruijn Ω ps

/-- The innermost label. -/
abbrev LVar.head {Ω : LCtx} {ps : List Ty} : LVar (ps :: Ω) ps := DeBruijn.head

/-- A label bound further out. -/
abbrev LVar.tail {Ω : LCtx} {ps qs : List Ty} (v : LVar Ω ps) : LVar (qs :: Ω) ps :=
  DeBruijn.tail v

/-- Membership notation for labels: `Ω ∋ₗ ps`. -/
infix:40 " ∋ₗ " => LVar

/-- The de Bruijn index of a label. -/
abbrev LVar.index {Ω : LCtx} {ps : List Ty} (v : LVar Ω ps) : Nat := DeBruijn.index v

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
abbrev GlobalRef (ds : List GlobalDecl) (τ : Ty) : Type :=
  DeBruijnProj GlobalDecl.ty ds τ

/-- The declaration just bound. -/
@[match_pattern] abbrev GlobalRef.here {g : GlobalDecl} {ds : List GlobalDecl} :
    GlobalRef (g :: ds) g.ty := DeBruijnProj.head

/-- A declaration bound further out. -/
@[match_pattern] abbrev GlobalRef.there {g : GlobalDecl} {ds : List GlobalDecl} {τ : Ty}
    (r : GlobalRef ds τ) : GlobalRef (g :: ds) τ := DeBruijnProj.tail r

/-- The name a reference resolves to: the name of the declaration it points at. -/
def GlobalRef.name {ds : List GlobalDecl} {τ : Ty} (r : GlobalRef ds τ) : String :=
  r.entry.name

@[simp] theorem GlobalRef.name_here {g : GlobalDecl} {ds : List GlobalDecl} :
    (GlobalRef.here (g := g) (ds := ds)).name = g.name := rfl

@[simp] theorem GlobalRef.name_there {g : GlobalDecl} {ds : List GlobalDecl} {τ : Ty}
    (r : GlobalRef ds τ) : (GlobalRef.there (g := g) r).name = r.name := rfl

/-- The name of a reference is one of the names the signature declares. -/
theorem GlobalRef.name_mem {ds : List GlobalDecl} {τ : Ty} (r : GlobalRef ds τ) :
    r.name ∈ ds.map GlobalDecl.name :=
  List.mem_map_of_mem r.entry_mem

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

/-! ## Recursions have a context of their own

A self-reference is no more a value than a label is: it can be *called*, and nothing
else.  So it lives in a context of its own, `Ρ`, whose entries record what a recursion
takes and what it answers with — and **not** its measure.  That omission is the whole
termination argument of the grammar: a `Term.selfCall` has nowhere to put a bound, so the
only descent a recursion can ever make is the one the semantics checks for it — the
measure at the arguments of the call, against the measure of the activation it is made
from.
-/

/-- The signature of a recursion in scope: the types of its arguments and the type it
    answers with.  There is deliberately **no measure component**. -/
structure RSig where
  /-- The argument types of the recursive function. -/
  ps : List Ty
  /-- Its result type. -/
  ret : Ty
  deriving DecidableEq

/-- The recursions whose body we are inside, innermost first. -/
abbrev RCtx := List RSig

/-- A recursion in scope: a de Bruijn index into `Ρ`, separate from the index of a
    variable and from the index of a label — again the same family, at a third entry
    type. -/
abbrev RVar (Ρ : RCtx) (r : RSig) : Type := DeBruijn Ρ r

/-- The innermost recursion. -/
abbrev RVar.head {Ρ : RCtx} {r : RSig} : RVar (r :: Ρ) r := DeBruijn.head

/-- A recursion bound further out. -/
abbrev RVar.tail {Ρ : RCtx} {r s : RSig} (v : RVar Ρ r) : RVar (s :: Ρ) r :=
  DeBruijn.tail v

/-- Membership notation for recursions: `Ρ ∋ᵣ r`. -/
infix:40 " ∋ᵣ " => RVar

/-- The de Bruijn index of a recursion. -/
abbrev RVar.index {Ρ : RCtx} {r : RSig} (v : RVar Ρ r) : Nat := DeBruijn.index v

/-! ## Terms -/

mutual

/-- A well-scoped, simply-typed term of the module whose signature is `Sg`, in the
    variable context `Γ` and the recursion context `Ρ`.  A term has **no** label context:
    a jump is a `Tail`, never a `Term`, so no value position of the language can hold
    one. -/
inductive Term (Sg : Sig) : Ctx → RCtx → Ty → Type
  /-- A variable of `Γ`. -/
  | var : ∀ {Γ Ρ τ}, Γ ∋ τ → Term Sg Γ Ρ τ
  /-- `fun x => body`: **one** parameter, since every function is curried. -/
  | lam : ∀ {Γ Ρ σ τ}, Term Sg (σ :: Γ) Ρ τ → Term Sg Γ Ρ (σ ⇒ τ)
  /-- `f a`: **one** argument. -/
  | ap  : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ (σ ⇒ τ) → Term Sg Γ Ρ σ → Term Sg Γ Ρ τ
  /-- A constant of a terminal type. -/
  | lit : ∀ {Γ Ρ} {p : LeanPrimTy}, LeanPrimLit p → Term Sg Γ Ρ (.prim p)
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ Ρ τ}, GlobalRef Sg.decls τ → Term Sg Γ Ρ τ
  /-- A function Lean implements with `@[extern]`, named by the catalogue
      `LakeJs.Externs`, at the curried type its argument list gives it. -/
  | extern : ∀ {Γ Ρ σs τ}, Externs σs τ → Term Sg Γ Ρ (Ty.arrows σs τ)
  /-- Delay a value.  This is what a Lean `fun (_ : Unit) => e` becomes: the parameter is
      the one value of a unit type, which carries nothing at run time and is erased, so
      what is left is a delayed value — and `Ty.lazy` is exactly that.

      **Unmemoised**: forcing it twice runs it twice. -/
  | lazyMk : ∀ {Γ Ρ τ}, Term Sg Γ Ρ τ → Term Sg Γ Ρ (.lazy τ)
  /-- Run a delayed value: what an application `f ()` becomes once the unit argument is
      erased. -/
  | lazyForce : ∀ {Γ Ρ τ}, Term Sg Γ Ρ (.lazy τ) → Term Sg Γ Ρ τ
  /-- `let x = e; body` — `x` is de Bruijn index 0 of `body`. -/
  | letE : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ σ → Term Sg (σ :: Γ) Ρ τ → Term Sg Γ Ρ τ
  /-- `if c then t else e`. -/
  | ite : ∀ {Γ Ρ τ},
      Term Sg Γ Ρ (.prim .bool) → Term Sg Γ Ρ τ → Term Sg Γ Ρ τ → Term Sg Γ Ρ τ
  /-- A tagged value, built **at a type whose layout says so**.  `h` is the evidence that
      `τ` has a constructor number `i`, and which fields it has; the arguments are then a
      spine of exactly those types.  So a constructor cannot be built at a type that has
      no such constructor, with a field missing, a field too many, the fields in the
      wrong order, or a field of the wrong type. -/
  | ctor : ∀ {Γ Ρ τ}, (i : Nat) → (fields : FieldLayout) →
      (h : τ.ctorFields? i = some fields) → Spine Sg Γ Ρ fields → Term Sg Γ Ρ τ
  /-- A field of a tagged value.  `h` is the evidence that constructor `i` of `σ` has a
      field `j`, *of type `τ`*, so a field the type does not have cannot be read.

      `hOne` is what makes the read **sound**: `σ` has exactly one constructor, so the
      constructor the value was built with is the one this projection speaks about.  A
      field of a type with several constructors is reached by a `Term.caseTag`, whose
      alternative *binds* the fields of the constructor it matches. -/
  | proj : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ σ → (i j : Nat) →
      (hOne : σ.numCtors? = some 1) →
      (h : σ.fieldTy? i j = some τ) → Term Sg Γ Ρ τ
  /-- The runtime tag of a value whose type has a layout: how a dispatch tests which
      constructor it has. -/
  | tagOf : ∀ {Γ Ρ σ}, Term Sg Γ Ρ σ → (h : σ.isTagged = true) → Term Sg Γ Ρ (.prim .nat)
  /-- The **structural size** of a value: the measure a structurally recursive function
      descends on.  It is the size of the value's runtime tree, an ordinary total
      function of the value, so it is no new piece of trust — and it is the one thing the
      front end needs in order to turn "recurses on a strict sub-component" into a
      measure. -/
  | structSize : ∀ {Γ Ρ σ}, Term Sg Γ Ρ σ → Term Sg Γ Ρ (.prim .nat)
  /-- A dispatch on the tag of a value.  An alternative **binds the fields** of the
      constructor it matches, in declaration order, so de Bruijn index `0` of its body is
      the constructor's first field.  `h` says that every tag branched on is a
      constructor of `σ` and that none is repeated, so a case cannot test an impossible
      tag; and a case cannot fall off the end of its branches either, because `Alts` ends
      *either* in a default branch (`full = false`) *or* in nothing at all with a branch
      for every constructor (`full = true`, `Ty.caseOkFull`). -/
  | caseTag : ∀ {Γ Ρ σ τ tags full}, Term Sg Γ Ρ σ → Alts Sg Γ Ρ σ τ tags full →
      (h : σ.caseOkAlts full tags = true) → Term Sg Γ Ρ τ
  /-- **A block**: the one way a term uses labels.  Its tail is written in the *empty*
      label context, so a block is closed for jumps — a `break` of the target never
      crosses the boundary of the block it is in. -/
  | block : ∀ {Γ Ρ τ}, Tail Sg Γ [] Ρ τ → Term Sg Γ Ρ τ
  /-- **The one recursion construct.**  `measure` is the `k`-component lexicographic
      termination measure, read off the arguments; `body` is the function's body, with the
      recursion itself in scope as the innermost entry of `Ρ`; `stuck` is the answer to a
      self call that does **not** descend, which for a faithfully translated Lean function
      never happens.

      A structurally recursive function has for its measure the `Term.structSize` of the
      argument it recurses on; a well-founded one has the transcribed components of its
      `termination_by`.  Nothing else can be written. -/
  | fix : ∀ {Γ Ρ τ}, (ps : List Ty) → (k : Nat) →
      (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k)) →
      (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) →
      (stuck : Term Sg (ps ++ Γ) Ρ τ) →
      Term Sg Γ Ρ (Ty.arrows ps τ)
  /-- **The one way to recurse**: call a recursion of `Ρ` with a full argument list.
      There is no measure argument, and no syntax for one. -/
  | selfCall : ∀ {Γ Ρ ps τ}, (Ρ ∋ᵣ ⟨ps, τ⟩) → Spine Sg Γ Ρ ps → Term Sg Γ Ρ τ

/-- A list of terms, typed by the list of their types: the arguments of an operation, the
    arguments of a jump, the arguments of a self call, the fields of a constructor. -/
inductive Spine (Sg : Sig) : Ctx → RCtx → List Ty → Type
  | nil  : ∀ {Γ Ρ}, Spine Sg Γ Ρ []
  | cons : ∀ {Γ Ρ σ σs}, Term Sg Γ Ρ σ → Spine Sg Γ Ρ σs → Spine Sg Γ Ρ (σ :: σs)

/-- The branches of a `Term.caseTag` on a value of type `σ`, keyed by constructor tag and
    indexed by the list of tags they test, in order, and by whether that list is
    **exhaustive**.  An alternative binds the fields of its constructor: its body is
    written in `fields ++ Γ`, and `h` is the evidence that those are exactly the fields
    the layout gives that constructor.

    A list ends either in `Alts.deflt`, a default branch, or — when `full = true` — in
    `Alts.nilFull`, which is only usable at a `Ty.caseOkFull`, i.e. when every constructor
    has a branch of its own.  Either way no dispatch can fall off the end. -/
inductive Alts (Sg : Sig) : Ctx → RCtx → Ty → Ty → List Nat → Bool → Type
  /-- The default branch a dispatch ends with. -/
  | deflt : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ τ → Alts Sg Γ Ρ σ τ [] false
  /-- The end of an **exhaustive** dispatch: no default branch, because every constructor
      has a branch of its own (`Ty.caseOkFull`). -/
  | nilFull : ∀ {Γ Ρ σ τ}, Alts Sg Γ Ρ σ τ [] true
  /-- One more branch, binding the fields of the constructor it matches. -/
  | cons  : ∀ {Γ Ρ σ τ tags full}, (tag : Nat) → (fields : FieldLayout) →
      (h : σ.ctorFields? tag = some fields) →
      Term Sg (fields ++ Γ) Ρ τ → Alts Sg Γ Ρ σ τ tags full →
      Alts Sg Γ Ρ σ τ (tag :: tags) full

/-- A **tail**: a basic block of the block grammar, in the variable context `Γ`, the label
    context `Ω` and the recursion context `Ρ`, answering with `τ`.  Every position of a
    `Tail` is a tail position of the enclosing `Term.block`, which is why a jump is
    allowed here and nowhere else. -/
inductive Tail (Sg : Sig) : Ctx → LCtx → RCtx → Ty → Type
  /-- Answer with this value: the block is done. -/
  | ret : ∀ {Γ Ω Ρ τ}, Term Sg Γ Ρ τ → Tail Sg Γ Ω Ρ τ
  /-- Jump to a join point in scope, with one argument per parameter.  A jump never comes
      back, so it stands at **any** answer type: it is the whole of the rest of this
      block. -/
  | jmp : ∀ {Γ Ω Ρ ps τ}, Ω ∋ₗ ps → Spine Sg Γ Ρ ps → Tail Sg Γ Ω Ρ τ
  /-- `let x = e;` in front of the rest of the block. -/
  | letT : ∀ {Γ Ω Ρ σ τ}, Term Sg Γ Ρ σ → Tail Sg (σ :: Γ) Ω Ρ τ → Tail Sg Γ Ω Ρ τ
  /-- A two-way branch, both arms being blocks. -/
  | iteT : ∀ {Γ Ω Ρ τ},
      Term Sg Γ Ρ (.prim .bool) → Tail Sg Γ Ω Ρ τ → Tail Sg Γ Ω Ρ τ → Tail Sg Γ Ω Ρ τ
  /-- A dispatch on the tag of a value, every arm being a block. -/
  | caseT : ∀ {Γ Ω Ρ σ τ tags full}, Term Sg Γ Ρ σ → AltsT Sg Γ Ω Ρ σ τ tags full →
      (h : σ.caseOkAlts full tags = true) → Tail Sg Γ Ω Ρ τ
  /-- **A join point**, taking the arguments `ps`, in scope in `rest` as label index `0`.

      Its `body` is typed in the *outer* label context `Ω`, so it cannot jump back to
      itself — control passes through it once per jump (`l: { … }` with `break l` in the
      target).  There is no loop here, and none can be written: repeating work is
      `Term.fix` and nothing else.

      Inside `body`, de Bruijn index `0` is the **first** argument of the join point,
      i.e. the variable context is `ps ++ Γ`. -/
  | join : ∀ {Γ Ω Ρ τ}, (ps : List Ty) →
      (body : Tail Sg (ps ++ Γ) Ω Ρ τ) →
      (rest : Tail Sg Γ (ps :: Ω) Ρ τ) → Tail Sg Γ Ω Ρ τ

/-- The branches of a `Tail.caseT`: `Alts`, with a block in place of each term, so that a
    branch may answer *or* jump. -/
inductive AltsT (Sg : Sig) : Ctx → LCtx → RCtx → Ty → Ty → List Nat → Bool → Type
  /-- The default branch a dispatch ends with. -/
  | deflt : ∀ {Γ Ω Ρ σ τ}, Tail Sg Γ Ω Ρ τ → AltsT Sg Γ Ω Ρ σ τ [] false
  /-- The end of an **exhaustive** dispatch: no default branch. -/
  | nilFull : ∀ {Γ Ω Ρ σ τ}, AltsT Sg Γ Ω Ρ σ τ [] true
  /-- One more branch, binding the fields of the constructor it matches. -/
  | cons : ∀ {Γ Ω Ρ σ τ tags full}, (tag : Nat) → (fields : FieldLayout) →
      (h : σ.ctorFields? tag = some fields) →
      Tail Sg (fields ++ Γ) Ω Ρ τ → AltsT Sg Γ Ω Ρ σ τ tags full →
      AltsT Sg Γ Ω Ρ σ τ (tag :: tags) full

end

/-- Apply a curried term to a spine, one argument at a time: `f a₁ … aₙ`. -/
def Term.appSpine {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} :
    ∀ {σs : List Ty} {τ : Ty},
      Term Sg Γ Ρ (Ty.arrows σs τ) → Spine Sg Γ Ρ σs → Term Sg Γ Ρ τ
  | [], _, f, .nil => f
  | _ :: _, _, f, .cons a rest => Term.appSpine (.ap f a) rest

/-- A Lean function the runtime implements, applied to exactly the arguments it takes:
    iterated `Term.ap` of `Term.extern`. -/
def Term.callExtern {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σs : List Ty} {τ : Ty}
    (e : Externs σs τ) (args : Spine Sg Γ Ρ σs) : Term Sg Γ Ρ τ :=
  Term.appSpine (.extern e) args

-- Notation
prefix:100 "ƛ " => Term.lam
infixl:70 " ⬝ " => Term.ap

/-- Sugar: `♯0` is the innermost variable, `♯1` the one before it, … -/
macro "♯" n:term:90 : term => `(Term.var (v♯ $n))

namespace Term

/-- A `Nat` literal. -/
abbrev natL {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} (n : Nat) : Term Sg Γ Ρ Ty.nat :=
  .lit (.nat n)

/-- A `Bool` literal. -/
abbrev boolL {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} (b : Bool) : Term Sg Γ Ρ Ty.bool :=
  .lit (.bool b)

/-- An `Int` literal. -/
abbrev intL {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} (i : Int) : Term Sg Γ Ρ Ty.int :=
  .lit (.int i)

/-- A `String` literal. -/
abbrev strL {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} (s : String) : Term Sg Γ Ρ Ty.string :=
  .lit (.string s)

/-- The identity function, `fun x => x`. -/
def idTerm {Sg : Sig} {Ρ : RCtx} {τ : Ty} : Term Sg [] Ρ (τ ⇒ τ) :=
  ƛ ♯0

/-- The constant function, `fun x y => x`. -/
def const {Sg : Sig} {Ρ : RCtx} {τ1 τ2 : Ty} : Term Sg [] Ρ (τ1 ⇒ τ2 ⇒ τ1) :=
  ƛ (ƛ ♯1)

/-- A term with two free variables, in the context `[α, α ⇒ β]`. -/
def freeTerm {Sg : Sig} {Ρ : RCtx} {α β : Ty} : Term Sg [α, α ⇒ β] Ρ β :=
  ♯1 ⬝ ♯0

/-- A term with one free variable: `fun y => y x₀`, in the context `[α]`. -/
def boundAndFree {Sg : Sig} {Ρ : RCtx} {α β : Ty} : Term Sg [α] Ρ ((α ⇒ β) ⇒ β) :=
  ƛ (♯0 ⬝ ♯1)

/-! ## A recursion, by hand

`SnapshotsPBOPure/Tco01.lean` is `def test (n : Nat) : Nat := match n with | 0 => n
| n + 1 => test n`.  Lean proves it terminating by structural recursion on `n`, so the
front end accepts it, and what it becomes here is one `Term.fix`: one argument, the
one-component measure read off that argument, an exit and a self call. -/

/-- `test` of `Tco01`, by hand.  The measure is `n`, transcribed verbatim: the one self
    call is at `n - 1`, which descends, so the `stuck` branch is unreachable. -/
def tco01 {Sg : Sig} {Ρ : RCtx} : Term Sg [] Ρ (.nat ⇒ .nat) :=
  .fix [Ty.nat] 1 (.cons (♯0) .nil)
    (.ite (callExtern (.prim2 .lean_nat_dec_eq) (.cons (♯0) (.cons (natL 0) .nil)))
      (♯0)
      (.selfCall .head
        (.cons (callExtern (.prim2 .lean_nat_sub) (.cons (♯0) (.cons (natL 1) .nil)))
          .nil)))
    (♯0)

/-- An **exhaustive** dispatch of terms: `Bool` has two constructors and both have a
    branch, so the case needs no default branch at all.  Neither constructor has a field,
    so neither branch binds anything. -/
def notTerm {Sg : Sig} {Ρ : RCtx} : Term Sg [Ty.bool] Ρ Ty.bool :=
  .caseTag (♯0)
    (.cons 0 [] (by decide) (boolL true)
      (.cons 1 [] (by decide) (boolL false) .nilFull))
    (by decide)

/-- A shared tail, by hand: bind a join point of one `Nat` argument and jump to it from
    both arms of a branch — the block a dispatch would otherwise duplicate. -/
def sharedTail {Sg : Sig} {Ρ : RCtx} : Term Sg [Ty.bool] Ρ Ty.nat :=
  .block
    (.join [Ty.nat] (.ret (♯0))
      (.iteT (♯0)
        (.jmp .head (.cons (natL 1) .nil))
        (.jmp .head (.cons (natL 2) .nil))))

/-- A join point **inside the body of a recursion**: the two arms of the branch share a
    tail, and that tail performs the self call.  A join point and a recursion are
    different constructs here, and this is the shape in which they meet. -/
def sharedTailInFix {Sg : Sig} {Ρ : RCtx} : Term Sg [] Ρ (.nat ⇒ .nat) :=
  .fix [Ty.nat] 1 (.cons (♯0) .nil)
    (.block
      (.join [Ty.nat]
        (.ret (.selfCall .head (.cons (♯0) .nil)))
        (.iteT (callExtern (.prim2 .lean_nat_dec_eq) (.cons (♯0) (.cons (natL 0) .nil)))
          (.ret (natL 0))
          (.jmp .head
            (.cons (callExtern (.prim2 .lean_nat_sub)
              (.cons (♯0) (.cons (natL 1) .nil))) .nil)))))
    (♯0)

end Term

/-- The number of arguments in a spine. -/
def Spine.length {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σs : List Ty} (s : Spine Sg Γ Ρ σs) :
    Nat :=
  match s with
  | .nil => 0
  | .cons _ rest => rest.length + 1

/-- The number of branches of a case, the default branch included. -/
def Alts.length {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool}
    (a : Alts Sg Γ Ρ σ τ tags full) : Nat :=
  match a with
  | .deflt _ => 1
  | .nilFull => 0
  | .cons _ _ _ _ rest => rest.length + 1

/-- The number of branches of a dispatch inside a block. -/
def AltsT.length {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat}
    {full : Bool} (a : AltsT Sg Γ Ω Ρ σ τ tags full) : Nat :=
  match a with
  | .deflt _ => 1
  | .nilFull => 0
  | .cons _ _ _ _ rest => rest.length + 1

end LakeJs.Expr

end
