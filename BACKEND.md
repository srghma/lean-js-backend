# `lean-to-js-backend`

A Lean-to-JavaScript backend that reads what Lean already stored in the `.olean` files
and prints a JavaScript module beside the source.

```
lake build lean-to-js-backend
lake env ./.lake/build/bin/lean-to-js-backend SnapshotsPBOPure/Tco01.lean
#   SnapshotsPBOPure/Tco01.lean -> SnapshotsPBOPure/Tco01.js

lake env ./.lake/build/bin/lean-to-js-backend --check  SnapshotsPBOPartial/RecursiveBindingGroup01.lean
lake env ./.lake/build/bin/lean-to-js-backend --stdout SnapshotsPBOPure/Tco01.lean
```

`lake test` runs the backend over **every** snapshot of `SnapshotsPBOPure` — the
directory is read as the test runs, so a snapshot added to it is tested without any list
being edited — and over the pure modules of `SnapshotsMy`, and checks each verdict.

## The pipeline

| Step | Where |
| :--- | :--- |
| read the **`saveBase`** LCNF phase out of the `.olean` | `LakeJs/FromLcnf.lean` |
| refuse what must not be compiled | `LakeJs/Totality.lean` |
| translate to the typed `Term` | `LakeJs/FromLcnf.lean`, `LakeJs/Compile.lean` |
| print with `MiniAST` | `LakeJs/EmitJs.lean` |

It is the `saveBase` phase deliberately, not `Lean.IR`, not `saveMono` and not the
result phase: those have already erased the types, and by then a `Nat`, a `UInt32`, a
`Char` and a one-field structure all look alike, so neither the choice of JavaScript
representation nor an optimiser that wants to work against types can be made any more.
`base` still carries the LCNF type of every binder.

## What is refused, and why

The backend compiles a recursive Lean function to a JavaScript loop or to a plain
recursive call. Either is faithful only when the function terminates, so a module is
refused outright — with a message naming the declaration — when it reaches:

* a **`partial def`** (Lean did not prove it terminating; it is stored as an `opaque`
  constant with an `unsafe` implementation beside it, which is what the check looks
  for);
* an **`unsafe def`** of a module being compiled;
* an **IO entry point** (`IO`, `EIO`, `BaseIO`, `ST`, `EST`, `EStateM`): the source
  language here is pure;
* a declaration of a module being compiled with **no body**: an `opaque`, or one
  implemented by `@[extern]`.

A single declaration — rather than the whole module — is skipped, with the reason
reported, when its body is not expressible as a pure `Term`: it reaches LCNF's
`.unreach`, or it branches on a value without covering every constructor and without a
default. There is no `throw` in the language to compile those to.

Two deliberate exceptions keep the check useful rather than absolute:

* Lean's own library implements several *proved total* functions by an `unsafe` loop
  (`Array.mapM` is `Array.mapMUnsafe.map`) and hands the backend a specialization of it.
  Outside the modules being compiled, what is refused is a declaration whose origin Lean
  marks `partial`, not every `unsafe` one.
* An `opaque` or `@[extern]` declaration of the standard library — `String.hash`,
  `String.Internal.append` — is a *primitive of the runtime*: it has no Lean body
  because the platform implements it, not because it might not terminate. Such a call is
  printed as a call of the corresponding `Externs` constructor (`$lean_string_append`);
  a runtime prelude defining those names is not part of this iteration.

## Why no `Term` can be an Omega

`Term Sg Γ τ` (`LakeJs/Expr.lean`) is well-scoped and simply typed, and two facts about
it are proved in `LakeJs/TermTotal.lean`:

* `Ty.ne_arrow_self : σ ≠ .fn [σ] τ` — no type is its own argument type, so a
  self-application `x x` does not typecheck and `ω = λx. x x`, the `Y` combinator and
  every fixed point built from self-application are not `Term`s;
* `Term.loopCount` counts `Term.loop` nodes, and every other constructor's count is the
  sum of its children's: the grammar has no recursive-definition node at all, so the
  only repetition a `Term` can express is the `while` loop of `Term.loop`, whose body
  either answers (`Body.ret`) or goes round again (`Body.cont`).

A declaration that calls *itself in tail position* becomes exactly that loop. A
declaration that calls itself elsewhere becomes an ordinary JavaScript function that
calls itself — which is what the Lean source does too, and which terminates because the
totality gate above has already established that the Lean function does.

## A mutually tail-recursive group is one merged loop

Two declarations that tail-call each other must not become two JavaScript functions
calling each other: each call would grow the stack, and neither engine nor language
removes it. So a group of declarations that call one another — the strongly connected
component of the module's call graph — is compiled, when its members do tail-call one
another, into **one** function with a single dispatch loop, plus one wrapper per member
that enters it (`LakeJs.Compile.transGroup`):

```js
const _mut$test1 = (v0, v1) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v2 === 0) { /* test1 */ } else { /* test2 */ }
  }
  return r$2;
};
const test1 = (v0) => _mut$test1(0, v0);
const test2 = (v0) => _mut$test1(1, v0);
```

The loop variables are the **tag** of the member that is currently running followed by
one **argument slot** per parameter — as many slots as the widest member has, so members
of different arities share one loop and a member that does not use a slot passes `0`
for it — a pure, total value that is never read, where the slot used to be filled with
`undefined`. Where two members give a slot different types, the slot is
`Ty.typeParam`; nothing is inserted into the output either way.

A tail call to *any* member of the group is then a `Body.cont` of that one loop: it
assigns the new tag and the new arguments and goes round again. Nothing is pushed, so a
mutually tail-recursive group runs in constant JavaScript stack, exactly as a self
tail-recursive one does. Under `node`, `MutualTail.test1(100000)`,
`MutualTail.test3(100000, 0)` and `CaptureDerefRegression01.testOdd(100000, …)` now
answer (`true`, `199999`, `250000`); every one of them raised
`RangeError: Maximum call stack size exceeded` when the group was two functions calling
each other. A call to a member that is *not* in tail position still goes through that
member's wrapper, which re-enters the loop.

A group whose members never tail-call one another gains nothing from a loop, so it is
left as the ordinary mutually recursive functions it is: `cata`/`cataMap` of
`SnapshotsPBOPure/RecursionSchemes01` call each other under a constructor, and stay two
functions.

## Every name a term mentions is declared

A `Term` is written against a **module signature**, the list of top-level declarations
the emitted JavaScript module binds together with the imported ones it calls:

```lean
structure GlobalDecl where
  name : String   -- the JavaScript identifier it is bound to
  ty   : Ty

abbrev Sig := List GlobalDecl

inductive GlobalRef : Sig → Ty → Type
  | here  : GlobalRef (g :: Sg) g.ty
  | there : GlobalRef Sg τ → GlobalRef (g :: Sg) τ
```

`Term.global : GlobalRef Sg τ → Term Sg Γ τ` is the only way to name a top-level
declaration, and a `GlobalRef` is a de Bruijn index into `Sg`, so both the name and the
type come from the signature. A call of a name the module neither declares nor imports,
or a call of a declared name at a type it does not have, is *unrepresentable* — where
the old `Term.global (name : String) (τ : Ty)` accepted any string at any type.
`LakeJs.Compile` therefore computes the whole signature first — the module's own
declarations (including the unboxed instance fields below and the merged `_mut$…` loops)
and every imported constant the code mentions — and translates all declarations against
that one fixed `Sg`.

## Primitives and externs carry their types

`JsPrim` is indexed by the list of its argument types and by its result type:

```lean
inductive JsPrim : List Ty → Ty → Type
  | add (τ : Ty)      : JsPrim [τ, τ] τ
  | arrayGet (α : Ty) : JsPrim [.array α, .nat] α
  | cast (σ τ : Ty)   : JsPrim [σ] τ
  …
```

and `Term.prim : JsPrim σs τ → Spine Sg Γ σs → Term Sg Γ τ` takes a spine of exactly
those types, so a primitive applied to the wrong number of arguments, or to arguments of
the wrong type, is not a `Term`. The printer needs no arity fallback, and the old
`runtime (name : String)` escape hatch — an unchecked call of an arbitrary JavaScript
name — is gone. When the translation meets a primitive used as a *value* rather than
fully applied, it eta-expands it (`Bool.beq` becomes `(v0, v1) => v0 === v1`) instead of
printing a name.

The functions Lean implements with `@[extern]` are a second closed catalogue:
`LakeJs/Externs.lean` is an inductive `Externs : Ty → Type` with one constructor per
extern, and `Term.extern : Externs τ → Term Sg Γ τ` puts it in the language. Two
generated files carry the metadata (`python3 scripts/gen-externs-meta.py` rebuilds both;
do not edit them by hand):

* `LakeJs/ExternsMeta.lean` — `Externs.cName` and `Externs.arity` for all 593
  constructors;
* `LakeJs/ExternTable.lean` — `externTable`, a lookup from the Lean name to the
  constructor, and `externFor?`.

An extern prints as `$` followed by its C name, and a saturated call prints as a call:

```js
const v12 = $lean_uint64_of_nat(v6);
const v15 = $lean_uint64_xor(v12, v14);
```

An extern that is *not* saturated prints as a curried wrapper, so the arity of the
emitted call always matches the arity of the runtime function. Any other known standard
library function the backend wants to optimise is added as a `JsPrim` or an `Externs`
constructor — never as a string.

## Instances are unboxed

A class instance is a structure whose fields are known at compile time, so there is no
reason to build the record at run time. An instance declaration is emitted as **one
constant per field**, named `<instance>_<field>`:

```js
const instToStringExpr_toString = renderExpr;
```

where the record-building form used to be an IIFE returning a record. A
single-field instance whose field is exactly a known function collapses further, by the
simplifier's eta rule, to the function itself — which is the line above.

A function that takes an instance it does not know is given the instance's **fields** as
parameters, one JavaScript parameter each (`LakeJs.FromLcnf.Binding.split`,
`LakeJs.Compile.expandParams`), and each call site passes the corresponding fields:

```js
const List_forIn__loop__at__test7_spec_0 = (v0, v1, v2, v3, v4) => …;
…
List_forIn__loop__at__test7_spec_0(…, v4._1, v2._1, …);
```

The plan for an instance type (`LakeJs.Compile.instPlanOfType?`) is read from the
class's own constructor rather than from the LCNF type, which keeps it free of the
foreign free variables LCNF types carry; `Prop`-valued and sort-valued fields are
skipped. Where an instance genuinely has to exist as a value — it is passed to something
that is not compiled field-wise — the backend falls back to a private `<name>$box`
constant built from the field constants. Reading the environment's class information
needs `Lean.importModules … (loadExts := true)`; without it `Lean.isClass` answers
`false` and nothing is unboxed.

## The type language: a tree of types, with one `.self` binder per recursive shape

A compiled datatype has **no names at run time**, and `Ty` has no names in it either: a
type is a *tree*, built out of its own parts, and two types are equal when their trees
are (an ordinary structural `DecidableEq`, `Ty.beq`). A constructor is a *position* and
a field is a *position*, so a value prints as `{ tag: 0, _1: … }`, a field read as
`v._1` and a branch as `v.tag === 0`.

The shapes a user-defined type can have are spelled out, one constructor each, rather
than being one `obj` with a flag:

```lean
inductive Ty
  | prim       : PrimTy → Ty                       -- a scalar leaf
  | typeParam  : Ty                                -- a value of a type parameter
  | shape      : Shape Ty → Ty                     -- fn, array, list, task, promise, thunk
  | enum       : Nat → Ty                          -- `north | south`
  | record     : List Ty → Ty                      -- one constructor, ≥ 2 fields
  | taggedUnion : List (List Ty) → Ty              -- `Option`, `Except`, …
  | recTaggedUnion : List (List RTy) → Ty          -- a recursive sum
  | recObject  : List RTy → Ty                     -- a recursive record
  | recAlias   : RTy → Ty                          -- a recursive newtype, wrapper erased
  | mutualRecursiveFamily : List FamMember → Nat → Ty
```

Three things are worth saying about that list.

**The shared formers are shared.** `fn`, `fn_returnsProd`, `array`, `list`, `task`,
`promise` and `thunk` say nothing about recursion and make sense at every layer, so they
are not repeated: they are the constructors of one parameterised inductive, `Shape`,
which both layers embed. `Ty.fn`, `Ty.array`, … remain available — and usable in
patterns — as abbreviations for `Ty.shape (Shape.fn …)` and friends.

**`.self` is available in the recursive shapes and nowhere else.** The four recursive
shapes are the *binders* of the type language: their children are `RTy`s, the types
*inside* a recursive declaration, and `RTy.self i` is an occurrence of member `i` of
that declaration (`i = 0` unless the binder is a mutual family). `RTy` mirrors `Ty`, so
anything may appear inside a recursive declaration — a `Nat`, an `Option Tree`
(`.taggedUnion [[], [.self 0]]`), an `Array Tree`; where an `RTy` is itself a recursive
shape it opens a new scope, and its children's `.self` is that inner declaration. A
closed `Ty` has no `.self` constructor at all, so the old `Ty.selfRef` — representable
at the top level, where it meant nothing — is gone.

**There is no `dynamic`.** Every Lean type a compiled declaration mentions is modelled,
or the declaration is refused. A parameterised declaration is modelled *at its
instantiation* (`Except Nat String` is `.taggedUnion [[.nat], [.string]]`), a mutual
block is modelled as a `mutualRecursiveFamily`, and a single-constructor declaration
with a single runtime field is a **newtype**: its wrapper is erased, its `Ty` is the
field's own `Ty`, building one is its field and reading its field is the value itself.
The built-in cons list has the layout it has at run time,
`[[], [α, list α]]`; `Unit` is `.enum 1`; `Ordering` is `.enum 3`; a `Decidable` is the
boolean it decides.

The one type that stands for a value whose shape the backend does not know is
`Ty.typeParam`, and it is *parametricity*, not ignorance: it is the type of a value
whose Lean type is a type parameter of the enclosing declaration — the `α` of
`def f (xs : List α)`. Lean erases type arguments, so the compiled function can pass
such a value on, store it and return it, and **no** data operation is available at it
(`Ty.ctorFields?_typeParam`, `Term.no_ctor_at_typeParam`). The unchecked operations that
used to live at `Ty.dynamic` — `Term.dynCtor`, `Term.dynProj`, `Term.dynTag`,
`Term.dynCase` — no longer exist, so every data access in a compiled module is checked
against a layout.

The three data operations ask for the evidence that the layout really has what they
name:

```lean
| ctor   (i : Nat) (fields : FieldLayout) (h : τ.ctorFields? i = some fields) :
           Spine Sg Γ fields → Term Sg Γ τ
| proj   (e : Term Sg Γ σ) (i j : Nat) (h : σ.fieldTy? i j = some τ) : Term Sg Γ τ
| caseTag (s : Term Sg Γ σ) (alts : Alts Sg Γ τ tags) (h : σ.caseOk tags) : Term Sg Γ τ
```

So `{ tag: 0, _1: … }` is never a term of a function type or of a scalar type, and
`f._1` is never emitted for an `f` that is a function (`Term.no_ctor_at_function`,
`Term.no_proj_of_function`, `Term.no_ctor_at_scalar` in `LakeJs/TermTotal.lean`).
`Ty.layout?` (in `LakeJs/Layout.lean`) is what turns a shape into the layout those
operations are checked against, resolving the `.self`s; the worked examples at the end
of that module show each shape and its layout, and are checked by the build.

Reading the fields of a Lean declaration means agreeing with LCNF about which of them
survive: a field that is a type, a type family or a proof is dropped on both sides
(`isTypeOrProofTy`), including the case where the field's type is a *parameter* of the
declaration, as `Subtype`'s `property : p val` is. A projection, whose index LCNF takes
from the declaration and not from the layout, is renumbered (`runtimeFieldIndex`), so
`structure Unfold where State : Type; seed : State; …` reads `seed` as `_1` and not as
`_2`.

## Nothing erased, and nothing that throws

A type argument, a type family and a proof carry nothing at run time, so `Ty` has no
constructor for them and `Term` no literal for them: such a binder is **dropped**
outright (`LakeJs.FromLcnf.isErasedLcnfTy`). A dropped parameter is no JavaScript
parameter, a dropped argument is no argument — an emitted call never passes `undefined`
for one — and a dropped `let` is not emitted.

Every `Term` is also **pure and total**: there is no `throw`, no panic and no
`unreachable` node to print one. A branch Lean proved impossible — an LCNF `.unreach` —
needs no value, so it is **dropped** before the dispatch is built
(`LakeJs.FromLcnf.liveAlts`): the tag it tests is never tested and control reaches a
sibling branch instead, which is faithful precisely because the branch cannot be taken.
Where a dispatch has *no* branch left — every path through it is unreachable, so the
declaration can never answer — the declaration is *refused* with a message naming it,
rather than compiled into something that could throw. `SnapshotsMy/UnreachBranch.lean`
is the worked example: `small (n : Nat) (h : n < 3)` and `headOf (xs : List Nat)
(h : xs ≠ [])` both compile, to a chain of tests with no fallback and to a pair of
projections.

That a dispatch needs no fallback is proved, not asserted: `Alts.select` (in
`LakeJs/TermTotal.lean`) is the branch a runtime tag takes, a *total* function of that
tag, and `Alts.select_mem_branches` says the branch it takes is always one of the
branches the case has — for a tag the case tests, for one it does not, and for a number
no constructor has. `Alts.select_of_not_mem` identifies that branch as the default one.

That every sub-expression is a value is what lets an optimiser reorder, duplicate or
drop any of them without changing what the module does. It also means the emitted
module never mentions a name of its own that it does not bind: a declaration the
translation could not handle is dropped together with everything that calls it,
transitively, and each of them is reported.

## The simplifier

`LakeJs.Simp.Term.simp` (`LakeJs/Simp.lean`) is a bottom-up pass over `Term`, total and
type-preserving by construction — it maps `Term Sg Γ τ` to `Term Sg Γ τ`, so it cannot
change what a term means to the type system. It does three things:

* `let x = e; x` ⟶ `e`;
* `let x = e; cast x` ⟶ `cast e`;
* eta: `(v0, …, vn) => f(v0, …, vn)` ⟶ `f`, when `f` is a global or an extern, seeing
  through one `cast` layer.

The eta rule is what turns an unboxed one-field instance into `const
instToStringExpr_toString = renderExpr;`.

## The types

`LakeJs/Ty.lean` gained one constructor for this work:

```lean
| fn_returnsProd : (params : List Ty) → (ret1 : Ty) → (retRest : List Ty) → Ty
```

a function answering with several values at once, printed as an uncurried function whose
`return` is an array literal. `Term.lamProd` is the only way to build one, so such a
function always does return a tuple:

```lean
def foo : Term [] (.fn [Ty.int, Ty.float] (.fn_returnsProd [Ty.int, Ty.float] Ty.int [Ty.float]))
```

prints as

```js
const foo = (v0, v1) => (v2, v3) => {
  return [1, 1.0];
};
```

The list of results is spelled as a first result and the rest rather than as a
`NonEmptyList Ty`: the kernel does not accept a nested inductive whose invariant field
mentions `List Ty`.

## What the test run checks

Every module it compiles has to satisfy all of the following, and 121 do: the 116
modules of `SnapshotsPBOPure` and the five pure ones of `SnapshotsMy`.

* It compiles, and **no declaration of it is skipped**: a declaration the translation
  cannot handle is dropped together with everything that calls it, so a skipped one
  means the emitted module is not the Lean module.
* Its JavaScript **loops only with `while` and `for`** (`LakeJsTest/JsShape.lean`). The
  output is read as JavaScript *tokens*, so a keyword inside a string literal — several
  snapshots return the string `"catch"` — is data and not a keyword, and then:
  * none of `function`, `eval`, `arguments`, `new`, `throw`, `undefined`, `do`, `var`,
    `with`, `delete`, `yield`, `await`, `class`, `try`, `catch`, `switch` occurs. No
    function declaration means no function that can name itself other than the `const`
    the module binds; no `new`/`eval` means no code built at run time; no `do` means a
    `do … while` cannot slip past the next check;
  * every `while` and every `for` opens a `while (…)` / `for (…)` statement;
  * there is no self-application `x(x)` — the shape `ω = λx. x x`, the `Y` combinator and
    every untyped fixed point are built from, and the shape `Ty.ne_arrow_self` says no
    `Term` has.
  The check is itself checked: the test run first feeds it an Omega, a `Y` combinator, a
  named recursive `function`, a `do … while`, a `new Function` and a `throw`, each of
  which it must reject, and a `while` loop, a `for` loop and a string containing a
  keyword, each of which it must accept.
* `node --check` parses it as an **ES module** (skipped, with a note, when `node` is not
  on the path). A module is strict, so this catches a declaration bound to a name
  JavaScript reserves and a name bound twice.
* A handful of modules must also contain particular text: a `while` loop where the Lean
  recursion is a tail call, the merged `_mut$…` loop for a mutually tail-recursive
  group, the unboxed instance fields.

And the modules that must be refused are refused, with a message that says why:
`SnapshotsPBOPartial/RecursiveBindingGroup01` and `SnapshotsPBOPure/Html` for a
`partial def`, `SnapshotsMy/IoEntry` and `SnapshotsMy/StdinEntry` for being IO.

## Every declaration gets a name of its own, and one JavaScript will take

`LakeJs.FromLcnf.jsName` is only the *base* name of a declaration: it replaces the
characters JavaScript does not allow in an identifier, so two Lean names can come out
alike, and a Lean declaration can be called `eval`, which a module may not bind
(`SnapshotsPBOPure/RecursionSchemes01` has one, and it is emitted as `eval$`).
`LakeJs.Compile.compileModule` therefore hands out the names itself, before anything is
translated: every name the module binds — a declaration, the `<inst>_<field>` constants
an unboxed instance becomes, its `<inst>$box`, the `_mut$…` of a merged group and every
imported name the code mentions — is taken from one set, and a base already taken gets
`$1`, `$2`, … Two different Lean names are therefore two different JavaScript names, and
none of them is a word JavaScript reserves. The name each declaration was given is
carried in `Ctx'.jsNames` and read with `Ctx'.js`, so the definition and every reference
to it agree.

## The snapshots

These were compiled with the output written beside the source. Where a `.js` file was
already there, the previous one was kept as `<Name>.expected.js`. The other snapshots of
`SnapshotsPBOPure` are compiled and checked by `lake test` in memory, and their `.js`
files are the ones that came with the corpus; running the backend over one of them
(`lake env ./.lake/build/bin/lean-to-js-backend SnapshotsPBOPure/<Name>.lean`) writes
the backend's own output over it.

| Snapshot | What it exercises | Output |
| :--- | :--- | :--- |
| `SnapshotsPBOPure/Tco01` | self tail recursion on `Nat` | one `while` loop |
| `SnapshotsPBOPure/Tco03` | mutual recursion with `termination_by` | one merged loop |
| `SnapshotsPBOPure/Tco04` | mutual recursion carrying proofs | one merged loop |
| `SnapshotsPBOPure/Tco05` | a `let rec` walking an array | a `while` loop |
| `SnapshotsPBOPure/Tco06` | a mutual group driven by fuel | one merged loop |
| `SnapshotsPBOPure/CaseJacobs` | nested constructor patterns | a tag dispatch |
| `SnapshotsPBOPure/CaseLeafTco` | tail recursion under a deep match | a `while` loop |
| `SnapshotsPBOPure/Fusion01`, `Fusion02` | fold and unfold fusion | straight-line code |
| `SnapshotsPBOPure/CaptureDerefRegression01` | captures, unboxing, a mutual tail group | closures and a merged loop |
| `SnapshotsPBOPure/RecursionSchemes01` | recursion schemes (no tail call) | recursive functions |
| `SnapshotsPBOPure/VanLaarhovenTraversals01` | van Laarhoven traversals | closures |
| `SnapshotsMy/HashContainers` | `Std.HashMap`/`HashSet` loops | loops and calls |
| `SnapshotsMy/MutualTail` | mutually tail-recursive groups, of equal and of different arities | two merged loops |
| `SnapshotsMy/StringWalk` | byte-position string walks | `while` loops |
| `SnapshotsMy/UnreachBranch` | branches Lean proved impossible | a dispatch with no fallback |
| `SnapshotsMy/GcdEntry` | `Nat.gcd`, a well-founded recursion | a call of the runtime's `$lean_nat_gcd` |

Refused, as they should be:

| Snapshot | Why |
| :--- | :--- |
| `SnapshotsPBOPartial/RecursiveBindingGroup01` | three `partial def`s, and an `IO` `main` |
| `SnapshotsPBOPure/Html` | its derived `Repr` instance is a `partial def` |
| `SnapshotsMy/IoEntry`, `SnapshotsMy/StdinEntry` | they are IO |

`SnapshotsMy/GcdEntry` used to be refused too, because of its `main : IO Unit`. A `Term`
is a value — an optimiser may reorder, duplicate or drop it — and `IO.println` is not,
so there is nothing for the backend to compile an IO entry point *into*; the `main` of
that snapshot is commented out, and what is left, `Nat.gcd`, `gcd2` and `run`, compiles.

## Known limits

* A call to a library function that the backend has no primitive and no extern for is a
  call of that declaration's own emitted name if it is compiled, and otherwise a call of
  an imported name that the signature records but nothing defines yet; externs print as
  `$lean_…`. There is no runtime prelude supplying `$lean_…` yet, so such a module
  type-checks as JavaScript but does not run until one is provided. Modules that only
  use the primitives of `LakeJs.FromLcnf.primFor` (arithmetic, comparison, string
  concatenation, array indexing and the like) do run: `Tco01`, `Tco06`, `MutualTail` and
  `StringWalk.test4` were checked against `node`.
* A group whose members call one another but never in tail position is left as mutually
  recursive JavaScript functions; merging it into a dispatch loop would not remove any
  stack frame, since the calls are not tail calls in the first place.
* The one Lean type that `Ty` does not describe the shape of is a **type parameter** of
  the enclosing declaration, which is `Ty.typeParam`. That is parametricity and not
  ignorance: no data operation is available at it, so such a value can only be passed
  on, stored and returned. Where the LCNF type is more precise than `Ty` the translation
  reinterprets the term (`LakeJs.FromLcnf.coerce`), which changes nothing in the output.
* Constructor functions (`$Expr$add`) are not emitted; a constructor is built inline
  where it is applied.
* A parameterised declaration is modelled at its instantiation, and a mutual block as a
  `Ty.mutualRecursiveFamily`, so `Option α`, `Except Nat String` and a mutual pair of
  trees all have layouts and all go through the checked `Term.ctor`/`Term.proj`. Two
  cases are still refused rather than modelled: a recursive declaration that occurs
  *inside* another recursive declaration cannot refer back to the outer one (the
  translation reports the name it could not resolve), and an indexed inductive family is
  refused outright.
* An argument slot of a merged dispatch loop that the entering member does not have is
  filled with `0`. It is pure and it is never read, but it is a value the source never
  mentions.
* A Lean function whose recursion is **not** a tail call is emitted as a JavaScript
  function that calls itself. It terminates — the totality gate has established that the
  Lean function does — but it is a recursive call and not a `while` loop, so it uses the
  JavaScript stack. Turning a non-tail recursion into a loop over an explicit stack is
  not part of this iteration. The test run finds those declarations
  (`LakeJsTest.JsShape.recursiveNames`) and prints them as a `note`, so exactly where it
  happens is visible: of the 121 modules it compiles, six have one —
  `CaseJacobs` (`renderExpr`), `InlineReferenceOpIsTag`, `Object01`, `RecursionSchemes01`
  (`cata`/`cataMap`), `VanLaarhovenTraversals01` and `HashContainers` (the association
  lists of `Std.HashMap`). Every other module loops only with `while`.
* `SnapshotsPBOPure/PrimOpNumber02` did not elaborate under this toolchain: its
  `testLt`/`testGt`/`testLe`/`testGe` helpers asked for `DecidableRel` on an `α` with no
  `LT`/`LE` instance in scope. The instance binders were added, which is what lets the
  whole `SnapshotsPBOPure` library build and the snapshot be tested.
* The modules that carried the earlier string-keyed schema machinery are parked beside
  the build as `LakeJs/*.lean_` rather than deleted.
