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

## The configuration: numbers or `BigInt`s

`LakeJs.Config.JsConfig` (`LakeJs/Config.lean`) holds one decision per numeric type:
is it a JavaScript number, or a `BigInt`?  Two presets are named on the command line:

```
lake env ./.lake/build/bin/lean-to-js-backend --config=pbo      SnapshotsPBOPure/PrimOpIntDivConfigurable.lean
#   … -> SnapshotsPBOPure/PrimOpIntDivConfigurable-num.js
lake env ./.lake/build/bin/lean-to-js-backend --config=faithful SnapshotsPBOPure/PrimOpIntDivConfigurable.lean
#   … -> SnapshotsPBOPure/PrimOpIntDivConfigurable-bigint.js
```

* `pbo` — the default — represents `Nat`, `Int`, `USize`, `UInt64`, `Int64` and `ISize`
  as JavaScript numbers: fast, and exact below `2^53`.
* `faithful` represents them as `BigInt`s: exact at every size.

`UInt8/16/32`, `Int8/16/32`, `Float`, `Char`, `String` and `Array` are not configurable,
since a number holds each of them exactly; a module built only out of those has one
output rather than two, which is what `PrimOpIntDivNonConfigurable.lean` is.

The representation reaches the output in three places: the literals, the operator forms
(`a + b` is not `UInt64.add` over numbers *or* over `BigInt`s, but `1n` is not `1`), and
the runtime prelude the module imports — `runtime/lean_runtime.mjs` implements the
externs over numbers and `runtime/lean_runtime_bigint.mjs` over `BigInt`s.  A
configuration that mixes the two would need a prelude that is neither, so it is refused
(`JsConfig.isUniform`), and the test run checks that it is.

A configured output names its configuration, and so does the header of its
`-Expr.txt`.  `scripts/snapshot-files.txt` carries the preset beside the file:

```
SnapshotsPBOPure/PrimOpIntDivConfigurable-num.js pbo
SnapshotsPBOPure/PrimOpIntDivConfigurable-bigint.js faithful
```

The two outputs of `PrimOpIntDivConfigurable.lean` are checked by running them: every
declaration of that module is a `Bool` that says the division the optimiser folded
agrees with the `@[noinline]` division and with the answer written in Lean, so the test
suite beside each output asserts that every `…_shouldBeTrue` export is `true`.

`PrimOpInt01/02/03Configurable` and `PrimOpIntBit01/02Configurable` — the arithmetic,
the comparisons and the bitwise operations of the 64-bit types — are compiled both ways
too, and their outputs are checked against what Lean answers for each export.  Those
answers are Lean's own: `scripts/gen-primop-expectations.py` writes one Lean program per
snapshot, `scripts/regen-primop-expectations.sh` runs them into
`scripts/expectations/<Module>.json`, and `scripts/primop-check.mjs` is what the ten
`*.test.js` files run against it.  Under `faithful` every answer must be Lean's.  Under
`pbo` a number holds an integer exactly only below `2^53`, and these snapshots exceed
that on purpose (`-1 : UInt64` is `2^64 - 1`), so the suite asserts Lean's answer inside
that range and *names* what falls outside it: a count of the answers that do not fit,
and a list of the exports that fit but are computed through one that does not — each of
which is asserted to disagree with Lean, so the list cannot go stale.

`lake test` runs the backend over **every** snapshot of `SnapshotsPBOPure` — the
directory is read as the test runs, so a snapshot added to it is tested without any list
being edited — and over the pure modules of `SnapshotsMy`, and checks each verdict.

## The pipeline

| Step | Where |
| :--- | :--- |
| read the **`saveBase`** LCNF phase out of the `.olean` | `LakeJs/FromLcnf.lean` |
| refuse what must not be compiled | `LakeJs/Totality.lean` |
| translate to the typed `Term` | `LakeJs/FromLcnf.lean`, `LakeJs/Compile.lean` |
| specialise the member tag of a mutual group whose jumps name their target | `LakeJs/Specialise.lean` |
| simplify, inline the calls of inlinable declarations, scalarise loop accumulators, simplify again | `LakeJs/Simp.lean`, `LakeJs/Inline.lean`, `LakeJs/Scalarise.lean` (`LakeJs.Compile.optimise`) |
| print with `MiniAST`, and the terms before the optimiser with `LakeJs/TermPretty.lean` | `LakeJs/EmitJs.lean` |

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

### When the tag is known, it is specialised away

A jump inside the group almost always names the member it goes to, so the tag is a
*compile-time* value and testing it every iteration is waste.  `LakeJs/Specialise.lean`
removes it by **unrolling the cycle**: one member owns the loop, a jump to another member
is replaced by that member's body — its arguments bound in front of it — and the jump
that comes back round to the owner is the one `continue` that remains.  A member that
does not own the loop runs its own body once, and the bodies of the members between it
and the owner, and then *calls* the owner's function, which happens once per entry rather
than once per iteration, so the stack stays constant.

```js
const _spec$testEven = (v0, v1) => {
  let v2 = v0, v3 = v1._1, v4 = v1._2;
  while (true) {
    if (v2 === 0) return { tag: 0, _1: v3, _2: v4 };
    const v5 = v2 - 1, v6 = v4 + 1, v7 = v3 + 2;      // testEven
    if (v5 === 0) return { tag: 0, _1: v6, _2: v7 };
    const v8 = v5 - 1, v9 = v7 + 3, v10 = v6 + 4;     // testOdd, unrolled
    v2 = v8; v3 = v9; v4 = v10;
    continue;
  }
};
export const testEven = _spec$testEven;
export const testOdd = (v0, v1) => { /* one step, then _spec$testEven(…) */ };
```

The conditions are checked in order, and every one of them is conservative: each
`Body.cont` of each member must supply a **literal** tag; the successor map that gives
must be a **single cycle** through all the members, which is what makes the unrolling
terminate and puts each member's body on a path once; the cycle must be short
(`maxCycleLength`, 3) and the resulting function under a node budget (`sizeBudget`),
since a member with two jumps duplicates whatever follows it.  Anything else keeps the
dispatch loop — `SnapshotsPBOPure/Tco03`, whose `go` jumps to itself *and* to `k`, is
such a group and still prints `_mut$go`.

The rebuild is type-preserving by construction: a body is moved into its new context by
the substitution of `LakeJs/Scalarise.lean`, which answers `none` rather than producing
anything ill-typed, so a specialised group is a `Term` of the same signature or it is not
produced at all.  The two shapes get two names (`_mut$…`, `_spec$…`) and a group is
emitted as exactly one of them.

## A join point with several jumps is a local function

LCNF marks the shared continuation of a `match` as a **join point**.  A join point with
one jump is inlined at it — that is what join points are for — but one with *several* was
inlined at every one of them, so its body was emitted once per jump.  It is now bound as
a local function instead, and each jump is a call of it:

```js
const v4 = (v4) => { …the shared continuation… };
const v5 = 1024 <= v1;
if (v5) { return v4(1); } else { return v4(2); }
```

Nothing was added to the term language for this: a local function is `Term.letE` of a
`Term.lamN`, and a jump is `Term.apN` of the variable it bound, both of which were there
already.

Three conditions, all of them conservative, decide it (`LakeJs/FromLcnf.lean`,
`transBody`):

* the block must hold **at least two** jumps to the join point (`jumpCount`), since one
  jump is cheaper inlined;
* the join-point body must be **big enough** to be worth a closure and a name
  (`codeSize`, `jpShareSize`), since duplicating two operations costs less than
  allocating a function;
* the body must **not call the declaration being compiled**, nor a member of its mutual
  group, directly or through another join point it jumps to (`mentionsLoopCall`).  Such a
  call is the `continue` of the enclosing loop, and a closure cannot continue a loop it
  is not in: making it a function would turn the loop back into recursion.  The third
  condition is exactly what keeps `SnapshotsPBOPure/CaseLeafTco` a loop — its stack test
  at depth 1 000 000 fails without it.

`SnapshotsPBOPure/VanLaarhovenTraversals01` is the case in the corpus: its derived
`Repr` instance shares the continuation of the precedence test, and the module is 17
lines shorter for it.

## The optimiser is also a relation

`LakeJs/Simp.lean` and `LakeJs/Inline.lean` are the optimiser as *functions*, which is
what the backend runs.  The same rules are written down a second time in
`LakeJs/Reduce.lean` as an inductive relation, `Step tbl`, with one constructor per rule —
the projection of a constructor application, the dead `let`, the copy, the `let` read
straight back, the cast of a bound variable, eta-contraction, the guarded `Nat`
predecessor, and the inliner's `delta` and `deltaLit` — and one per *position* a rewrite
may be made in, which makes it a congruence.  `Chain (Step tbl)`, written `—↠[tbl]`, is
its reflexive-transitive closure.

`tbl` is the table of declarations a call of which may be inlined
(`LakeJs.Inline.Table`), and only `delta` and `deltaLit` read it: unfolding a call is
justified by the *definition* of the callee, and a `Sig` records only names and types, so
the definitions have to be given.

The relation and the functions are tied together, not merely kept side by side:

```lean
theorem Term.simp_chain (t : Term Sg Γ τ) : t —↠[tbl] Term.simp t
theorem Term.simpAll_chain (t : Term Sg Γ τ) : t —↠[tbl] Term.simpAll t
theorem Term.inlineCalls_chain (t : Term Sg Γ τ) :
    t —↠[tbl] LakeJs.Inline.Term.inlineCalls tbl t
theorem Term.simp_inline_simp_chain (t : Term Sg Γ τ) :
    t —↠[tbl] Term.simpAll (LakeJs.Inline.Term.inlineCalls tbl (Term.simpAll t))
```

so the function is one *strategy* for the rules — apply each of them bottom up, once —
rather than a separate optimiser that has to be kept in step with them by hand, and a
property proved of `Step` is a property of what the backend emits.  Each binding form's
rules live in their own function of the already-simplified parts (`simpProj`, `simpIte`,
`simpLetE`, `simpLamN`, `simpLetB`, `simpIteB`, and the inliner's `inlineApN` and
`inlineGlobal`), each with its own lemma.

What this needed, and what it does not yet cover:

* the simplifier and the renaming it uses are **no longer `partial`**: they are
  structural recursions, so their equations exist and their rules can be reasoned about.
  Two functions stay `partial` on purpose, because they genuinely are not structural:
  `LakeJs.Scalarise.scalariseLoop` (splitting a slot makes the loop wider, and the pass
  starts again) and `LakeJs.Specialise.specBody` (the unrolling is bounded by fuel);
* the **scalariser** is in the relation too — `letCtorInline` and `scalariseSlot` are its
  two rules, `Term.scalarise_chain` is its lemma, and `LakeJs.Compile.optimise_chain`
  (in `LakeJs/OptimiseChain.lean`) puts the whole pipeline together, so every term the
  backend prints is reachable by the rules from the term the translation produced, which
  is the one `<Module>-Expr.txt` holds;
* `LakeJs/Specialise.lean` is not: it takes the bodies of a whole *group* of
  declarations and builds one loop the members enter, so what it relates is a module
  rather than a term;
* **the relation is not confluent**, and `LakeJs/ReduceConfluence.lean` proves it.  A
  wrapper around an inlinable declaration, `fun (x0, x1) => add2(x0, x1)`, rewrites in
  one step to `add2` (eta) and in one step to `fun (x0, x1) => x0 + x1` (delta, the
  inliner), and the second of those eta-contracts to the extern `lean_nat_add`.  Both
  results are normal forms — nothing rewrites a reference whose body is not a literal,
  and nothing rewrites an extern — and they are different terms, so the two rewrites
  have no common reduct (`cfCall_not_joinable`, `step_not_locallyConfluent`,
  `step_not_confluent`).  They denote the same function, so the emitted module is
  correct whichever it prints; what fails is that the answer is independent of the order
  the rules fire in, which is why the backend fixes an order (the inliner, then the
  bottom-up sweep) rather than chasing the relation to a normal form.

`LakeJs/SimpFixpoint.lean` settles a third question of the same kind: **one sweep of the
simplifier is not idempotent** (`simp_not_idempotent`).  In
`let c = 0; if (n === c) then 0 else n - 1` the copy rule of the first sweep puts the
literal in the test, and only then is the test a guard the second sweep sharpens the
`else` branch by — which is why `Term.simpAll` is two sweeps.

The other question that comes before confluence is settled in `LakeJs/ReduceCycle.lean`:
**the relation does not terminate.**  `iteGuard` rewrites the `else` branch of a test
against `0` with `Term.assumeNonZero`, which hands the branch back unchanged when there
is no truncating subtraction in it to sharpen, so

```js
if (n === 0) { return 0; } else { return 0; }
```

steps to itself (`exTerm_step_self`), and `Step` is therefore not well-founded
(`step_not_wellFounded`).  That is a fact about the relation, not about the function:
the simplifier applies each rule once per bottom-up sweep and always stops.  What it
rules out is reasoning about `Step` through "the normal form of a term", and proving
anything about it by induction on a reduction order.

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
declarations (including the unboxed instance fields below and the `_mut$…`/`_spec$…` loops)
and every imported constant the code mentions — and translates all declarations against
that one fixed `Sg`.

## Every operation is a Lean function, and carries its type

An operation of the language is a function Lean implements with `@[extern]`, named by the
catalogue `LakeJs/Externs.lean`: an inductive `Externs : List Ty → Ty → Type` with one
constructor per extern, indexed by the list of its argument types and by its result type.
`Term.extern : Externs σs τ → Term Sg Γ (.fn σs τ)` puts it in the language, and
`Term.apN` is the only way to call it, so an extern applied to the wrong number of
arguments, or to arguments of the wrong type, is not a `Term`. Two generated files carry
the metadata (`python3 scripts/gen-externs-meta.py` rebuilds both; do not edit them by
hand):

* `LakeJs/ExternsMeta.lean` — `Externs.cName` and `Externs.arity` for all 582
  constructors;
* `LakeJs/ExternTable.lean` — `externTable`, a lookup from the Lean name to the
  constructor, and `externFor?`.

`LakeJs/FromLcnf.lean`’s `directFor` is the table of the Lean declarations a call of
which becomes the operation itself: `Nat.add` is `lean_nat_add`, `Array.size` is
`lean_array_get_size`, and so on. Whether an extern *prints* as a call of the runtime
function or as a JavaScript operator is then a decision of the printer alone
(`LakeJs/EmitJs.lean`, `inlineExtern?`): the arithmetic, the comparisons and a handful of
string and array operations have an operator form and print as `a + b`, `a === b`,
`a.length`, `[...a, x]`; everything else prints as a call, and an extern that prints as an
operator is never imported from the runtime prelude.

```js
const v12 = $lean_uint64_of_nat(v6);        // no operator form: a call
const v15 = $lean_uint64_xor(v12, v14);
const v16 = v0 + v1;                        // lean_nat_add has one
```

The table is deliberately small, because a row is only allowed in it where the operator
is the Lean function **on every input the representation can hold**:

* the fixed-width arithmetic *wraps* and the JavaScript operator does not, so
  `UInt8.add`, `UInt32.mul`, `USize.sub` and the rest are calls of the runtime function
  that wraps, at either representation;
* a division or a remainder by zero is `0` (and `n % 0` is `n`) in Lean, and `NaN`,
  `Infinity` or a thrown `RangeError` in JavaScript, so `Nat./`, `Int./` and `Nat.%`
  print as an operator only under a guard — `b !== 0 ? Math.trunc(a / b) : 0` — and only
  where the divisor is a name or a literal, so that the guard costs nothing and repeats
  nothing.  A literal divisor settles the guard at compile time: `a / 2` needs none, and
  `a / 0` is the literal `0`.  Where the divisor is a computation, the extern is called
  (`LakeJs/EmitJs.lean`, `divGuard`).

An extern that is *not* saturated prints as a wrapper over the same thing —
`(v0, v1) => $lean_nat_gcd(v0, v1)`, `(v0, v1) => v0 === v1` — so the arity of the
emitted call always matches the arity of the runtime function.

What is left over is the handful of operations that are **not** Lean functions, and so
have no entry in the catalogue: `JsOp` (in `LakeJs/Expr.lean`), applied by
`Term.jsOp : JsOp σs τ → Spine Sg Γ σs → Term Sg Γ τ`, and indexed by its types in the
same way. There are seven of them: reading a value at another type (`cast`, which prints
as its argument), `Bool.and`, `Bool.or` and `Bool.not` and the equality of two `Bool`s or
two `Char`s — Lean functions, but not `@[extern]` ones, so no runtime function implements
them — the untruncated subtraction of two `Nat`s, which the optimiser puts where a guard
shows `Nat.sub` cannot truncate, and `String(a)`. Any other standard library function the
backend wants to optimise is added as an `Externs` constructor — never as a string.

Which rows of the catalogue can never appear in a `Term` is a question with a mechanical
answer: `lake env lean scripts/check-extern-names.lean` reports the rows whose Lean name
this toolchain does not have, and those are commented out in `LakeJs/Externs.lean`, with
the row kept as a record for a version of Lean that does have the declaration.

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
`[[], [α, list α]]`; `Unit` is `.enum 1`; `Ordering` is `.enum 3` (the constructor count is positive by construction); a `Decidable` is the
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
change what a term means to the type system. It does the following:

* `let x = e; x` ⟶ `e`;
* `let x = e; cast x` ⟶ `cast e`;
* `let x = e; b` ⟶ `b`, when `b` never reads `x` — the body is rebuilt in the smaller
  context (`Term.strengthen?`), and that rebuilding *is* the side condition;
* `let x = c; b` ⟶ `b[c/x]`, when `c` is a *copy*: a variable, a literal, a global, an
  extern, or one of those read at another type. Each is a value, so no work is
  duplicated, and the closed ones travel under any number of binders unchanged;
* `e._j` ⟶ the `j`-th argument, when `e` is a constructor application built right there
  (`projOfCtor?`). The arguments not read are dropped, which is sound because every
  `Term` is a pure, total value;
* `Math.max(0, n - 1)` ⟶ `n - 1` in the branch guarded by a test of `n` against `0`
  (`nonZeroGuard?` / `Term.assumeNonZero`): `Nat` subtraction truncates only when the
  subtrahend exceeds the value, which the guard rules out. The guard is recognised both
  written inline and bound to a name first, and through the reinterpretation by which a
  `Decidable` is read as the `Bool` it decides;
* eta: `(v0, …, vn) => f(v0, …, vn)` ⟶ `f`, when `f` is a global or an extern, seeing
  through one `cast` layer.

The eta rule is what turns an unboxed one-field instance into `const
instToStringExpr_toString = renderExpr;`.

## Inlining a call

`@[inline] def foo a b := …` followed by `def bar := foo 1 2` should not leave a call in
the emitted module, and it does not: `LakeJs/Inline.lean` rewrites a saturated call of a
top-level declaration into that declaration's body, with the arguments of the call in
place of its parameters.

A declaration the backend has already translated is a **closed** term
`Term Sg [] (.fn params ret)`, so a saturated call of it is
`Term.apN (.global r) args`, and the body of the declaration is a term whose context is
exactly the parameters (`params.reverse ++ []`).  Inlining the call is therefore the body
read through the map that sends parameter *i* to argument *i* — a `Ren` of
`LakeJs/Rename.lean`, applied with `Term.rename?`.  Two things follow:

* **nothing is duplicated.**  A `Ren` carries a variable or a value — a literal, a global,
  an extern, or one of those read at another type — and nothing else, so an argument that
  is a computation is not substituted and the call is left alone.  The terms the
  translation produces are in administrative normal form, so the arguments of a call are
  variables and literals in practice, and the rule fires;
* **nothing can go wrong in the types.**  A renaming maps a variable to a target at its
  own type and `Term.rename?` preserves the type, so the inlined body is a term of the
  type the call had.  A wrong arity or a mismatched argument type is not expressible: the
  spine of the call has the parameter types of the declaration by construction.

Which declarations go into the table (`LakeJs.Compile.inlinableDecl`): the ones Lean marks
`@[inline]` or `@[macro_inline]`, and the ones Lean says nothing about whose body is small
(`Term.nodeCount`) and straight-line (`hasControlFlowTerm` — a branch copied into a
position that is an expression would have to be printed inside an arrow function, which is
bigger than the call it replaced).  Never a declaration marked `@[noinline]`, never a
member of a merged mutually-recursive group, never an unboxed instance, and never one
whose body still mentions its own name — that last condition is what makes the pass
terminate.

The module is translated **callees first** (`LakeJs.Compile.topoOrder`), so the body a
call site inlines is the callee's finished, already optimised term; the declarations are
still *printed* in the order they always were.  A declaration nothing exports and nothing
calls any more is then not printed at all (`dropUnusedDecls`), which is what a private
`@[inline]` helper becomes once every call site has its own copy.

Lean's own `saveBase` phase already inlines most `@[inline]` declarations before the
backend sees them.  What this pass adds is the cases it cannot: a recursive `@[inline]`
declaration, which Lean will not unfold and which the backend has already turned into a
loop (`SnapshotsPBOPure/Fusion02.lean`), and a small declaration nobody marked
(`SnapshotsMy/HashContainers.lean`).  `SnapshotsMy/InlineDemo.lean` is the module that
shows all four answers side by side.

## The terms before the optimiser: `<Module>-Expr.txt`

The JavaScript is what the backend is for, but it is not what the optimiser works on, and
a rewrite that fired and a rewrite that did not can print alike.  The driver therefore
translates every declaration twice — once through `LakeJs.Compile.optimised` and once
through `LakeJs.Compile.unoptimised` — and writes the second rendering beside the `.js`
file:

```
lake env ./.lake/build/bin/lean-to-js-backend SnapshotsMy/InlineDemo.lean
#   SnapshotsMy/InlineDemo.lean -> SnapshotsMy/InlineDemo.js, SnapshotsMy/InlineDemo-Expr.txt
```

`LakeJs/TermPretty.lean` prints the term as an indented s-expression: every binding form
names the types it binds, a variable prints as its de Bruijn index and its type, a global
prints as the name the signature gives it and an extern as the runtime name it is called
by.  `--no-expr` leaves the file alone.

## Scalarising a loop accumulator

A loop variable whose type is a record costs an allocation per iteration when the body
takes it apart and builds a new one. `LakeJs/Scalarise.lean` gives such a loop **one slot
per field**, so the fields travel round the loop as scalars and the object is built only
where the loop answers:

```js
const _spec$testEven = (v0, v1) => {
  let v2 = v0, v3 = v1._1, v4 = v1._2;
  while (true) {
    if (v2 === 0) { return { tag: 0, _1: v3, _2: v4 }; }
    const v5 = v2 - 1, v6 = v4 + 1, v7 = v3 + 2;
    …
  }
};
```

A field read counts for nothing when the pass decides whether to move a constructor
application to its uses (`occCount`): a projection of a value built right there is the
field itself, so substituting into it builds no object.  That is what leaves a value
handed from one unrolled member to the next as its fields rather than as an object.

It is two steps, each a function `Term Sg Γ τ → Term Sg Γ τ`. First, a constructor
application bound to a name that nothing needs *whole* — every use of it is a field read
— is moved to its use sites, where the projection rule above turns each into the field
itself; the same happens when its one use is where the block ends, which is the jump
round the loop. Then the slot itself is split: the loop variable is **substituted** by
the constructor applied to the new field slots, which is the very same value, and the
jump's argument for that slot becomes one projection per field — and both of those the
projection rule collapses again.

The pass leaves a loop alone when no jump rebuilds the value, and when the body needs it
whole anywhere but in an answer: scalarising then would only move the allocation, which
is the re-boxing trap. `lake test` asserts that the loop body of
`CaptureDerefRegression01` builds no object, and `scripts/bench-generated.mjs` times the
generated module against the hand-written shape the plan calls the expected output
(23 ms against 12 ms, where it was 98 ms before this pass).

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

## The declarations are printed in dependency order

A `const` is not hoisted in JavaScript, so a declaration whose value is *computed as the
module loads* — a Lean constant rather than a function — throws a `ReferenceError` if it
runs before a declaration it calls has been initialised.  `LakeJs.Compile.orderDecls`
therefore prints a declaration after everything it mentions.  Only a cycle cannot be
ordered, and the declarations of one keep the order they had: a cycle is made of
functions, which are read when they are called, by which time the module has loaded.

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
| `SnapshotsPBOPure/Tco04` | mutual recursion carrying proofs | one specialised loop |
| `SnapshotsPBOPure/Tco05` | a `let rec` walking an array | a `while` loop |
| `SnapshotsPBOPure/Tco06` | a mutual group driven by fuel | one specialised loop |
| `SnapshotsPBOPure/CaseJacobs` | nested constructor patterns | a tag dispatch |
| `SnapshotsPBOPure/CaseLeafTco` | tail recursion under a deep match | a `while` loop |
| `SnapshotsPBOPure/Fusion01`, `Fusion02` | fold and unfold fusion | straight-line code |
| `SnapshotsPBOPure/CaptureDerefRegression01` | captures, unboxing, a mutual tail group | closures and a specialised loop |
| `SnapshotsPBOPure/RecursionSchemes01` | recursion schemes (no tail call) | recursive functions |
| `SnapshotsPBOPure/VanLaarhovenTraversals01` | van Laarhoven traversals | closures |
| `SnapshotsMy/HashContainers` | `Std.HashMap`/`HashSet` loops | loops and calls |
| `SnapshotsMy/MutualTail` | mutually tail-recursive groups, of equal and of different arities | two specialised loops (a 2-cycle and a 3-cycle) |
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
  left as it is by a jump inside the group — the member never reads it, and a slot
  assigned to itself is not printed at all — but the wrapper that *enters* the loop from
  outside still fills it with `0`. It is pure and it is never read, but it is a value the
  source never mentions.
* Where two members of a merged group disagree on the type of a slot, the slot is typed
  `Ty.typeParam` and each member reads it at its own type. Nothing in the corpus does
  this, and no value is inserted into the output either way.
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
* A function *value* of a Lean type `A → B → C` is emitted with the backend's uncurried
  calling convention, as a two-parameter arrow. Monomorphic code on both sides agrees on
  that, but a **polymorphic** consumer — one whose parameter has the type of a type
  parameter, such as the `f` of a `Functor.map` — applies its argument one argument at a
  time, and so needs the curried form. Where such a value crosses into polymorphic code
  the two conventions disagree. The only place in the corpus where that happens is
  `VanLaarhovenTraversals01` (`Fun.App <$> k a <*> k b`), and nothing there can be run:
  `Fun`'s two constructors are both recursive, so the type has no closed value at all
  (`Fun → False` is provable in Lean), which is recorded in
  `SnapshotsPBOPure/VanLaarhovenTraversals01.test.js`.

## The tests of the generated JavaScript

Every module listed in `scripts/snapshot-files.txt` has a `*.test.js` beside it, written
against `node:test` and `node:assert/strict`: it imports the generated module and checks
its exported functions against the answers Lean itself gives for the same arguments (the
expectations were read off `#eval`), against a reference implementation of the same
pipeline where one is natural, and — for the modules the backend compiles to a loop —
against an input large enough that a recursive call would exhaust the stack.

`scripts/run_snapshots_nodejs_dot_tests` runs all of them. It first checks that every
listed module exists, loads as an ES module and has a test suite beside it, then runs
`node --test Snapshots*/*.test.js`. `scripts/regen-snapshots.sh` regenerates the `.js`
files first if the backend has changed.

Two defects turned up this way, both fixed:

* **A partially applied declaration was emitted as a call.** A declaration is emitted with
  one JavaScript parameter for each of its run-time parameters, so a call that gives fewer
  arguments than that is not a call but the function that takes the rest. The signature
  records the declaration at its full arity, and a use at another type used to be read
  through a `JsOp.cast`, which prints as its argument — so `Unfold.step` of
  `Fusion02.filterU` was emitted as `filterMapStep(v1, v2)`, a call of a three-parameter
  function with two arguments, and answered with a value where a function was wanted.
  `LakeJs.FromLcnf.transConst` now eta-expands such a call: it reads the arguments again
  under the parameters it adds — sound because a variable is named by its depth, and a
  depth does not move when the context grows on top — and emits
  `(v4) => filterMapStep(v1, v2, v4)`. `RecursionSchemes01.instFunctorExprF_mapConst` was
  the other case, through `Function.const`.
* **`Function_const` in the runtime was curried**, `(a) => (_b) => a`, while the calling
  convention for an imported declaration is uncurried; the mismatch was invisible only
  because the under-applied call happened to match it. It is now `(a, _b) => a`.

The suite also corrected one expectation that came with the corpus: `Tco04.test1 3` is
`2`, not `1`, because the walk lands on `test2`'s own base case. Lean agrees.
