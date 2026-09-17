# Where `TODO.md` stands

One entry per item of `TODO.md`, with what was built and how it is checked.  The whole
project builds (`lake build`), `lake test` reports *all tests passed (123 modules
compiled, 4 refused)*, the Node suites under `scripts/run_snapshots_nodejs_dot_tests`
pass (1 284 tests, 0 failures), and no `sorry` remains in `LakeJs/`.

| # | Item | State |
| :--- | :--- | :--- |
| 1 | `enum (nOfConstructors) (shift)` uniting enums with `Ordering` | **done** |
| 2 | LCNF join points made part of the term language, for optimisation | **done** (see below) |
| 3a | `export const …` rather than a trailing `export { … }` | **done** |
| 3b | a `*.test.js` per emitted module, and a script that runs them | **done** |
| 4 | no unused bound variable in the output | **done**: `USAGE_INDEX_ASSESSMENT.md`, the dead-`let` rule, and the corpus-wide check in the test run |
| 5 | the names of a `Sig` are unique | **done**: `Sig.namesUnique`, checked before a module is translated |
| 6a | `Lit` indexed by `LeanPrimTy`, floats settled by `float_decide` | **done** |
| 6b | `JsPrim` replaced by the `Externs` catalogue | **done** (see below) |
| 6c | the configurable output: `<Module>-num.js` and `<Module>-bigint.js` | **done** (see below) |
| 7 | loop performance, per `MUTUAL_LOOP_PERF.md` | **done**: P1–P6 landed, P7 asserted |
| 8 | the optimiser as an inductive `Prop` relation | **done for the simplifier, the inliner and the scalariser**; the Church-Rosser question is answered — the relation is *not* confluent (`LakeJs/ReduceConfluence.lean`) — and `LakeJs/Specialise.lean` relates modules rather than terms |

## Item 2 — join points

A join point with **several** jumps used to be inlined at each of them, so its body was
emitted once per jump.  It is now bound as a *local function* and each jump is a call of
it.  Nothing was added to the term language: a local function is `Term.letE` of a
`Term.lamN`, and a jump is `Term.apN` of the variable it bound.

Three conservative conditions (`LakeJs/FromLcnf.lean`, `transBody`): at least two jumps
(`jumpCount`); a body big enough to be worth a closure (`codeSize`, `jpShareSize`); and
no call to the declaration being compiled or to a member of its mutual group, directly or
through another join point (`mentionsLoopCall`) — such a call is the `continue` of the
enclosing loop, which a closure cannot do.  `SnapshotsPBOPure/VanLaarhovenTraversals01`
is the case in the corpus and is 17 lines shorter; `lake test` asserts the shared call,
and the stack tests still pass at depth 1 000 000, which the third condition protects.

## Item 7 — P5, the member tag

A mutually tail-recursive group whose jumps name their target no longer carries a tag and
no longer tests it: the cycle is unrolled into one loop that one member owns, and the
other members enter it (`LakeJs/Specialise.lean`).  `CaptureDerefRegression01`, `Tco04`,
`Tco06` and both groups of `MutualTail` are now `_spec$…`; `Tco03`, whose `go` jumps both
to itself and to `k`, keeps the merged `_mut$go` dispatch loop, which stays the general
case.  Measured on `scripts/bench-generated.mjs`: 19 ms, against 23 ms for the merged
loop, 251 ms for the unoptimised merge and 13 ms for the hand-written shape the plan
calls the expected output.

Two bugs in the scalariser were found and fixed while doing it: a field read `x._j` was
counted as a use of the *object* when `x` was some other variable, which stopped the
accumulator of a specialised loop from being scalarised at all, and a constructor
application whose only whole uses are where the block ends is now moved to its uses even
when it is also read field-wise.  `SnapshotsMy/StringWalk` gained a scalarised
accumulator from the first fix, and `lake test` now asserts it.

## Item 8 — the optimiser as a relation

`LakeJs/Reduce.lean` writes the optimiser's rules down as an inductive relation `Step`
(one constructor per rule, one per position a rewrite may be made in) with its
reflexive-transitive closure `Chain`, written `—↠`, and proves

```lean
theorem Term.simp_chain (t : Term Sg Γ τ) : t —↠ Term.simp t
theorem Term.simpAll_chain (t : Term Sg Γ τ) : t —↠ Term.simpAll t
```

so the function the backend runs is one *strategy* for the rules rather than a second
optimiser kept in step by hand.  This needed the simplifier and the renaming it uses to
stop being `partial`, which they have: they are structural recursions, so their equations
exist and their rules can be reasoned about.

The scalarising pass is covered as well — see *Item 8 — the scalariser, and the whole
pipeline* below.  What is not: no confluence (Church-Rosser) claim is made, since the
guard rules overlap with the rules that rewrite the test they read.  The relation is what
makes such a question statable in the first place.

## Item 6b — `JsPrim` replaced by the catalogue

`JsPrim` is gone.  Every operation of the language that *is* a Lean function is now
`Term.extern` of a row of `LakeJs/Externs.lean`, applied with `Term.apN`:
`LakeJs/FromLcnf.lean`’s `directFor` maps `Nat.add` to `lean_nat_add`, `Array.size` to
`lean_array_get_size`, `Float.div` to `lean_float_div`, and so on for the arithmetic, the
comparisons, the string and the array operations.  Nothing is typed `τ → τ → Bool` for an
arbitrary `τ` any more: each row carries the one type Lean gives that function.

Whether such a call *prints* as a call of the runtime function or as a JavaScript operator
is now a decision of the printer alone: `LakeJs/EmitJs.lean`’s `inlineExtern?` gives the
operator form of the externs that have one, `externCall?` uses it where the call is
saturated and `externValue` where the extern is a value, and an extern with an operator
form is never imported from the prelude.  The table is deliberately conservative: an
extern is in it only where the JavaScript operator agrees with Lean on every input the
representation can hold, which is why `lean_string_dec_lt` and the wrapping fixed-width
arithmetic are absent.

Three things came out of doing it:

* the `Int` rows of the catalogue were typed `.int64`; they are `Ty.int` now, which is the
  type the translation gives a Lean `Int`, and `Int.toNat` has a row of its own
  (`lean_int_to_nat`, printed `Math.max(0, a)`) rather than being a reinterpretation that
  kept a negative number;
* `Float.div` used to print as `Math.trunc(a / b)`, because the old `JsPrim.div` was one
  operation for every numeric type; the catalogue distinguishes `lean_float_div` from
  `lean_nat_div`, so it prints as `a / b`;
* `Array.mkEmpty n` and `String.append` are now recognised where they were not, so
  `Array_mkEmpty(0)` is `[]` and `$lean_string_append(a, b)` is `a + b` in the corpus.

What is left over is `JsOp` — seven operations that are not Lean functions at all: the
reinterpretation of a value at another type, `Bool.and`/`Bool.or`/`Bool.not` and the
equality of two `Bool`s or two `Char`s (Lean functions, but not `@[extern]` ones), the
untruncated `Nat` subtraction the optimiser introduces under a guard, and `String(a)`.
Each is monomorphic and documented where it stands.

The parenthetical of the item — *make a list of the `lean_xxx` externs which can never
appear in a `Term`* — is answered mechanically by
`lake env lean scripts/check-extern-names.lean`: it reports the rows whose Lean name this
toolchain does not have (twelve of them, `isScalarObj` and `String.compare` among them)
and the rows whose declaration has an `IO` type (none).  Those twelve are commented out in
the catalogue, each with the reason, so the row is kept as a record for a version of Lean
that does have the declaration.

## Item 7 — P6, one slot per type

`LakeJs/Compile.lean`’s `groupSlotAlloc` lays the parameters of the members of a merged
group out over the argument slots of its loop, sharing a slot between two members only
where they *agree* on its type; a parameter whose type no free slot has gets a slot of its
own.  No slot is widened to `Ty.typeParam` any more, and a group whose members agree
pointwise — every group in the corpus — keeps exactly the layout it had.  The value a
wrapper passes for a slot its member does not use is the empty value of *that slot’s* type
(`""`, `[]`, `false`), so the slot still holds values of one JavaScript type.
`SnapshotsMy/MutualSlots.lean` is the new snapshot that exercises the disagreeing case.

## Item 8 — the scalariser, and the whole pipeline

The scalariser turned out to be a rewrite of a single `Term` after all: splitting a loop
slot into its fields changes the slots the loop carries, and the slots of a loop are not
part of the type of the term the loop is.  `Step` therefore has two more rules —
`letCtorInline`, the constructor application that goes to the field reads, and
`scalariseSlot` — and `Term.scalarise_chain` proves that the pass only produces terms
reachable by them.  For that the pass had to stop being `partial`: its sweep now counts
its splits (`Scalarise.splitBudget`), so it has equations, and its two `let` rules are
named functions of the already-rewritten parts.

`LakeJs/OptimiseChain.lean` then puts the three passes together:

```lean
theorem LakeJs.Compile.optimise_chain (tbl) (t) : t —↠[tbl] LakeJs.Compile.optimise tbl t
```

— every term the backend prints is reachable, by the rules of the relation, from the term
the translation produced, which is the one `<Module>-Expr.txt` holds.

## Item 6c — one module, two representations

The last paragraph of item 6 asks for `PrimOpIntDivConfigurable.lean` to be compiled to
`PrimOpIntDivConfigurable-bigint.js` under `presetFaithful` and to
`PrimOpIntDivConfigurable-num.js` under `presetPBO`, for
`PrimOpIntDivNonConfigurable.lean` to have the one output that uses no `BigInt`, and for
each of them to be tested by checking that the `…_shouldBeTrue` exports are `true`.  All
three outputs are generated, and all three test suites pass (56 assertions).

* `lean-to-js-backend --config=pbo|faithful` picks the preset, and names the output
  after it (`--out=<file>` overrides); `LakeJs.Compile.compileModule` takes the
  configuration and refuses one that mixes numbers and `BigInt`s, since the runtime
  prelude is one module per representation.
* `runtime/lean_runtime_bigint.mjs` is new: the prelude over `BigInt`s.  What does not
  depend on how a `Nat` is represented is re-exported from `runtime/lean_runtime.mjs`
  rather than written twice.
* `scripts/snapshot-files.txt` carries the preset beside a configured file, and
  `scripts/regen-snapshots.sh` reads it.  `lake test` compiles the two modules under
  both presets and checks that the `BigInt` literals and the `BigInt` prelude appear in
  exactly one of them, and that a mixed configuration is refused.

Two real bugs in the backend came out of running the results, both fixed:

* **the declarations were printed caller-first**, which is fine for a function but not
  for a Lean constant, whose value is computed as the module loads: every one of these
  three outputs threw a `ReferenceError` on load.  `LakeJs.Compile.orderDecls` now
  prints a declaration after everything it mentions.
* **four operator forms did not agree with Lean**: `Nat./`, `Int./` and `Nat.%` gave
  `NaN` where Lean gives `0` (or, for the remainder, the dividend), and the fixed-width
  `add`/`sub`/`mul` did not wrap.  The divisions now print as an operator only under a
  `b !== 0` guard, and only where the divisor is a name or a literal; the wrapping
  arithmetic prints as a call of a runtime function that wraps.  A fifth check was added
  to the Node run for it: `scripts/check-prelude-imports.mjs` asserts that every name a
  generated module imports is one the prelude exports.

## What is left

* **Confluence — settled, in the negative.**  `LakeJs/ReduceConfluence.lean` exhibits a
  critical pair that does not join, so `Step` is **not** Church-Rosser and not even
  locally confluent (`step_not_locallyConfluent`, `step_not_confluent`,
  `exists_not_confluent`).  The pair is the wrapper `fun (x0, x1) => add2(x0, x1)`
  around an inlinable declaration: *eta* contracts it to `add2`, *delta* (the inliner)
  expands it to `fun (x0, x1) => x0 + x1`, which *eta* then contracts to the extern
  `lean_nat_add`; both results are normal forms and they are different terms.  That is
  not a defect of the emitted code — the two normal forms are the same function — but it
  does mean that the optimiser's answer depends on the order its rules fire in, which is
  why the backend fixes an order rather than chasing the relation.  (The overlaps the
  guard rules create, which this entry used to point at, are therefore no longer the
  place one has to look.)

  A third question of the same kind is answered in `LakeJs/SimpFixpoint.lean`:
  **one sweep of the simplifier is not idempotent** (`simp_not_idempotent`).  In
  `let c = 0; if (n === c) then 0 else n - 1` the copy rule of the first sweep puts the
  literal in the test, and only then is the test a guard the second sweep can sharpen
  the `else` branch by — so the number of sweeps `Term.simpAll` runs is part of what the
  backend computes rather than an accident of it.

  The other question that comes before it was settled, in `LakeJs/ReduceCycle.lean`:
  **`Step` does not terminate**.  `iteGuard` rewrites the `else` branch of a test
  against `0` with `Term.assumeNonZero`, which gives the branch back unchanged when it
  holds no truncating subtraction, so `if (n === 0) then 0 else 0` steps *to itself*
  (`exTerm_step_self`) and the relation is not well-founded
  (`step_not_wellFounded`).  Nothing there is a defect of the simplifier — it applies
  each rule once per sweep and always stops — but it does mean that "the normal form of
  a term" is the wrong phrase to reach for when reasoning about `Step`, and that a
  confluence proof cannot go by induction on a reduction order.
* **`LakeJs/Specialise.lean`.**  It does not rewrite one term into another: it takes the
  bodies of a whole *group* of declarations and builds one loop that the members enter,
  so what it relates is a module rather than a term, and it is outside `Step` for that
  reason rather than for a typing one.

## Item 6c — the other configurable snapshots

`PrimOpInt01/02/03Configurable` and `PrimOpIntBit01/02Configurable` export plain
functions and constants rather than the self-checking `…_shouldBeTrue` ones of
`PrimOpIntDivConfigurable`, so testing their two outputs means comparing against answers
computed in Lean.  All ten outputs are now generated and tested, and the hand-written
reference outputs that stood in their place were kept as `*-num.expected.js` and
`*-bigint.expected.js`.

* **The answers are Lean's own.**  `scripts/gen-primop-expectations.py` writes one Lean
  program per snapshot (the snapshots declare the same names, so they cannot be imported
  together); `scripts/regen-primop-expectations.sh` runs them and writes
  `scripts/expectations/<Module>.json`, which holds what Lean answers for every export —
  a constant as it stands, a function at a fixed list of arguments, including division
  by zero and a negative shift distance.  `scripts/primop-check.mjs` is the suite the
  ten `*.test.js` files run against it.
* **The two representations are held to different standards.**  Under `faithful` every
  answer must be Lean's, and every one of them is: 597 assertions over the five modules.
  Under `pbo` a `Nat`, an `Int`, a `USize`, a `UInt64`, an `Int64` and an `ISize` are
  JavaScript numbers, which hold an integer exactly only below `2^53`; these snapshots
  exceed that on purpose (`-1 : UInt64` is `2^64 - 1`), so the suite asserts Lean's
  answer for everything inside the range and *names* what falls outside it — a count of
  the answers that do not fit, and a list of the exports that fit but are reached
  through one that does not, each of which is asserted to disagree with Lean so the list
  cannot go stale.  Two exports are in that list, both `~~~(-3)` at 64 bits.
* **The runtime gained what those modules call**, in both preludes: the wrapping
  `Int64`/`ISize` addition, subtraction and multiplication and their comparisons, the
  bitwise operations and shifts of `UInt64`, `USize`, `Int64`, `ISize` and `Nat` (Lean
  takes a 64-bit shift distance modulo 64, and a negative one counts from the top), the
  complement, `Int.not`, and `Nat.sub` over `BigInt`s — 37 exports per prelude.
* `lake test` compiles all five modules under both presets and checks that the `BigInt`
  prelude appears in exactly one of them, and `scripts/run_snapshots_nodejs_dot_tests`
  now runs **1 284** Node assertions over 32 generated modules.

## Added after the plan: the inliner, and the terms before the optimiser

Three things asked for after `TODO.md` was written, all landed:

* **An inliner.**  `LakeJs/Inline.lean` rewrites a saturated call of an inlinable
  top-level declaration into that declaration's body, with the arguments of the call in
  place of its parameters — a `Ren` of `LakeJs/Rename.lean` applied with
  `Term.rename?`, so the result is still a well-scoped, well-typed term of the same
  signature.  A declaration is inlinable when Lean marks it `@[inline]` or
  `@[macro_inline]`, or when its body is small and straight-line; never when it is
  `@[noinline]`, a member of a merged group, an unboxed instance, or mentions its own
  name.  The module is now translated callees first, so the body a call site inlines is
  the callee's finished term, and a declaration nothing exports and nothing calls any
  more is no longer printed.  `SnapshotsMy/InlineDemo.lean` (new, with a Node suite and
  an entry in the test run) shows the four answers; `SnapshotsPBOPure/Fusion02.js` and
  `SnapshotsMy/HashContainers.js` are the snapshots that changed.
* **`<Module>-Expr.txt`.**  `LakeJs/TermPretty.lean` prints a `Term` as an indented
  s-expression, and the driver writes the terms *as the translation produced them*,
  before the optimiser, beside the `.js` file (`--no-expr` turns it off).  Every snapshot
  in `scripts/snapshot-files.txt` has one.
* **The inliner is part of the relation.**  `LakeJs/Reduce.lean`'s `Step` now carries the
  table of inlinable declarations and has two more rules, `delta` (a saturated call is the
  callee's body) and `deltaLit` (a reference to a declaration whose body is a literal is
  that literal), and `Term.inlineCalls_chain` proves that the inliner's output is
  reachable from its input by those rules — the same statement `Term.simp_chain` makes
  about the simplifier.  `LakeJs/OptimiseChain.lean` puts the whole pipeline together
  (`LakeJs.Compile.optimise_chain`).
* **`OPTIMIZER_PROPOSALS.md`.**  Eleven proposals for further optimisation, with what the
  output looks like now, what it would take, and how each would be checked — including
  how to bring the inliner into the relation of `LakeJs/Reduce.lean`.
