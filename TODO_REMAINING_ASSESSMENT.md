# What of `TODO.md` is still unimplemented — an independent assessment

This file re-checks every item of `TODO.md` against the code and the generated output as
they stand today, rather than against the earlier write-up in `TODO_STATUS.md`.  Every
verdict below is backed by something that was run in this tree; the commands are given so
each one can be reproduced.

**Baseline of this assessment.**

* `lake build` — clean, 0 errors, and no `sorry`/`admit` anywhere under `LakeJs/`
  (`rg -n '\bsorry\b' --glob '*.lean'` finds nothing).
* `lake test` — *all tests passed (123 modules compiled, 5 refused)*, **but only after**
  `lake build SnapshotsPBOPure SnapshotsPBOPartial SnapshotsMy`.  On a tree where only the
  default targets are built, `lake test` fails 142 tests with
  `unknown module prefix 'SnapshotsPBOPure'`: the `extraDepTargets` of the test executable
  does not actually get the snapshot libraries built.  This is a real, reproducible defect
  in the test setup (see *Cross-cutting* below).
* `bash scripts/run_snapshots_nodejs_dot_tests` — 1284 assertions, 0 failures.
  (The script has no executable bit, so `./scripts/...` fails with *Permission denied*;
  all `scripts/*` are mode `100644` in git.)

## Summary

| # | Item of `TODO.md` | Verdict |
| :-- | :--- | :--- |
| 1 | `enum (nOfConstructors) (shift)`, uniting the `Ordering` special case | **done** |
| 2 | LCNF join points made part of `Term`, for optimisation | **partly** — shared at translation time, *not* a construct of `Term` |
| 3 (first) | `export const …` instead of a trailing `export { … }` | **done** |
| 3 (second) | a `*.test.js` per emitted module, plus a runner script | **done for the 17 files the item lists**; 126 of the 158 emitted modules still have no suite |
| 4 | no unused bound variables; make them impossible to build | **partly** — dead `let`s are gone, but the intrinsic guarantee was deliberately not built, and unused *loop slots* and *parameters* still reach the output |
| 5 | the names of a `Sig` are unique | **partly** — a checked side condition, not a property of the type |
| 6a | `Lit` indexed by `LeanPrimTy`; `float_decide` instead of bare `native_decide` | **mostly done** — the tactic exists but is used by no live proof and its test file is disabled |
| 6b | drop `JsPrim`, use the `Externs` catalogue | **mostly done** — a residue of 8 `JsOp` constructors remains, two of them still type-polymorphic |
| 6c | `…-num.js` / `…-bigint.js` from one source, tested via `…_shouldBeTrue` | **done** |
| 7 | loop performance per `MUTUAL_LOOP_PERF.md` | **P1–P6 done; P7 partly** — benchmarks are not wired into any runner, and the plan's timing target is still not met |
| 8 | the optimiser as an inductive `Prop` relation (PLFA style) | **partly** — the relation and soundness theorems exist, but the sketch's `Value`/`Progress`/`Steps`/`optimize` architecture does not, and one pass rewrites terms outside the relation |

Nothing in `TODO.md` is untouched; five items are complete, six carry a real remainder.
The remainders, in the order I would tackle them, are listed at the end.

---

## 1. `Ty.enum` with a shift — done

`LakeJs/Ty.lean:151` is `| enum : (nOfConstructors : Nat) → (h_nonEmpty : … ) → (shift : Int) → Ty`,
`Ty.ordering` is the abbreviation `.enum 3 (shift := -1)`, and `LeanPrimTy` no longer has an
`ordering` constructor.  The printer honours the shift (`LakeJs/EmitJs.lean:82`, `unshift`).

Checked end to end by compiling a fresh module with the built backend:
`def cmp2 (a b : Nat) : Ordering := compare a b` emits
`(v0, v1) => { … return -1; … return 0; … return 1; }` — the numbering the item asked for.

*Observation, not a gap:* no snapshot in the corpus returns an `Ordering`, so the shifted
numbering is not covered by the regression suites; the same probe also shows two missed
optimisations (a `const v3 = -1;` copy that is not folded into its single use, and
`instDecidableEqOrdering(v2, v3)` where `v2 === v3` would do).

## 2. Join points — partly

What the item asks for is that join points become *part of `Term`*.  They did not:
`Term` (`LakeJs/Expr.lean`) has no join-point constructor, and `LakeJs/Reduce.lean` has no
rule that mentions one.  What landed instead is at translation time: a join point with two
or more jumps is bound as a local function (`Term.letE` of a `Term.lamN`) and each jump is
a call of it, so its body is emitted once instead of once per jump.

Consequences that remain:

* the sharing is decided once, in `LakeJs/FromLcnf.lean` (`transBody`), under three
  conservative conditions — at least two jumps, a body above `jpShareSize`, and no call to
  the declaration or its mutual group.  A join point failing any of them is still inlined
  at every jump, and no later pass can reconsider that decision;
* because there is no join-point form in the term language, the optimiser cannot do
  anything *to* join points: there is no contification rule, no rule that turns a shared
  local function back into straight-line code when it ends up with one call, and nothing
  about jumps in the relation of item 8.

## 3. Emitted modules — first half done, second half done only for the listed files

`export const` is what the emitter produces (`SnapshotsMy/GcdEntry.js` is the item's own
example, now two `export const` lines and no trailing `export { … }`).

All 17 files the item lists have a `*.test.js` beside them, and
`scripts/run_snapshots_nodejs_dot_tests` exists and passes (1284 assertions over 32
modules).  Beyond the list, however, **126 of the 158 generated `.js` files in the tree have
no test suite** — the runner only walks `scripts/snapshot-files.txt`, which holds 32
entries.  If the intent was "every emitted module is exercised from Node", that is the
remaining work; if it was the literal list, the item is closed.

Minor: the runner is not executable (`bash scripts/run_snapshots_nodejs_dot_tests` works,
`./scripts/run_snapshots_nodejs_dot_tests` does not).

## 4. Unused bound variables — partly, and the strongest half was declined

The item has two halves: *don't print unused variables*, and *make it impossible to build a
`Term` with unused bound variables*, by implementing `USAGE_INDEX_ASSESSMENT.md`.

The second half was **not** implemented, and that document is itself the argument against
it (§8: index nothing, delete dead `let`s in `Simp`, check the result extrinsically).  So
the outcome is consistent with the plan `TODO.md` points at, but it is not what the
sentence "it should be impossible to build `Term` with unused bound variables" asks for:
`Term` is unindexed, and a term with a dead binder is still a term.

What did land: `Term.strengthen?` and a dead-`let` rule in `LakeJs/Simp.lean`, the
extrinsic `Term.noUnusedLet`/`Term.unusedParams` in `LakeJs/Rename.lean`, an assertion over
the whole corpus in `LakeJsTest/Main.lean:301`, and a `note` line per declaration with an
unread parameter.  The `headOf` example of the item is fixed: `SnapshotsMy/UnreachBranch.js`
is now `export const headOf = (v0) => v0._1;`.

What is still printed, measured with `node scripts/count-unused-bindings.mjs`:

* **6 unused loop slots**, all in `SnapshotsMy/HashContainers.js` — e.g.
  `List_forIn__loop__at__test7_spec_0` opens with `let v5 = v0, v6 = v1, …` and never reads
  `v5`.  These are binders of `Term.loop`, which `Term.noUnusedLet` does not look at (it
  only covers `Term.letE`), so the corpus assertion passes while the output still declares
  them.  A dead-slot elimination pass, plus extending `noUnusedLet` to loop slots, is the
  concrete missing piece.
* **21 unused parameters** across 11 modules.  These are reported, not removed — a
  deliberate choice (§4 of the assessment: a parameter is part of the calling convention),
  but they are "unused variables that are printed", so the item is not closed by its own
  wording.
* `Term.noUnusedLet` and friends are `partial`, so the theorem the plan offers as the
  honest formal version — `(Simp.simp t).noUnusedLet = true` — is not stated, let alone
  proved.

## 5. Unique names in a `Sig` — partly

`abbrev Sig := List GlobalDecl` is unchanged.  Uniqueness is a `Bool` predicate
(`Sig.namesUnique`, `LakeJs/Expr.lean:108`), a module whose signature fails it is refused
(`LakeJs/Compile.lean:920`), and the one place uniqueness is needed has a theorem under it
as a hypothesis (`GlobalRef.ty_unique_of_namesUnique`).  That is a sound engineering
answer, but the type still admits a `Sig` with duplicate names, so "names should be unique"
holds by a runtime check rather than by construction.

## 6a. `Lit` over `LeanPrimTy`, and `float_decide` — mostly done

`Lit : LeanPrimTy → Type` (`LakeJs/Expr.lean:187`) with a constructor per literal-carrying
leaf, and `Float`/`Float32`/`Array Float` are carried natively.  Two remainders:

* the alternative the item floats — splitting `LeanPrimTy` into the leaves that can have a
  constant and the leaves that cannot — was not taken.  `LeanPrimTy` has 27 constructors and
  `Lit` has 24; `childProcess`, `shareCommonObject` and `shareCommonState` simply have no
  `Lit` row, which is the invariant the split would have made structural;
* `float_decide` exists (`LakeJs/FloatDecide.lean`) and is a genuine guard around
  `native_decide`, but **no proof in the project uses it**: the only other mention is a
  docstring.  Its test file is `LakeJs/FloatDecideTests.lean_` — the trailing underscore
  keeps it out of the build, and its contents import `RequestProject.*` and `Mathlib`,
  neither of which this project has.  So the guard is unexercised in this build.

## 6b. `JsPrim` → `Externs` — mostly done

`JsPrim` is gone; arithmetic, comparisons, string and array operations are `Term.extern` of
a row of `LakeJs/Externs.lean`, and whether a call prints as an operator is a decision of
`LakeJs/EmitJs.lean` alone.  The parenthetical of the item is answered mechanically:
`lake env lean scripts/check-extern-names.lean` reports *0* rows whose Lean name is missing
and *0* rows with an `IO` type — the twelve that failed are already commented out in the
catalogue, each with its reason.

The remainder is `JsOp` (`LakeJs/Expr.lean:241`), eight operations kept outside the
catalogue: `cast`, `boolAnd`, `boolOr`, `boolNot`, `boolBEq`, `charBEq`, `natSubExact`,
`toStr`.  Six of them are monomorphic and have a defensible justification (they are not
`@[extern]` Lean functions).  Two do not fit the item's own criterion — `cast (σ τ : Ty) :
JsOp [σ] τ` and `toStr (τ : Ty) : JsOp [τ] .string` are exactly the "any type" shape that
the item objected to in `beq (τ : Ty)`.  `cast` in particular lets any value be re-read at
any type, which is the one hole left in "a `Term` is Lean code, typed as Lean types it".

## 6c. One source, two representations — done

`PrimOpIntDivConfigurable-{num,bigint}.js` and `PrimOpIntDivNonConfigurable.js` are
generated and tested (the `…_shouldBeTrue` exports are asserted `true`); the `-bigint`
output contains `BigInt` literals and imports `runtime/lean_runtime_bigint.mjs`, the
non-configurable one contains no `BigInt` at all.  The same treatment was extended to
`PrimOpInt01/02/03Configurable` and `PrimOpIntBit01/02Configurable` against expectations
computed by Lean itself.  Nothing outstanding.

## 7. Loop performance — P1–P6 done, P7 partly

P1–P6 of `MUTUAL_LOOP_PERF.md` are implemented, and their *structural* consequences are
asserted in `lake test` (no object built inside a loop body, no `Math.max` in a guarded
predecessor, `return` rather than a flag, no `_mut$` tag for a statically single cycle).

P7 is marked `[~]` in the plan itself, and two of its bullets are still open:

* **the benchmarks are in no runner.**  `rg bench LakeJsTest scripts/run_snapshots_nodejs_dot_tests`
  finds nothing: `scripts/bench-generated.mjs` and `scripts/bench-mutual-loop*.mjs` have to
  be run by hand, so the plan's "add them as a reported measurement" has not happened;
* **the timing goal is not reached.**  Run here: `node scripts/bench-generated.mjs` gives
  *generated 19 ms* against *expected (hand-written) shape 14 ms*.  The plan's stated
  outcome was to come out *ahead* of the hand-written shape.  The large win (251 ms → 19 ms)
  is real; the last 35 % is not.

## 8. The optimiser as an inductive relation — partly

This is the item with the largest remainder, though the part that landed is substantial.

**What exists.** `LakeJs/Reduce.lean` defines `Step` (an inductive `Prop`, one constructor
per rewrite rule and per position a rewrite may occur in, over `Term`/`Spine`/`Alts`/`Body`)
and its reflexive-transitive closure `Chain`, written `—↠[tbl]`; the simplifier, the inliner
and the scalariser were made structurally recursive so that theorems about them are
possible, and each is proved sound for the relation (`Term.simp_chain`,
`Term.simpAll_chain`, `Term.inlineCalls_chain`, `Term.scalarise_chain`), with
`LakeJs.OptimiseChain.optimise_chain` covering the whole pipeline the driver runs.  Three
metatheoretic questions are answered, all in the negative and all proved:
`Step` is not confluent and not locally confluent (`LakeJs/ReduceConfluence.lean`), one
simplifier sweep is not idempotent (`LakeJs/SimpFixpoint.lean`), and `Step` does not
terminate (`LakeJs/ReduceCycle.lean`).

**What does not exist.**

* None of the PLFA-shaped architecture the item sketches: there is no `Value`, no
  `Progress`/`progress`, no `Result`, no `Steps`, and no `optimize` driven by them.  The
  relation is a *specification* that the hand-written passes are proved to respect, not the
  engine that performs the optimisation.  Whether that is acceptable is a design call, but
  it is not what the item describes.
* The item's constraint *"only this function should be able to transform `Term` to `Term`"*
  does **not** hold.  `LakeJs/Specialise.lean` rewrites the bodies of a whole group into one
  loop; its core (`letSpine`, `specBody`) is `partial`, so it has no equations and no
  soundness theorem is possible in its current form, and it is outside `Step`.
* Consequently the payoff the item names is out of reach as stated: `Relation.church_rosser`
  is not merely unproved, it is *false* for `Step`, and an `Std.IdempotentOp` instance for
  one simplifier sweep is false too.  If those properties are wanted, the rule set has to be
  changed (the `iteGuard` self-loop and the `eta`/`delta` critical pair are the two known
  obstructions, both exhibited in the files above).
* The item's aside *"probably doesn't require gas because `Term` is total"* is only half
  true today: the scalariser needed a `Scalarise.splitBudget` counter to become structural.

## Cross-cutting findings

1. **`lake test` is not self-contained.**  From a tree where only the default targets are
   built it reports 142 failures (`unknown module prefix 'SnapshotsPBOPure'`).  Running
   `lake build SnapshotsPBOPure SnapshotsPBOPartial SnapshotsMy` first makes it pass.  The
   `extraDepTargets` entry in `lakefile.toml` is meant to prevent exactly this and does not.
2. **Node suites and benchmarks are outside `lake test`.**  Both the 1284-assertion Node run
   and the timing benchmarks must be invoked by hand; nothing fails if the generated `.js`
   files drift from the backend until someone remembers to re-run them.
3. **`scripts/*` are not executable** in git (mode `100644`), including the runner the item
   asked for by name.
4. **Stale, disabled sources.**  `LakeJs/FloatDecideTests.lean_`, `LakeJs/TyDerive.lean_`,
   `LakeJs/TyMeta*.lean_` and eight `Snapshots*/….lean_` files are excluded from the build by
   their file extension; the first still refers to a different project (`RequestProject`,
   `Mathlib`).  They are dead weight or unfinished work, and nothing marks which.

## What I would do next, in order

1. **Dead loop slots** (item 4): drop slots no iteration reads, extend `noUnusedLet` to
   `Term.loop`, and assert it — this removes the last unused bindings from the output.
2. **Fix `lake test`'s dependency on pre-built snapshots**, and call the Node runner from it
   (cross-cutting 1 and 2); everything else rests on the suites being run.
3. **Bring `Specialise` into the relation** (item 8): make `letSpine`/`specBody` structural,
   then either prove a `—↠` theorem for it or state honestly, in the type, that it relates
   modules rather than terms.
4. **Eliminate `JsOp.cast`** (item 6b), the last arbitrary-type operation, by giving the
   translation a typed coercion for each case it actually needs.
5. **Join points in `Term`** (item 2), if the optimiser is to reason about them at all; this
   is the item whose intent is least served by what exists.
6. **Decide item 3's scope**: either extend the Node suites to the other 126 emitted modules
   or write down that `scripts/snapshot-files.txt` is the intended, curated subset.
7. **Either use `float_decide` or retire it** (item 6a), and restore a test file for it that
   builds in this project.
8. **P7's remaining half** (item 7): wire the benchmarks in as a reported measurement, and
   decide whether the 19 ms vs 14 ms gap is worth closing.

---

*Note on the negative results cited under item 8*: `step_not_confluent`,
`simp_not_idempotent` and `step_not_wellFounded` were re-checked here with
`#print axioms`; each depends only on `propext`, `Classical.choice` and `Quot.sound`, so
they are genuine proofs rather than assumptions.

---

## Update: items 2 and 4 have moved on

Join points are a construct of `Term` (`Term.joinPoint`, `Term.jump`), and the usage
discipline of `LakeJs.Usage` is now *enforced*: two passes establish it
(`LakeJs.LinearLet`, `LakeJs.DeadSlot`), `LakeJs.Compile` refuses a module whose printed
declarations break it, and `lake test` re-checks it over the corpus.  The unused loop
slots and the singly-read `let`s this file counted are gone from the generated
JavaScript; what is still only *reported* is an unread **function parameter**, which is
part of the function's type.  See `USAGE_ENFORCEMENT.md`.
