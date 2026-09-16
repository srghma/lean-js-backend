# `CaptureDerefRegression01`: why the merged dispatch loop is slower, and what to do about it

This answers the three questions about the mutual pair `testEven`/`testOdd` in
`SnapshotsPBOPure/CaptureDerefRegression01.lean`:

1. why the code we emit today (one merged dispatch loop for the whole mutual group) is
   slower than the expected output,
2. how to close the gap,
3. when the merged loop is nevertheless the better answer.

Everything numeric below was measured in this repository with `node v22.21.1`; the
benchmarks are checked in so the numbers can be reproduced and re-run after each change:

```
node scripts/bench-mutual-loop.mjs        [N] [iters]   # A vs B, plus two hybrids
node scripts/bench-mutual-loop-steps.mjs  [N] [iters]   # one transformation at a time
node scripts/bench-mutual-loop-robust.mjs [N] [iters]   # where the merged loop wins
```

Each benchmark first prints the result of every variant and they must all agree, so a
variant that is accidentally not computing the same function is visible immediately.

---

## 0. The two shapes being compared

*Expected* (`SnapshotsPBOPure/CaptureDerefRegression01.expected.js`): the `Box2 Int`
accumulator is **scalarised** into two `let` parameters, the two-member cycle is
**unrolled** into a single `while (true)` inside `testEven`, exits are plain `return`s,
and `testOdd` is an ordinary function that enters `testEven`'s loop once.

*Actual* (`SnapshotsPBOPure/CaptureDerefRegression01.js`): one `_mut$testEven(v0, v1, v2)`
holding a member **tag** plus one slot per argument, a `Box2` object **rebuilt on every
iteration**, exits written as `c$3 = false; r$3 = …; continue`, `Math.max(0, n - 1)` for
the `Nat` predecessor, and one wrapper per member.

## 1. Why ours is slower — measured, cause by cause

`scripts/bench-mutual-loop-steps.mjs` starts from the emitted code (`S0`) and applies one
transformation per step, so each line of the table is the cost of exactly one difference.

| Step | What it adds on top of the previous step | N=1000, 20 000 iters | N=100000, 200 iters |
|---|---|---|---|
| `S0` | the code we emit today | **251 ms** | **183 ms** |
| `S1` | + scalarise the `Box2` accumulator (no per-iteration allocation) | 63 ms | 63 ms |
| `S2` | + `return` instead of `c$ = false; r$ = …; continue` | 51 ms | 50 ms |
| `S3` | + `n - 1` instead of `Math.max(0, n - 1)` | 43 ms | 44 ms |
| `S4` | + specialise the member tag away (unroll the 2-cycle) | **20 ms** | **19 ms** |
| `S5` | = `S4` with the curried entry points, i.e. the expected output | 34 ms | 31 ms |

Reading the table (steady-state rounds; the full output has three rounds per run):

* **The per-iteration allocation is the whole story — ~4× on its own** (`S0 → S1`,
  251 ms → 63 ms). Every trip round the loop we destructure `v5` and then build a fresh
  `{ tag: 0, _1, _2 }` that dies immediately; at N=1000 that is 1000 short-lived objects
  per call, i.e. scavenger pressure plus two stores and two loads that the expected code
  does not perform at all. The expected code allocates **one** object, at the exit.
  Confirmation from the other benchmark (`scripts/bench-mutual-loop.mjs`): unrolling the
  cycle while *keeping* the box (variant `B2`) only gets 254 ms → 200 ms, whereas keeping
  the dispatch loop and *dropping* the box (variant `B1`) gets 254 ms → 63 ms. Boxing, not
  merging, is the dominant cost.
* **The member tag costs about 2×** (`S3 → S4`, 43 ms → 20 ms). Two effects are bundled
  here: the extra branch on `v3` on every iteration, and the fact that with the tag gone
  the two half-steps fuse into one straight-line loop body with one back edge instead of
  two. Note this is the *only* line of the table that is intrinsic to merging.
* **The flag-driven exit costs ~1.2×** (`S1 → S2`). `c$3 = false; r$3 = v5; continue`
  keeps the loop variable `r$3` alive across the loop and forces one more test of `c$3`
  and one more back edge before the function returns, where `return` leaves directly.
* **`Math.max(0, n - 1)` costs ~1.18×** (`S2 → S3`). The `Nat` predecessor is emitted as
  a call to `Math.max` even where the branch above it has already established `n !== 0`.
* **Noise in the emitted code.** `const v9 = 1; const v10 = v9; const v11 = v8 + v10;` —
  literal bindings and copies that LCNF names and that `LakeJs/Simp.lean` does not fold.
  This does not show up in a microbenchmark (V8 copy-propagates trivially), but it
  triples the size of the loop body, and loop/function body size is what V8's inlining
  budget is spent on. It matters at scale, not here.
* **Two structural costs not visible in this snapshot, but visible in `SnapshotsMy/MutualTail.js`:**
  * `groupTypes`/`unifyTy` widen a slot whose members disagree on its type to
    `Ty.typeParam`. One JS variable then holds, say, an integer for one member and an
    object for another — a polymorphic variable, which is exactly what stops V8 keeping a
    slot unboxed.
  * Members of different arities share one slot vector, padded with dummy values
    (`_mut$test3` has four slots; some members write `0` into `v7` just to fill it). The
    padding is written on every iteration.
* **Currying is not a win** (`S4` 20 ms vs `S5` 34 ms). The expected output's
  `(n) => (b_1, b_2) => …` is ~1.7× *slower* than the same loop taking all arguments at
  once, because each entry allocates a closure. So the target to aim for is `S4`, not a
  byte-for-byte copy of the expected file: take the expected file's scalarisation and
  unrolling, keep our uncurried entry points.

**Summary of the answer to (1):** merging is responsible for roughly a 2× factor. The
remaining ~6× is unrelated to merging — it is that the merged path currently re-boxes the
accumulator every iteration, exits through a flag, and calls `Math.max` for `n - 1`. Those
three are fixable without giving up the merged loop, and together they take 251 ms → 43 ms,
i.e. within ~1.3× of the expected output's 34 ms and only ~2× off the best shape measured.

## 2. How to improve — plan

Ordered by measured payoff per unit of risk. Each item is independent of the others unless
stated, and each ends with the check that should go into `lake test`.

### [ ] P1. Scalarise loop accumulators (the 4× item)

When a loop variable's type is a **non-recursive record or single-constructor type** whose
value is destructured and rebuilt inside the loop, and the value does not escape except at
the exits, give the loop one slot per field instead of one slot for the value, and build
the object only at the `return`s.

Before (emitted today):

```js
const _mut$testEven = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    …
    const v7 = v5._1;
    const v8 = v5._2;
    const v15 = { tag: 0, _1: v8 + 1, _2: v7 + 2 };   // allocated every iteration
    v3 = 1; v4 = v6; v5 = v15;
    continue;
  }
  return r$3;
};
```

After (P1 only — still merged, still flag-driven):

```js
const _mut$testEven = (t, n, b1, b2) => {
  let v3 = t, v4 = n, v5 = b1, v6 = b2, c = true, r1, r2;
  while (c) {
    …
    const n1 = Math.max(0, v4 - 1), x = (v6 + 1) | 0, y = (v5 + 2) | 0;
    v3 = 1; v4 = n1; v5 = x; v6 = y;
    continue;
  }
  return { _1: r1, _2: r2 };     // one allocation per call
};
const testEven = (n, b) => _mut$testEven(0, n, b._1, b._2);
```

* Where: `Compile.transGroup` / `groupTypes` (slot vector), plus the `Body.cont`
  construction in `FromLcnf`.
* The escape condition is the "re-boxing trap" already noted in the snapshot's own TODO
  comment: if the value is passed whole to another function, stored, or returned from a
  non-exit position, scalarising just moves the allocation, so **do not** scalarise then.
  Start with the conservative rule: scalarise only if every use inside the loop body is a
  projection or a reconstruction of the same constructor.
* Keep a boxed fallback so no snapshot can regress into an unsupported shape.
* Check: `CaptureDerefRegression01.js` contains no `{ tag:` inside a `while` body; the
  benchmark records `S1`-level timing.

### [ ] P2. Exit a loop with `return`, not a flag

Before:

```js
let … c$3 = true, r$3;
while (c$3) { … c$3 = false; r$3 = v5; continue; … }
return r$3;
```

After:

```js
while (true) { … return v5; … }
```

* Where: `EmitJs.bodyStmts` (`Body.ret` case) and the loop preamble in `EmitJs`
  (`loopFlag`/`loopRes` become unnecessary). This is purely an emission change: `Term.loop`
  is unchanged, and `Body.ret` is by construction in tail position of the enclosing
  function, which is what makes `return` sound here.
* Only when the loop *is* the whole function body. Where a loop appears as a sub-expression
  (`EmitJs` wraps it in an IIFE) the current flag form must stay, or the IIFE's `return`
  must be used instead.
* Check: no `c$` / `r$` identifier in any generated file whose loop is the function body;
  ~1.2× on the benchmark.

### [ ] P3. Emit `n - 1` for the `Nat` predecessor when `n ≠ 0` is already known

Before: `const v6 = Math.max(0, v4 - 1);` — after: `const v6 = v4 - 1;`.

* Where: the `Nat.sub`/pred primitive in `FromLcnf`, guarded by a small "this value is
  known non-zero on this path" fact carried down the `if`/`caseTag` branches (in this
  snapshot the branch is literally `if (n === 0) … else …`, so the fact is free).
* Truncation is only observable when the subtrahend exceeds the value; the guard is what
  proves that cannot happen, so this is not a "fast and unsafe number" option — it is
  exact. (Keep `Math.max` wherever the guard is absent.)
* Check: ~1.18×; `Math.max` disappears from the `Tco*`, `MutualTail` and
  `CaptureDerefRegression01` outputs.

### [ ] P4. Fold literal copies in `Simp`

Before: `const v9 = 1; const v10 = v9; const v11 = v8 + v10;`
After: `const v11 = v8 + 1;`

* Where: `LakeJs/Simp.lean`, two new rules, both non-duplicating and therefore safe for
  work and for evaluation order: `let x = lit; body` substitutes the literal (a literal is
  a value, so no work is duplicated), and `let x = y; body` substitutes the variable.
* No measurable runtime effect here; the point is output size and V8's inlining budget.
* Check: generated files shrink; all snapshots still agree under `node`.

### [ ] P5. Specialise the member tag away where the transition graph allows it

This is the only item that touches the merge decision itself. When the group's tag
transitions are statically known at each `continue` (as here: `testEven` always continues
as `testOdd` and vice versa), the tag is a compile-time value and the loop can be
**specialised per member** — for a 2-cycle that is exactly the expected output's unrolled
loop.

Before (merged, tag tested every iteration):

```js
while (c$3) { if (v3 === 0) { …; v3 = 1; continue; } else { …; v3 = 0; continue; } }
```

After (tag specialised; one member owns the loop, the rest enter it):

```js
const testEven = (n, b_1, b_2) => {
  while (true) {
    if (n === 0) return { _1: b_1, _2: b_2 };
    const nb1 = (b_2 + 1) | 0, nb2 = (b_1 + 2) | 0, nn = n - 1;
    if (nn === 0) return { _1: nb1, _2: nb2 };
    b_1 = (nb2 + 3) | 0; b_2 = (nb1 + 4) | 0; n = nn - 1;
  }
};
const testOdd = (n, b_1, b_2) => {
  if (n === 0) return { _1: b_1, _2: b_2 };
  return testEven(n - 1, (b_2 + 3) | 0, (b_1 + 4) | 0);
};
```

* Applicability rule to implement, in order: (a) every intra-group tail call names a
  *statically known* member; (b) the group's transition graph is a single cycle; (c) the
  unrolled body stays under a size budget (unrolling a k-cycle duplicates each member's
  body once, so cap k, e.g. k ≤ 3, and cap total node count). Otherwise fall back to the
  merged dispatch loop, which stays as the general case (see §3).
* Do **not** copy the currying of the expected output: measured `S4` (uncurried) 20 ms vs
  `S5` (curried) 34 ms.
* Check: `CaptureDerefRegression01.js` has no tag variable; `MutualTail`'s three-member
  group either specialises or keeps the merged loop, with the stack test still passing at
  depth 100 000.

### [ ] P6. Stop widening slots to `Ty.typeParam`, and stop padding

`groupTypes`/`unifyTy` give one slot vector to all members, typed `Ty.typeParam` wherever
two members disagree, and pad short members with dummy values. Both make the slot
polymorphic, which defeats V8's unboxing.

* After: give each member **its own** slots in the merged function (the union, laid out
  disjointly), so each slot has one type; or, cheaper, only merge members whose parameter
  types agree pointwise and compile the rest as ordinary functions.
* Check: no `Ty.typeParam` slot in the merged loops of `MutualTail`; no dummy `0` written
  into an unused slot.

### [ ] P7. Lock the numbers in

* Add `scripts/bench-mutual-loop*.mjs` to the test runner as a *reported* (not asserted)
  measurement, plus one asserted structural property per item above — those are stable,
  unlike timings: "no object literal inside a loop body", "no `c$` flag", "no `Math.max`
  in a guarded predecessor", "no tag variable for a statically-known 2-cycle".
* Keep the stack test (`depth 100 000` and `1 000 000`) asserted: it is the property the
  merged loop exists for, and P5 must not lose it.

Expected outcome if P1–P5 land: 251 ms → ~20 ms on this benchmark, i.e. ahead of the
expected output's 34 ms, with the merged loop retained as the fallback for the groups
where it is needed.

## 3. When is the merged loop better?

Not a fallback of last resort — it is strictly better in three situations, two of which
are about correctness rather than speed.

**(a) When the successor is data-dependent, or the cycle is not a simple cycle.**
Unrolling requires knowing at compile time which member runs next. Consider

```
f n a = if n = 0 then a else (if a % 3 = 0 then g else h) (n-1) (a+1)
g n a = if n = 0 then a else f (n-1) (a+2)
h n a = if n = 0 then a else (if a % 5 = 0 then f else g) (n-1) (a+3)
```

There is no member whose loop the others can be unrolled into, so the alternative is real
mutual tail calls — and JavaScript engines do not eliminate them.
`scripts/bench-mutual-loop-robust.mjs` measures exactly this:

| | N=1000, 20 000 iters | depth 100 000 | depth 1 000 000 |
|---|---|---|---|
| mutual calls | 21 ms | `RangeError: Maximum call stack size exceeded` | `RangeError` |
| merged loop | 31 ms | `150000` | `1500000` |

The merged loop pays ~1.5× per iteration and buys **termination**: the call version cannot
run past a few tens of thousands of steps. For a backend whose stated goal is that every
total Lean function becomes a `while`/`for` loop, that is not a trade-off, it is the
requirement. (The expected output for `CaptureDerefRegression01` gets away without it only
because the cycle has length 2 and `testOdd` enters `testEven` exactly once.)

**(b) When the cycle is long, or the members are large.** Unrolling a k-member cycle
duplicates each member's body into one loop; the merged loop's size is linear in the group
and independent of k, and there is one function for the JIT to compile and warm up instead
of k. For a big group entered from many places, that is also better instruction-cache and
inlining-budget behaviour.

**(c) When the group is cold.** For code that is not hot, the merged loop is smaller
output for the same semantics, and the dispatch cost is never paid enough times to matter.

The right policy, then, is the one P5 encodes: **specialise when the transition graph is
statically a small simple cycle; otherwise merge.** The improvements P1–P4 and P6 apply to
both paths, and are where nearly all of the measured gap actually lives.
