# `Tco04.test1` end to end: Lean → `Term` → the `Reduce.lean` evaluator

**What this answers.**  You confirmed F1 of `TERM_ONE_GRAMMAR_ASSESSMENT.md`, and asked three
things about the design that document recommends:

1. how `test1` of `SnapshotsPBOPure/Tco04.lean` becomes a `Term`;
2. how the `Reduce.lean`-based evaluator then runs it on an input;
3. what happens for an `n` that satisfies `Valid1`, and for an `n` that does not — where you
   expect Lean to accept the first call and **reject the second with a type error**.

The short answers, then the details.

| Question | Answer |
| :-- | :-- |
| What `test1` becomes | one merged `fix` for the clique `{test1, test2}`, arguments `(tag, x)`, rank `[counter]` initialised to `n.toNat`; `test1` and `test2` become two thin wrappers over it. §2–§3 |
| Where the `n.toNat` comes from | Lean already stored exactly that measure, tag dispatch included, in `test1._mutual`. **[verified]**, §1.2 |
| How you run it | apply the term to `.lit (.int 7)` and reduce: `Steps (test1Term ⬝ .lit (.int 7)) (.lit (.int 1))`. §5 |
| Valid input (`n = 7`) | the term reduces to `1`, Lean's answer; the counter never runs out — that is a theorem, not an accident (§4) |
| Invalid input (`n = 5`) | **no type error at the `Term` level.**  The term is total and answers the exhausted default, `0`.  A type error is only possible one layer up, in the generated Lean-facing wrapper that carries `h : Valid1 n` — and that layer must therefore be part of the deliverable.  §6–§7 |

Statements are marked **[verified]** when I ran them against this tree on Lean 4.28.0, and
**[proposed]** when they are design.  §9 lists the amendments this walkthrough makes to
`TERM_ONE_GRAMMAR_ASSESSMENT.md`.

**See also** `TERM_VALID_DATA_WALKTHROUGH.md`, which repeats this exercise with a *data*
argument: a guarded mutual pair over a mutual inductive whose precondition also constrains
the shape of the argument.  The answers there are the same, with one addition that the
numeric case does not admit — a shape condition can be moved into the runtime *type*, and
then a bad input is a type error after all.

---

## 1. What Lean hands us

### 1.1 The erased body  **[verified]**

`lake env lean --run scripts/dump-lcnf-saveBase.lean SnapshotsPBOPure.Tco04` prints:

```
════ 🎯 test1
def test1 n h : Int :=
  let _x.1 := 1;
  let _x.2 := Int.ofNat _x.1;
  let _x.3 := Int.instDecidableEq n _x.2;
  cases _x.3 : Int
  | Decidable.isFalse hn =>
    let _x.4 := Int.sub n _x.2;
    let _x.5 := test2 _x.4 ◾;
    return _x.5
  | Decidable.isTrue hn =>
    return n

════ 🎯 test2
def test2 m h : Int :=
  let _x.1 := 2;
  let _x.2 := Int.ofNat _x.1;
  let _x.3 := Int.instDecidableEq m _x.2;
  cases _x.3 : Int
  | Decidable.isFalse hm =>
    let _x.4 := Int.sub m _x.2;
    let _x.5 := test1 _x.4 ◾;
    return _x.5
  | Decidable.isTrue hm =>
    return m
```

Two facts to hold on to:

* `h` survives as a **parameter**, but its *argument* at every call site is `◾` — erased.  There
  is nothing left of `Valid1 n` for the front end to translate even if it wanted to.  The
  translator drops the parameter (this is what today's emitted `Tco04.js` does: `test1 = (v0) =>
  …`, one argument).
* The recursion is **not** self-recursion in either body: `test1` calls `test2` and vice versa.
  The `fix` has to be built for the clique, not for one function.

### 1.2 The measure, and where it actually lives  **[verified]**

`scripts/dump-wf-measure.lean` (added by this run) reads
`Lean.Elab.WF.eqnInfoExt`, follows `declNameNonRec`, and pulls the measure out of the packed
body:

```
$ lake env lean --run scripts/dump-wf-measure.lean SnapshotsPBOPure.Tco04 test1
test1: WF recursion
  clique       : [test1, test2]
  packed decl  : test1._mutual
  measure, via WellFounded.Nat.fix:
    fun x => PSum.casesOn x (fun _x => PSigma.casesOn _x fun n h => n.toNat)
                            (fun _x => PSigma.casesOn _x fun m h => m.toNat)
```

This is worth reading slowly, because it is *already* the shape the plan proposes:

* the clique is packed into one function over `PSum ((n : Int) ×' Valid1 n) ((m : Int) ×' Valid2 m)`
  — a **tag plus the member's own arguments**, exactly the `ps = [tag, x]` of §5.7 of the
  assessment;
* the measure is one **`Nat`**, dispatched on the tag: `n.toNat` in the left branch, `m.toNat` in
  the right — exactly the shared rank;
* the well-founded relation is `InvImage (· < ·) measure` on `Nat`, i.e. `decreasing_by` proved
  `measure(callee args) < measure(caller args)` for *both* cross-calls.

The same probe on the other well-founded members of the corpus:

| Declaration | Packed decl | Measure recovered |
| :-- | :-- | :-- |
| `Tco04.test1`/`test2` | `test1._mutual` | `PSum.casesOn … n.toNat / m.toNat` |
| `Tco03.go`/`k` | `go._mutual` | `PSum.casesOn … n / m` |
| `Tco07.boom` | `boom._unary` | `fun ⟨n, h⟩ => n` |
| `GcdEntry.Nat.gcd` | `Nat.gcd._unary` | `fun ⟨m, n⟩ => m` |
| `Fusion02.toArrayLoop` | `toArrayLoop._unary` | found, but did not print: the measure mentions binders of the packed lambda (the pretty printer panics on the loose bvar) |

So for four of the five the rank is a small closed arithmetic expression that the existing LCNF
pipeline can compile without any new machinery.  The fifth is the case F3 already called out:
extraction must **instantiate the packed binders** before it looks at the measure, not grab a
subterm.

---

## 2. The `Term`, in words

One global holding the merged recursion, and one thin wrapper per public entry point — mirroring
Lean's own `test1._mutual`:

```
Tco04.test1._mutual : nat ⇒ nat ⇒ int ⇒ int       -- rank slot, tag, argument
Tco04.test1         : int ⇒ int                   -- 🎯 public
Tco04.test2         : int ⇒ int                   -- 🎯 public
```

* `ps = [Ty.nat, Ty.int]`: the tag (`0 = test1`, `1 = test2`) and the member's `Int` argument.
  Both are real runtime values.  `h` is not there; it never reached LCNF.
* `rk = [.counter]`: one descending slot.  Its entry value is the compiled measure, which here is
  just `Int.toNat` of the argument — the extern `lean_int_to_nat`, already in the catalogue.
* `exhausted` is the canonical inhabitant of `int`, `.lit (.int 0)`.

`test1` is `ƛ n, test1._mutual ⬝ (n.toNat) ⬝ 0 ⬝ n`, and `test2` is the same with tag `1` and
measure `m.toNat`.  Note that the tag dispatch and the shared rank are not an invention of the
translator: §1.2 shows Lean packed the clique the same way.

---

## 3. The `Term`, written out  **[proposed]**

In the notation the tree already uses (`ƛ`, `♯i`, `callExtern`, `.lit`), with the `fix` and
`selfCall` constructors of §5.2 of the assessment:

```lean
/-- `Tco04`'s clique, merged: `tag = 0` is `test1`, `tag = 1` is `test2`.
    Context inside `body`: `♯0 = tag : nat`, `♯1 = x : int`. -/
def tco04Mutual {Sg : Sig} : Term Sg [] (Ty.nat ⇒ Ty.nat ⇒ Ty.int ⇒ Ty.int) :=
  Term.fix (rk := [.counter]) (ps := [Ty.nat, Ty.int])
    (body :=
      .ite (callExtern (.prim2 .lean_nat_dec_eq) (.cons (♯0) (.cons (.lit (.nat 0)) .nil)))
        -- tag 0 : test1, with x = n
        (.ite (callExtern (.prim2 .lean_int_dec_eq) (.cons (♯1) (.cons (.lit (.int 1)) .nil)))
          (♯1)
          (.selfCall .head (.here .nil)
            (.cons (.lit (.nat 1))                                   -- become test2
              (.cons (callExtern (.prim2 .lean_int_sub)
                        (.cons (♯1) (.cons (.lit (.int 1)) .nil)))   -- n - 1
                .nil))))
        -- tag 1 : test2, with x = m
        (.ite (callExtern (.prim2 .lean_int_dec_eq) (.cons (♯1) (.cons (.lit (.int 2)) .nil)))
          (♯1)
          (.selfCall .head (.here .nil)
            (.cons (.lit (.nat 0))                                   -- become test1
              (.cons (callExtern (.prim2 .lean_int_sub)
                        (.cons (♯1) (.cons (.lit (.int 2)) .nil)))   -- m - 2
                .nil)))))
    (exhausted := .lit (.int 0))

/-- 🎯 `test1`. -/
def tco04Test1 {Sg : Sig} : Term Sg [] (Ty.int ⇒ Ty.int) :=
  ƛ (tco04Mutual
       ⬝ callExtern (.prim1 .lean_int_to_nat) (.cons (♯0) .nil)   -- rank  := n.toNat
       ⬝ .lit (.nat 0)                                            -- tag   := test1
       ⬝ (♯0))                                                    -- x     := n

/-- 🎯 `test2`. -/
def tco04Test2 {Sg : Sig} : Term Sg [] (Ty.int ⇒ Ty.int) :=
  ƛ (tco04Mutual
       ⬝ callExtern (.prim1 .lean_int_to_nat) (.cons (♯0) .nil)
       ⬝ .lit (.nat 1)
       ⬝ (♯0))
```

Read off the guarantees:

* `Descends.here .nil` is the *only* thing a recursive call says about the rank: "this slot goes
  down by one".  There is no syntax that names the counter, so no term can reset it, and the
  reason `test1` cannot diverge is the shape of the tree, not a side condition.
* Everything else — the tag flip, `n - 1`, `m - 2` — is ordinary data the term computes.
* `Tail`/`block` is not needed here at all; with `Tail.label self` gone (plan item 2), a block is
  a nest of join points, and this clique does not need one.  The emitter still prints this
  particular `fix` as a `while (true)` loop, because all of its self-calls are in tail position —
  that is the "`while` is an emission property" of F1.

Two design points this exercise settles, both refinements of the assessment:

* **The counter must not be in scope inside `body`.**  §5.2 wrote `body` in context
  `rk.tys ++ ps ++ Γ`.  If the term can *read* the counter, two programs that differ only in the
  rank become distinguishable, and the emitter's "drop the counter for a plain tail loop"
  optimisation stops being semantics-preserving.  Make the body's context `ps ++ Γ` and keep rank
  values in the machine state only.  Sealing then means sealed in both directions: unnameable and
  unreadable.
* **The packed global must not be exported.**  The rank is an ordinary `nat` *argument* of
  `tco04Mutual`, so a caller who passes a too-small rank gets the exhausted default instead of
  the real answer.  That is harmless for termination but fatal for faithfulness, so
  `…_mutual` must be module-private and only the wrappers 🎯-marked in the `-Expr.txt` dump.

---

## 4. Why decrementing by one is enough  **[proposed, with a proof sketch]**

Lean's `decreasing_by` proved `measure(callee) < measure(caller)` for each cross-call.  The term
does something cruder: it starts a counter at `measure(entry args)` and subtracts one per call.
That is sound, and here is the invariant that says so:

> **Rank domination.**  At every point of the reduction, `counter ≥ measure(current args)`.

*Proof.*  At entry the two are equal.  At a call, `counter' = counter - 1` and
`measure(next) ≤ measure(cur) - 1` (Lean's strict decrease, in `Nat`), so
`counter' ≥ measure(cur) - 1 ≥ measure(next)`. ∎

Consequently the counter reaches `0` only when the measure is already `0`, which for a call Lean
itself could make is impossible before the base case is hit.  So:

* on inputs Lean could have called the function with, the counter is **never** the reason the
  term stops — the term computes Lean's answer;
* on other inputs, the counter is what stops it.

This is the precise sense in which the counter is not "fuel": it is not supplied by the caller,
it is not in the public signature, and its presence is invisible on the domain of the function.
The theorem to prove in phase 3, per translated clique, is the faithfulness statement of §7.

---

## 5. Running it with the `Reduce.lean` evaluator

### 5.1 The call

```lean
def call7 {Sg : Sig} : Term Sg [] Ty.int := tco04Test1 ⬝ .lit (.int 7)
```

and the result is a reduction in the relation of `LakeJs/Reduce.lean`:

```lean
example : Steps (call7 (Sg := Sg)) (.lit (.int 1)) := by …
```

After plan phase 2, `Term.eval` loses its `Terminating` hypothesis — the point of the whole
exercise — so the same call is also

```lean
#check (Term.eval call7 : Term Sg [] Ty.int)     -- total, no fuel, no certificate
```

Two honest caveats about "running" it today:

* `Term.eval` is **noncomputable**, and not because of termination: `Step` is a nondeterministic
  relation (`Step.quick` versus `Step.apArg`), so `Term.evalSN` picks the next term with
  `Classical.choose` (`TermTotal.lean`, "Why the evaluator is noncomputable").  You therefore
  *prove* `Steps call7 (.lit (.int 1))`; you cannot `#eval` it.
* To turn that into `Term.eval call7 = .lit (.int 1)` you need answers to be unique, i.e. a
  confluence (or determinism-up-to-value) lemma, which the tree does not have yet.

Both are cheap to fix and both should be plan items (§9): a computable deterministic
`Term.step?` with soundness/completeness against `Step`, plus `Term.run` defined by well-founded
recursion on the SN proof, gives a genuine `#eval`-able evaluator, and confluence gives the
equational form.

### 5.2 The trace, `n = 7`  (`Valid1 7` holds: `7 ≥ 1`, `7 % 3 = 1`)

| step | counter | tag | x | what happens |
| --: | --: | --: | --: | :-- |
| entry | `7 = (7 : Int).toNat` | 0 | 7 | `7 ≠ 1` → self-call |
| 1 | 6 | 1 | 6 | `6 ≠ 2` → self-call |
| 2 | 5 | 0 | 4 | `4 ≠ 1` → self-call |
| 3 | 4 | 1 | 3 | `3 ≠ 2` → self-call |
| 4 | 3 | 0 | 1 | `1 = 1` → **return `1`** |

`Steps call7 (.lit (.int 1))`, with three units of counter to spare — the slack predicted by §4
(the `m - 2` steps drop the measure by 2 but the counter only by 1).  `1` is what Lean computes
(`example : test1 7 (by grind only [Valid1]) = 1` in `Tco04.lean`) and what today's JavaScript
computes (`assert.equal(test1(7), 1)` in `Tco04.test.js`).

---

## 6. Your two questions, answered exactly

### 6.1 `n` satisfies `Valid1` — e.g. `n = 7`, `n = 4`, `n = 10`, `n = 3`

Nothing rejects anything, and the answer is Lean's:

| `n` | Lean `test1 n h` | `Term` | note |
| --: | --: | --: | :-- |
| 1 | 1 | 1 | base case, zero self-calls |
| 3 | 2 | 2 | lands on `test2`'s base case |
| 4 | 1 | 1 | |
| 7 | 1 | 1 | trace above |
| 10 | 1 | 1 | |

This is the content of the faithfulness theorem in §7.1: *for every `n` with `Valid1 n`*, the
term reduces to the literal Lean computes.

### 6.2 `n` does not satisfy `Valid1` — e.g. `n = 5` (`5 % 3 = 2`)

Here is the part of your expectation the design cannot meet as stated, and it is worth being
blunt about it.

**At the `Term` level there is no type error, and there cannot be one.**  `tco04Test1` has type
`Term Sg [] (Ty.int ⇒ Ty.int)`.  `Ty` is a language of *runtime* types — it has no `Prop`, no
dependency, and the LCNF it is built from has already erased `Valid1 n` to `◾` (§1.1).  Applying
it to `.lit (.int 5)` is as well-typed as applying it to `.lit (.int 7)`: both are `int`
literals, and the Lean type-checker has nothing left to object to.

What happens instead is that the term *runs*, and stops:

| step | counter | tag | x | |
| --: | --: | --: | --: | :-- |
| entry | `5` | 0 | 5 | `5 ≠ 1` |
| 1 | 4 | 1 | 4 | `4 ≠ 2` |
| 2 | 3 | 0 | 2 | `2 ≠ 1` |
| 3 | 2 | 1 | 1 | `1 ≠ 2` |
| 4 | 1 | 0 | −1 | `−1 ≠ 1` |
| 5 | 0 | 1 | −2 | `−2 ≠ 2` → self-call on a **zero** counter |
| — | — | — | — | **`exhausted` → `0`** |

So `Steps (tco04Test1 ⬝ .lit (.int 5)) (.lit (.int 0))`.  Compare the three layers:

| | `test1 5` |
| :-- | :-- |
| Lean | not callable — no proof of `Valid1 5` exists, so the expression does not elaborate |
| today's emitted JavaScript | **diverges**: `5 → 4 → 2 → 1 → −1 → −2 → −4 → …` forever |
| the proposed `Term` | terminates, answering the canonical inhabitant `0` |

The `Term` is therefore strictly better behaved than the code the backend emits today, and it is
sound — but it is not *silent* about being outside the domain, and it is not Lean's function
there, because Lean's function is not defined there.  This is the "faithfulness scope" item 5 of
§10 of the assessment, made concrete.

---

## 7. How to get the rejection you want

The rejection has to live where the `Prop` still exists — i.e. in Lean, above the `Term` — and
the translator should generate it.  Three layers, of which only the middle one is new work.

### 7.1 The faithfulness theorem (generated, one per entry point)  **[proposed]**

```lean
/-- On its domain, the translated term computes Lean's function. -/
theorem tco04Test1_faithful (n : Int) (h : Valid1 n) :
    Steps (tco04Test1 (Sg := Sg) ⬝ .lit (.int n)) (.lit (.int (SnapshotsPBOPure.test1 n h)))
```

proved by well-founded induction on `n.toNat`, using rank domination (§4) for the counter and the
`decreasing_by` facts Lean already established.  This is the statement that makes §6.1 a theorem
rather than five examples, and it carries the precondition explicitly — which is the right place
for it.

### 7.2 The typed entry wrapper (generated)  **[proposed]**

```lean
/-- 🎯 `test1`, callable exactly where Lean's `test1` is callable. -/
def Tco04.test1.run (n : Int) (h : Valid1 n) : Int := …   -- reads the literal the term answers
```

The `h` is computationally irrelevant and is dropped before the term is applied, but it is part
of the *type*, so:

```lean
#eval Tco04.test1.run 7 (by grind only [Valid1])   -- 1
#eval Tco04.test1.run 5 (by grind only [Valid1])   -- ✗ rejected: cannot prove `Valid1 5`
```

The second line fails to elaborate, with an error at the proof obligation — which is the
behaviour you asked for, obtained the only way it can be obtained: the precondition is restored
at the Lean boundary, not smuggled into the term.  Note what this does and does not cover: it
rejects a *statically known* bad argument; it cannot reject an `n` that is only known at run
time, because no type discipline can.

### 7.3 A checked entry, for run-time inputs  **[proposed, optional]**

`Valid1` is decidable, so the front end can also compile it as an ordinary `Term`
(`n ≥ 1 ∧ (n % 3 = 0 ∨ n % 3 = 1)` needs only `lean_int_dec_le` and `lean_int_emod`, both in the
catalogue) and generate

```
Tco04.test1.checked : int ⇒ option int      -- `none` outside the domain
```

That replaces "answers `0`" with "answers `none`" for inputs the caller cannot vouch for, and it
is the honest API to expose to hand-written JavaScript.  It should be opt-in: it costs a test per
entry, and it is only available when the precondition is decidable and compilable.

### 7.4 Why the precondition cannot move into `Term` itself

For completeness, the three reasons, in increasing order of severity:

1. **It is gone by the time we look.**  The front end reads LCNF, and LCNF has `◾` (§1.1).  A
   `Prop`-aware translator would have to work on the pre-erasure term, i.e. be a different
   compiler.
2. **`Term` is a runtime language.**  Adding `Prop` indices makes it dependent; the evaluator,
   the substitution algebra, the logical relation and the emitter all change shape, and the
   emitted JavaScript would have to erase them again anyway.
3. **It would not buy termination.**  The whole point of the counter is that termination holds
   *without* re-deriving Lean's argument.  Carrying `Valid1` into the term would mean re-proving
   `decreasing_by` inside the object language — which is precisely the certificate-carrying
   design (`TermC`) that this rewrite removes.

---

## 8. What the `-Expr.txt` for this module looks like  **[proposed]**

```
════ 🎯 test1
ƛ tco04Mutual ⬝ (lean_int_to_nat ♯0) ⬝ 0# ⬝ ♯0

════ 🎯 test2
ƛ tco04Mutual ⬝ (lean_int_to_nat ♯0) ⬝ 1# ⬝ ♯0

════ 📦 test1._mutual                       -- private: the rank is an argument
fix [counter] (tag : nat, x : int) {
  if lean_nat_dec_eq tag 0# then
    if lean_int_dec_eq x 1i then x
    else self⟨↓⟩ (1#, lean_int_sub x 1i)
  else
    if lean_int_dec_eq x 2i then x
    else self⟨↓⟩ (0#, lean_int_sub x 2i)
} exhausted { 0i }
```

with `self⟨↓⟩` the rendering of `selfCall .head (.here .nil)` — the descent marker is printed,
but there is nothing after it to print, because there is nothing a term may say about the rank.
That is the grammar's guarantee, visible in the dump.

---

## 9. Amendments to `TERM_ONE_GRAMMAR_ASSESSMENT.md`

From this walkthrough, five changes to the plan of record:

1. **F3, corrected and sharpened.**  For a `Nat`-carrier measure Lean emits
   `WellFounded.Nat.fix h body`, not `invImage`; `h` is argument 2 and is exactly the tag-
   dispatching rank the plan wants (verified for `Tco04`, `Tco03`, `Tco07`, `Nat.gcd`).  The
   extractor must match **both** forms, and must instantiate the packed binders before reading
   the measure (`Fusion02` shows a measure with free binders).  `scripts/dump-wf-measure.lean`
   is the probe.
2. **The rank is invisible to the body** (§3): `body`'s context is `ps ++ Γ`, not
   `rk.tys ++ ps ++ Γ`.
3. **The packed global is private** (§3): only wrappers are public, so no caller can choose a
   rank.
4. **Two new phase-2 items**: a computable deterministic `Term.step?` proved to implement `Step`,
   so terms can be `#eval`ed, and confluence (unique answers), so `Term.eval t = v` is provable
   and not only `Steps t v`.
5. **Two new phase-3 items**: generate, per entry point, the faithfulness theorem of §7.1 and the
   typed wrapper of §7.2 — the latter is the only place where an out-of-domain call can be
   rejected at elaboration time, and it should be part of the deliverable rather than left to the
   caller.
