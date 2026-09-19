# A `Valid`-guarded mutual pair over *data*: `ExamplesValidData`

**The question.**  `Tco04`'s guarded pair takes an `Int`.  What happens when the argument
is data instead — a list (itself inductive) of values of a *mutual* inductive — and the
precondition is partly a statement about the shape of that data ("even length", "the
third element's second field is `2`")?  Concretely:

1. is such a function still representable in `Term` under the plan of
   `TERM_ONE_GRAMMAR_ASSESSMENT.md`?
2. and if the evaluator is handed an input that fails `Valid1`/`Valid2`, does Lean reject
   it with a **type error**?

**See also** `TERM_PROOF_FIELDS.md`, which asks the next question: what if the *fields of
the data* are proofs?  (Short answer: the shapes count only the fields that survive
erasure, and the seven proof-carrying specimens of `ExamplesProofFields/` land in exactly
the same seven shapes as their erased twins.)

**The answers, up front.**

1. **Yes** — nothing in the data case breaks the design, and the front-end work it needs
   is work the plan already schedules.  But it *forces* three plan items that `Tco04`
   could have got away without, listed in §7: field-binding alternatives (F2), a rank for
   structurally recursive functions (F4), and the mutual-family `Ty`.
2. **No, not at the `Term` level, and that does not change because the argument is
   data.**  `Ty` is a language of runtime types with no `Prop` and no dependency, and the
   precondition is gone before the front end ever looks: `Valid1` and `Forest.marked`
   have **no IR declaration at all**, and the proof argument is `◾` at every call site
   (both verified in §2.2).  A bad forest is as well-typed an argument as a good one.
   What you get instead is four layers of rejection, §6 — and the data case adds one
   option that the `Int` case does not have: because part of this precondition is a
   statement about *shape*, it can be moved into the **type**, and then a bad input
   really is unconstructible.  That is done, and checked, in
   `ExamplesValidData/ForestRefined.lean`.

Statements are marked **[verified]** when they were checked against Lean 4.28.0 in this
tree, and **[proposed]** when they are design.  Read after
`TERM_ONE_GRAMMAR_ASSESSMENT.md` (the plan) and `TERM_TCO04_WALKTHROUGH.md` (the same
exercise for the numeric case).

---

## 1. The specimen  **[verified: it builds, `lake build ExamplesValidData`]**

`ExamplesValidData/ForestPair.lean` is `Tco04` transposed onto data:

```lean
mutual
  inductive Node   | node (label : Nat) (flag : Nat) (kids : Forest)
  inductive Forest | nil | cons (hd : Node) (tl : Forest)
end

def Forest.len      : Forest → Nat        -- structural
def Forest.tail     : Forest → Forest     -- `tail nil = nil`  ← the source of divergence
def Forest.headFlag : Forest → Nat        -- `0` when there is no head
def Forest.marked   : Forest → Prop       -- every node's flag is `2`   (structural, Prop-valued)

def Valid1 (xs : Forest) : Prop := xs.len ≥ 1 ∧ (xs.len % 3 = 0 ∨ xs.len % 3 = 1) ∧ xs.marked
def Valid2 (xs : Forest) : Prop := xs.len ≥ 2 ∧ (xs.len % 3 = 0 ∨ xs.len % 3 = 2) ∧ xs.marked

mutual
def test1 (xs : Forest) (h : Valid1 xs) : Nat :=
  if h1 : xs.len = 1 then 1
  else if hf : xs.headFlag = 2 then test2 xs.tail (test1_step h h1)
  else test1 (.cons (.node 0 0 .nil) xs) (absurd (Forest.headFlag_of_marked h.1 h.2.2) hf)
termination_by xs.len
decreasing_by …

def test2 (xs : Forest) (h : Valid2 xs) : Nat :=
  if h2 : xs.len = 2 then 2 else test1 xs.tail.tail (test2_step h h2)
termination_by xs.len
decreasing_by …
end
```

It is deliberately more demanding than the `Tco04` of the question, in three ways.

* **The data is a genuinely mutual inductive** — `Node` mentions `Forest` and `Forest`
  mentions `Node` — with an inductive list at the outer level, exactly as asked.
* **The precondition mixes two kinds of fact.**  `len % 3` is arithmetic on a *derived
  quantity* of the data, and it is what makes a base case reachable at all (drop one,
  drop two, stop at length one resp. two).  `marked` is a statement about the *fields of
  the elements*, and it is what kills the third branch.
* **Both failure modes are real.**  Miss the base case and the shrinking branches spin on
  the empty forest for ever (`tail nil = nil`), exactly as `Tco04`'s `n - 1` walks off
  into the negatives; hit an unmarked head and the growing branch prepends an unmarked
  node and diverges upward, exactly as `Tco07`'s `boom` triples its argument.  Both
  branches are genuinely present in the compiled code; both are dead on the domain.

The "third element's second field is `2`" of the question is a *positional* condition.
`marked` is the same kind of fact stated so that it survives the steps (dropping elements
from the front does not preserve "element number 3 is such and such", it shifts it); §6.4
says what changes if you insist on the positional form.

### 1.1 It runs, inside the domain  **[verified]**

```lean
theorem sample4_valid1 : Valid1 sample4        -- a marked forest of length 4
theorem test1_sample4 : test1 sample4 sample4_valid1 = 1 := by simp [test1, test2, …]
```

`sample4` (length 4) → `test2` (length 3) → `test1` (length 1) → `1`.

### 1.2 The erased twin diverges, outside it  **[verified]**

`test1Fuel`/`test2Fuel` in the same file are `test1`/`test2` with the proof argument
deleted — what erasure leaves, i.e. what today's JavaScript backend emits — run under a
fuel counter so the divergence is observable:

| input | `Valid1`? | `test1Fuel 1000` |
| :-- | :-- | :-- |
| `sample4` (len 4, marked) | yes | `some 1` |
| `sample5` (len 5, marked) | no — `5 % 3 = 2` | `some 1` |
| `sampleBadHead` (len 4, head flag `7`) | no — not marked | `none` (still running at 5000 too) |

The middle row is worth pausing on: **the precondition is not a termination test.**  An
input outside the domain may still stop; `Valid1` is what makes termination *provable*,
not what makes it happen.

---

## 2. What Lean hands the front end

### 2.1 The recursion is packed exactly like `Tco04`'s  **[verified]**

`lake env lean --run scripts/dump-wf-measure.lean ExamplesValidData.ForestPair ExamplesValidData.test1`:

```
ExamplesValidData.test1: WF recursion
  clique       : [ExamplesValidData.test1, ExamplesValidData.test2]
  packed decl  : ExamplesValidData.test1._mutual
  measure, via WellFounded.Nat.fix:
    fun x => PSum.casesOn x (fun _x => PSigma.casesOn _x fun xs h => xs.len)
                            (fun _x => PSigma.casesOn _x fun xs h => xs.len)
```

So the shape the plan expects is there unchanged: **one** `WellFounded.Nat.fix`, a single
`Nat` rank, and a `PSum` tag choosing which member is running.  Nothing about the
argument being data made Lean reach for a lexicographic order here.

One difference from `Tco04` matters: the measure is `xs.len`, i.e. **a call to another
compiled declaration**, not arithmetic on the argument.  `Forest.len` is itself recursive
— structurally, on argument `0` (`Lean.Elab.Structural.eqnInfoExt`, **[verified]**) — so
the rank of one recursion is computed by another recursion.  §7 turns that into an
obligation.

### 2.2 The precondition is already gone  **[verified]**

`lake env lean --run scripts/dump-lcnf-saveBase.lean ExamplesValidData.ForestPair ExamplesValidData.test1`:

```
def ExamplesValidData.test1 xs h : Nat :=
  let _x.1 := ExamplesValidData.Forest.len xs;
  let _x.3 := instDecidableEqNat _x.1 1;
  cases _x.3 : Nat
  | Decidable.isFalse h1 =>
    let _x.4 := ExamplesValidData.Forest.headFlag xs;
    let _x.6 := instDecidableEqNat _x.4 2;
    cases _x.6 : Nat
    | Decidable.isFalse hf =>
      let _x.9  := ExamplesValidData.Node.node 0 0 ExamplesValidData.Forest.nil;
      let _x.10 := ExamplesValidData.Forest.cons _x.9 xs;
      let _x.11 := ExamplesValidData.test1 _x.10 ◾;          -- ← the divergent branch, kept
      return _x.11
    | Decidable.isTrue hf =>
      cases xs : Nat
      | ExamplesValidData.Forest.nil            => return ExamplesValidData.test2 xs ◾
      | ExamplesValidData.Forest.cons hd.13 tl.14 => return ExamplesValidData.test2 tl.14 ◾
  | Decidable.isTrue h1 => return 1
```

Three things to read off it.

* `h` is `◾` at **every** call site.  The proof is not passed, not stored, not checked.
* `Forest.marked` and `Valid1` have **no IR declaration at all** — they are `Prop`-valued,
  so the compiler never produced code for them.  There is nothing for a front end to
  consult even if it wanted to.
* `Forest.tail` was inlined into a `cases`, and the alternative **binds the fields**
  (`hd.13`, `tl.14`).  That is finding F2 of the assessment, now on the critical path:
  today's `Alts` bind nothing, so this body is not writable at all until that changes.

### 2.3 The data is representable  **[verified: `ExamplesValidData/ForestTy.lean`]**

```lean
def nodeMember   : Ty.FamMember := .record ⟨.prim .nat, .prim .nat, [.self 1]⟩
def forestMember : Ty.FamMember := .ctors (.skip (.here ⟨.self 0, [.self 1]⟩ []))

example : famStronglyConnected [nodeMember, forestMember] = true := by decide
example : (LeanMutualRecFamily.ofMembers? [nodeMember, forestMember] 0).map famWf
            = some true := by decide
```

`Node` is member `0` and `Forest` member `1` of a `Ty.mutualRecursiveFamily`; the family
is strongly connected and inhabited, so `RTy.wf` accepts it and both types exist as
ordinary `Ty`s.  The type language needed no extension for this example.

---

## 3. The `Term`  **[proposed]**

Identical in shape to `Tco04`'s, and that is the point: the data-ness of the argument
changes the *types* in the term, not its structure.

```
ExamplesValidData.test1._mutual : nat ⇒ nat ⇒ forestTy ⇒ nat     -- rank, tag, argument
ExamplesValidData.test1         : forestTy ⇒ nat                 -- 🎯 public
ExamplesValidData.test2         : forestTy ⇒ nat                 -- 🎯 public
ExamplesValidData.Forest.len    : forestTy ⇒ nat                 -- 🎯 public, a `fix` of its own
```

```lean
/-- The clique, merged: `tag = 0` is `test1`, `tag = 1` is `test2`.
    Inside `body`: `♯0 = tag : nat`, `♯1 = xs : forestTy`.  The rank is *not* in scope. -/
def forestPairMutual {Sg : Sig} : Term Sg [] (Ty.nat ⇒ Ty.nat ⇒ forestTy ⇒ Ty.nat) :=
  Term.fix (rk := [.counter]) (ps := [Ty.nat, forestTy])
    (body :=
      .ite (tag == 0)
        -- test1
        (.ite (global Forest.len ⬝ ♯1 == 1)
          (.lit (.nat 1))
          (.ite (global Forest.headFlag ⬝ ♯1 == 2)
            (.selfCall .head (.here .nil) ⟨1, global Forest.tail ⬝ ♯1⟩)
            (.selfCall .head (.here .nil) ⟨0, cons (node 0 0 nil) ♯1⟩)))   -- the dead branch
        -- test2
        (.ite (global Forest.len ⬝ ♯1 == 2)
          (.lit (.nat 2))
          (.selfCall .head (.here .nil)
            ⟨0, global Forest.tail ⬝ (global Forest.tail ⬝ ♯1)⟩)))
    (exhausted := .lit (.nat 0))

/-- 🎯 `test1`. -/
def forestTest1 {Sg : Sig} : Term Sg [] (forestTy ⇒ Ty.nat) :=
  ƛ (forestPairMutual ⬝ (global Forest.len ⬝ ♯0) ⬝ .lit (.nat 0) ⬝ ♯0)
```

(with `==`, `⟨…⟩` and `global f ⬝ x` written informally for the extern calls and spines
the tree already has; the `cases`-with-field-binders form of `Forest.tail` is elided into
a call to the compiled `Forest.tail`, which is what LCNF itself does.)

Four observations.

* **The rank entry value is a call, not an expression in externs.**  `Tco04`'s rank was
  `lean_int_to_nat ♯0`; here it is `Forest.len ♯0`, an O(n) walk over the argument,
  performed once per *outermost* call — not per iteration.  That is the cost of a data
  measure and it is unavoidable: the measure Lean chose is a function of the data.
* **`Forest.len` must itself be a terminating `Term`.**  It is a structural recursion over
  a mutual family, so it is a `fix` whose rank comes from phase 1's `sizeOf` primitive
  (F4/B1) or phase 2's sub-value descent (F4/B2).  There is no escape hatch by which a
  measure could be an untranslated or non-terminating function; §7 records this as an
  obligation of the whitelist.
* **Sealing is unchanged.**  `Descends.here .nil` is still the only thing a recursive call
  says about the rank; the growing branch is written out and is still bounded, because
  what bounds it is the shape of the tree rather than any argument about forests.
* **`exhausted` is easy here** because the return type is `nat`.  Had the clique returned
  `forestTy`, the exhausted branch would need the canonical inhabitant of a *mutual
  family*, and `RTyWf`'s `famAllInhabited` is a `Bool`-valued fixed-point computation, not
  a witness — so building `Ty.defaultTerm` for a family means re-running that fixed point
  as a term constructor and proving it total.  §7 records that too.

---

## 4. Traces

Counter starts at the measure of the entry arguments and drops by one per self-call; a
self-call on a zero counter takes the `exhausted` branch.

**`sample4`, inside the domain** (`Valid1` holds):

| counter | tag | `xs` | |
| --: | --: | :-- | :-- |
| 4 | 0 | len 4, marked | `len ≠ 1`, head flag `2` → shrink |
| 3 | 1 | len 3 | `len ≠ 2` → drop two |
| 2 | 0 | len 1 | base → **`1`** |

Lean's answer is `1` **[verified in §1.1]**, and the counter was never the reason
anything stopped — it still had `2` left.

**`sample5`, outside the domain** (`5 % 3 = 2`):

| counter | tag | `xs` | |
| --: | --: | :-- | :-- |
| 5 | 0 | len 5 | shrink |
| 4 | 1 | len 4 | drop two |
| 3 | 0 | len 2 | shrink |
| 2 | 1 | len 1 | drop two → `nil` |
| 1 | 0 | len 0 | head flag `0 ≠ 2` → **grow** |
| 0 | 0 | len 1 | base → **`1`** |

The term answers `1`, which is what the erased twin answers **[verified in §1.2]**.  No
type error, no `exhausted`: the counter happened to be enough.

**`sampleBadHead`, outside the domain** (unmarked head):

| counter | tag | `xs` | |
| --: | --: | :-- | :-- |
| 4 | 0 | len 4, head flag `7` | grow |
| 3 | 0 | len 5, head flag `0` | grow |
| 2 | 0 | len 6 | grow |
| 1 | 0 | len 7 | grow |
| 0 | 0 | len 8 | grow → self-call on a **zero** counter |
| — | | | **`exhausted` → `0`** |

The erased twin runs for ever here **[verified in §1.2: no answer at fuel 5000]**; the
term stops and answers the canonical inhabitant.

### 4.1 Why the counter never interferes on the domain

Unchanged from the numeric case, and the proof does not care that the measure is computed
from data:

> **Rank domination.**  At every point of the reduction, `counter ≥ measure(current args)`.

At entry they are equal; at a call `counter' = counter − 1` and Lean's `decreasing_by`
gives `measure(next) ≤ measure(cur) − 1`, so `counter' ≥ measure(next)`.  Hence the
counter reaches `0` only when the measure already has, which on the domain cannot happen
before a base case.  The only property of the measure used is that it is a `Nat` and that
Lean proved it strictly decreases — `xs.len` qualifies exactly as `n.toNat` did.

---

## 5. So: is it allowed in `Term`?  **Yes — here is the gate-by-gate check**

| gate (§6 of the assessment) | `test1`/`test2` over forests |
| :-- | :-- |
| 1. safety — not `partial`, not `unsafe` | passes **[verified: `isUnsafe = false` for both]** |
| 2. effects — result type translates | passes: `Nat` |
| 3. not a partial/inductive/coinductive fixpoint | passes **[verified: no `PartialFixpoint` info for either]** |
| 4. recursion kind, positive match | passes: `Lean.Elab.WF.eqnInfoExt` present, measure recovered **[verified, §2.1]** |
| 4′. the measure itself translates | passes, but only because `Forest.len` is structural and gets a rank of its own (F4) |
| 5. mutual clique → one `fix` with a tag | as `Tco04`; Lean packed it that way itself **[verified, §2.1]** |
| 6. argument and result types are `Ty`s | passes: the family is well formed **[verified, §2.3]** |

Nothing here is a special case.  The data version needs strictly more of the plan than the
numeric version did, but no new *kind* of thing.

---

## 6. And the second question: is a bad input a type error?

### 6.1 At the `Term` level — no, and it cannot be

`forestTest1 : Term Sg [] (forestTy ⇒ Ty.nat)`.  `forestTy` is the type of **all**
forests: nothing in it records length, parity, or flags, because nothing in Lean's own
runtime type `Forest` does.  Applying the term to an unmarked forest of length 5 is as
well-typed as applying it to `sample4`.  The three reasons the precondition cannot be
pushed into `Term` are the ones of `TERM_TCO04_WALKTHROUGH.md` §7.4 and they are, if
anything, stronger here: the predicate is *gone* from LCNF (§2.2, `Forest.marked` has no
code at all), `Term` is a non-dependent runtime language, and carrying the predicate would
mean re-proving `decreasing_by` inside the object language — the certificate design this
rewrite removes.

### 6.2 At the Lean boundary — yes, for statically known inputs  **[verified]**

This is where the `Prop` still exists, and the error is exactly the one you want:

```lean
#check test1 sample5 (by refine ⟨by decide, by decide, ?_⟩; simp [sample5, sample4, Forest.marked])
-- error: Tactic `decide` proved that the proposition
--   sample5.len % 3 = 0 ∨ sample5.len % 3 = 1
-- is false

#check test1 sample4bad (by refine ⟨by decide, by decide, ?_⟩; simp [sample4bad, Forest.marked])
-- error: unsolved goals ⊢ False
```

The generated typed wrapper (`…run (xs : Forest) (h : Valid1 xs) : Nat`, assessment plan
item) is what exposes this to a user of the backend.  It rejects a *statically known* bad
argument and nothing else — no type discipline can reject a forest that is only known at
run time.

### 6.3 At run time — `none`, if you ask for the checked entry  **[verified]**

Unlike `Tco04`'s, this precondition is a predicate on data, and it is still decidable, so
the front end can compile it:

```lean
def Forest.markedB : Forest → Bool                     -- structural, Bool-valued
theorem Forest.marked_iff_markedB (xs) : xs.marked ↔ xs.markedB = true
def Valid1B (xs : Forest) : Bool := 1 ≤ xs.len && (xs.len % 3 == 0 || xs.len % 3 == 1) && xs.markedB
def test1Checked (xs : Forest) : Option Nat :=
  if h : Valid1B xs = true then some (test1 xs (valid1_of_valid1B h)) else none
```

```
test1Checked sample4       = some 1
test1Checked sample5       = none
test1Checked sample4bad    = none
test1Checked sampleBadHead = none
```

all four checked.  `Valid1B` compiles to ordinary LCNF (a join point and two calls,
**[verified]**), so `test1Checked : forestTy ⇒ option nat` is an ordinary `Term`, and this
is the honest API to hand to JavaScript callers.  The cost is one O(n) pass.

### 6.4 The option the data case adds: refine the type  **[verified: `ExamplesValidData/ForestRefined.lean`]**

An `Int` cannot be made to carry `n % 3 ≠ 2` in its type without leaving the runtime type
language.  Data can: a condition on the *shape* of a value can be turned into a *type*,
and then the bad value is not rejected — it cannot be built.

```lean
mutual
  inductive MNode   | node (label : Nat) (kids : MForest)         -- no flag field
  inductive MForest | nil | cons2 (a b : MNode) (rest : MForest)  -- elements in pairs
end

theorem MForest.len_erase_even (xs : MForest) : (MForest.erase xs).len % 2 = 0
theorem MForest.marked_erase   (xs : MForest) : (MForest.erase xs).marked
```

Both theorems are proved, not assumed: every `MForest` erases to a forest that is marked
and of even length.  The type is representable too — `mnodeMember`/`mforestMember` in
`ExamplesValidData/ForestTy.lean` form a well-formed family — and it is *smaller* at run
time: the flag field is gone, because a field that can hold one value carries no
information (`nodeMember` has 3 fields, `mnodeMember` has 2; `Forest.cons` has 2 fields,
`MForest.cons2` has 3 **[verified by `decide`]**).

What this buys and what it costs:

* **buys**: a function written against `MForest` needs no `marked`/parity precondition, so
  there is nothing to erase, and a caller cannot even *write* an unmarked or odd-length
  argument.  At the `Term` level the two types are different `Ty`s, so passing the wrong
  one is a genuine type error — the rejection asked for in the question, obtained
  honestly;
* **costs**: it is a different runtime representation, so callers holding a plain `Forest`
  must convert, and the conversion `Forest → Option MForest` is §6.3's run-time check
  again, just relocated.  And only *shape* conditions can move: "even length" and "every
  flag is `2`" can (as above), "the third element's flag is `2`" can (a type whose first
  three elements are separate fields, the third of a node type with the flag fixed), but
  `len % 3 ≠ 2` needs a three-element grouping too, and a condition that is not a
  statement about the shape of the value — say, "this closure returns `true` on the
  argument" — cannot move at all.

### 6.5 Summary of the four layers

| layer | `sample4` | `sample5` | `sampleBadHead` |
| :-- | :-- | :-- | :-- |
| Lean source, typed wrapper | `1` | does not elaborate **[verified]** | does not elaborate **[verified]** |
| erased twin / today's emitted JavaScript | `1` **[verified]** | `1` **[verified]** | diverges **[verified: no answer at fuel 5000]** |
| the proposed `Term` | `1` | `1` | terminates, `0` (exhausted) **[proposed]** |
| checked entry `test1Checked` | `some 1` | `none` | `none` — all **[verified]** |
| refined type `MForest` | argument constructible | unconstructible (odd length) | unconstructible (unmarked) **[verified]** |

---

## 7. What this specimen adds to the plan of record

Six items, all amendments to `TERM_ONE_GRAMMAR_ASSESSMENT.md` §9 rather than changes of
direction.

1. **F2 is a blocker, not a nicety.**  Every data example's LCNF binds constructor fields
   in its alternatives (§2.2).  Until `Alts`/`AltsT` take bodies in `fields ++ Γ`, no
   function over a user inductive is writable, guarded or not.
2. **The measure is subject to the whitelist.**  A rank entry value may be a call to a
   compiled declaration (here `Forest.len`).  That declaration must itself pass the
   classifier and become a terminating `Term`; a measure that is `partial`, opaque or
   untranslatable must fail the whole translation, not be trusted.  (This is the general
   form of F3's "synthesise a measure auxiliary": sometimes the auxiliary already exists.)
3. **So F4 is on the critical path for kind W too.**  The measure of a data recursion is
   normally a structural recursion, so shipping the well-founded half without a rank for
   the structural half translates nothing.  B1 (`sizeOf` primitive) or B2 (sub-value
   descent) must land in the same phase.
4. **`Ty.defaultTerm` must handle mutual families.**  `famAllInhabited` decides
   inhabitation with a `Bool` fixed point; the exhausted branch needs an actual value, so
   the term builder has to re-run that fixed point and be proved total for every well
   formed family — not only for primitives and single recursive types.
5. **Faithfulness statements are per entry point and carry the precondition.**  For this
   clique: `∀ xs (h : Valid1 xs), Steps (forestTest1 ⬝ ⌜xs⌝) ⌜test1 xs h⌝`, by well-founded
   induction on `xs.len` with rank domination (§4.1).  Outside the domain the term is
   *sound* (it stops) but is not Lean's function, because Lean has no function there.
6. **Document the refinement route.**  Where a precondition is a shape condition, offer
   the refined type (§6.4) as the recommended answer rather than the `Prop`; it is the only
   one of the four layers that turns a bad input into a compile-time error in the compiled
   world, and it makes the runtime representation smaller rather than larger.

---

## 8. The `-Expr.txt` for this module  **[proposed]**

```
════ 🎯 test1
ƛ test1._mutual ⬝ (Forest.len ♯0) ⬝ 0# ⬝ ♯0

════ 🎯 test2
ƛ test1._mutual ⬝ (Forest.len ♯0) ⬝ 1# ⬝ ♯0

════ 🎯 Forest.len
fix [subvalue forestTy] (xs : forestTy) {
  case xs of
    | nil          => 0#
    | cons hd, tl  => lean_nat_add (self⟨↓ tl⟩) 1#
} exhausted { 0# }

════ 📦 test1._mutual                        -- private: the rank is an argument
fix [counter] (tag : nat, xs : forestTy) {
  if lean_nat_dec_eq tag 0# then
    if lean_nat_dec_eq (Forest.len xs) 1# then 1#
    else if lean_nat_dec_eq (Forest.headFlag xs) 2# then self⟨↓⟩ (1#, Forest.tail xs)
    else self⟨↓⟩ (0#, cons (node 0# 0# nil) xs)
  else
    if lean_nat_dec_eq (Forest.len xs) 2# then 2#
    else self⟨↓⟩ (0#, Forest.tail (Forest.tail xs))
} exhausted { 0# }
```

`self⟨↓⟩` prints the descent marker with nothing after it — for the counter there is
nothing a term may say — while `self⟨↓ tl⟩` names the field the structural descent is on,
which *is* something the term says, and which the type of the constructor makes checkable.

---

## 9. Files

| file | what it is |
| :-- | :-- |
| `ExamplesValidData/ForestPair.lean` | the specimen: mutual inductive data, the two `Valid`s, the guarded pair, the erased twin, the checked entry, and the samples — builds, no `sorry` |
| `ExamplesValidData/ForestRefined.lean` | the refined data type and the two theorems that its erasure satisfies the shape half of `Valid1` |
| `ExamplesValidData/ForestTy.lean` | both families written as `LakeJs.Ty`s, with their well-formedness checked by `decide` |
| `scripts/dump-wf-measure.lean`, `scripts/dump-lcnf-saveBase.lean` | the probes used for §2 |
