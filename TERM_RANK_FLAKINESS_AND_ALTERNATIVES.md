# The rank-based `Term.fix` is flaky — evidence, diagnosis, and the designs worth trying

This note answers three questions:

1. is the current rank-based `Term.fix` approach flaky, and in what precise sense?
2. how can it be improved without throwing the design away?
3. what *other* designs are there for `LakeJs/Expr.lean`'s recursion construct?

Everything in §1–§3 is a statement about this tree, with file and line references, and the
two experiments of §3 were run here and are committed under `RankFlakiness/`.  §4 onwards
is design discussion and is marked as such.

---

## 0. Summary

The grammar delivers exactly one of the two properties a backend needs, and the split is
sharper than the existing notes admit:

| property | who guarantees it | status |
| :-- | :-- | :-- |
| **the emitted term terminates** | the shape of `Term.fix` — the evaluator is `Nat.rec` on the rank, and `Term.selfCall` has no rank slot | **by construction**, kernel-checked when `<Module>Program.lean` elaborates |
| **the emitted term computes the Lean function it came from** | `LakeJs/FrontEnd.lean`, by a stack of syntactic heuristics | **unchecked**, and it fails **silently** |

Termination by construction was bought by making the rank part of the syntax.  The price
is that the *whole* correctness burden moved into the choice of that rank — and the
failure mode of a wrong rank is not an error, not an exception, not an `Option.none`: it
is the `exhausted` branch answering `Ty.dflt`, i.e. **a wrong number**.  A backend that
silently miscompiles is worse than one that refuses.

`RankFlakiness/AckOpaqueArgCheck.lean` makes this concrete and machine-checked: a
one-token change to Ackermann that Lean accepts with the same `termination_by` produces a
term the driver reports as `checked` and which computes a different function
(`ackOpaque_term_wrong_at_one_one`, proved by `native_decide`).

The recommendation, in one line: **stop asking the rank to be an iteration bound computed
by the front end, and make it a measure whose descent is checked — dynamically by the
evaluator, statically by a verification condition the emitted program carries.**  Details
in §5–§7; the concrete proposal is §6.4 (lexicographic, guarded `fix`), the migration is
§8.

---

## 1. What the rank actually has to be, and what the front end actually does

### 1.1 The semantics: the rank bounds the *height of the self-call tree*

`LakeJs/Reduce.lean` evaluates `Term.fix ps rank body exhausted` as `nIter`, which is
`Nat.rec` on the value of `rank`: at `0` it answers `exhausted`, and at `k + 1` it
evaluates `body` with the self-reference bound to `nIter … k`.  So the obligation on the
rank is

> at every argument tuple the recursion is entered with, the value of `rank` is at least
> the **height** of the tree of self calls of that recursion that the body performs.

That is the real proof obligation.  It is weaker than "number of iterations" (a chain of
sibling calls costs one level, not one each) and stronger than "the measure decreases
somewhere".  Nothing in the tree states it, and nothing checks it.

### 1.2 What the front end emits

`LakeJs/FrontEnd.lean` derives it from Lean's own termination data in six steps, **each of
which is a guess** that can be wrong without anyone noticing:

| # | step | where | what can go wrong |
| :-- | :-- | :-- | :-- |
| 1 | read the measure out of the compiler-generated packed declaration (`invImage`, `WellFounded.Nat.fix`, `PSigma.casesOn`, `Prod.mk`) | `findMeasure?`, `peelMeasure`, `measureParts` (≈ l. 1685–1726) | pattern-matches on internals of Lean's well-founded elaboration; a different packing shape is refused (good) or read wrongly (bad) |
| 2 | pair the binders the measure is written against with the parameters that survive erasure, **by user name, falling back to position** | `mkMeasureNames` (≈ l. 1793–1840) | a rename, a shadowed binder, a specialization with a different parameter list ⇒ the rank reads a *different parameter* — silently |
| 3 | transcribe each component into a `Src` | `transMeasure` (≈ l. 1728–1790) | only a fixed table of operations; anything else is refused (see §3.2) |
| 4 | split the parameters into one nesting level per measure component | `levelsOfComponents` / `dupLevelsOfComponents` (≈ l. 1846–1895) | purely positional: "component `i` owns the parameters it is the last to mention".  Reordering parameters changes the emitted shape or refuses the function |
| 5 | decide, for each self call, **which level it belongs to** | `mkSelfCall` / `mkSelfCallDup` / `levelDelta` / `linOf?` (l. 1044–1140) | a syntactic linear normal form over `+`, `-`, `*`-by-a-constant.  When it cannot tell, it **defaults** (`target.getD (fn.levels.size - 1)`, and `same = false` when an argument has no normal form).  This is the bug demonstrated in §3.1 |
| 6 | rank = the component **plus one** (`Term.rankSucc`, applied to every rank by the renderer at l. 266); for a structural mutual clique, rank = `clique.size * measure` | `cliqueMeasures`, ≈ l. 2190 | "+1" is right only if the measure strictly decreases along *every path the erased body can execute*; the `clique.size` factor is justified by a prose comment ("a chain of such calls cannot enter the same member twice"), not by a proof |

Add to that the point `TERM_RANK_VS_ACC.md` §3.1 makes in the *other* direction: after
erasure the call relation is **larger** than the one Lean proved decreasing, because the
`Prop` arguments that ruled out branches are gone (`Tco07.boom`).  The existing note treats
this as harmless — "an over-generous but still terminating loop is exactly as
terminating" — and for termination it is.  For *faithfulness* it is not automatically
harmless: it means the decrease property the rank relies on is a property of the **erased**
body, restricted to reachable states, which Lean never proved and the front end never
checks.

### 1.3 The evidence that exists today

* one general theorem, `ackTerm_eq` in `LakeJs/Examples/Ackermann.lean`, about a
  **hand-written** term of the Ackermann shape — not about anything the front end emits;
* nine `…Check.lean` files against twenty-three generated `…Program.lean` files, which run
  *some* emitted terms against their Lean originals on small finite ranges of inputs with
  `native_decide`;
* the driver's `checked` verdict, which means only that the generated Lean source
  *elaborates* — i.e. that the term is well-typed and therefore terminating.  It says
  nothing about which function it computes.

So for most emitted declarations there is no faithfulness evidence at all, and for the
rest it is sampling.  §3.1 shows sampling is not enough: the counterexample there agrees
with Lean on the whole `m = 0` row and on `(1,0)`.

---

## 2. The three obligations, and where each should be discharged

It helps to name them separately, because the current design conflates the last two.

* **(T) well-typed** — the emitted program is a `Term`.  Discharged by Lean's kernel when
  `<Module>Program.lean` elaborates.  This works today and should be kept.
* **(S) terminating** — the emitted program has no infinite reduction.  Discharged by the
  shape of the grammar.  This works today and should be kept.
* **(F) faithful** — the emitted program computes the Lean function.  Discharged today by
  *hope*: a chain of syntactic guesses in the front end, with a silent failure mode.

The whole point of the redesign below is to move as much of (F) as possible into something
that is *checked*, and to make whatever remains **fail loudly**.

Note the asymmetry the current design creates: because (S) is structural, a bug in the
front end cannot produce a non-terminating program — it produces a *wrong* program
instead.  Errors were traded for silence.  A design in which a rank error produces a
refusal, or an observable "stuck" value, is strictly better even if nothing else changes.

---

## 3. Two experiments, run in this tree

The `RankFlakiness/` library (declared in `lakefile.toml`) contains them.  Reproduce with

```
lake build lean-to-js-backend LakeJs RankFlakiness
lake env ./.lake/build/bin/lean-to-js-backend RankFlakiness/AckOpaqueArg.lean
lake env ./.lake/build/bin/lean-to-js-backend --check RankFlakiness/AckMeasureHelper.lean
```

### 3.1 A silent miscompilation (`RankFlakiness/AckOpaqueArg.lean`)

Ackermann, verbatim from `SnapshotsMy/Tco08.lean`, with **one change**: the first argument
of the inner recursive call — the one that must stay equal to `m + 1` for the recursion to
be the *inner* one — is written `2 * (m + 1) - (m + 1)`.

```lean
def ackOpaque : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ackOpaque m 1
  | m + 1, n + 1 => ackOpaque m (ackOpaque (2 * (m + 1) - (m + 1)) n)
termination_by m n => (m, n)
decreasing_by all_goals omega
```

Lean accepts it with the same measure.  The driver accepts it too:

```
RankFlakiness/AckOpaqueArg.lean -> RankFlakiness/AckOpaqueArgProgram.lean (1 declarations, checked)
```

But in the emitted tree the inner call is no longer `self0` (the `n`-ranked recursion), it
is `self1` — the **outer**, `m`-ranked one:

```
--     let ♯ := (self1⟨↓⟩(♯0) ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯5) ⬝ 1#));
```

because `linOf?` has no normal form for `2 * (m + 1) - (m + 1)`, so `mkSelfCall` concluded
that the outer argument changed.  The outer rank is `m + 1`; the inner loop needs many more
than `m + 1` levels; the `exhausted` branch fires and answers `0`.  The result is a term
that is well-typed, terminating, "checked" — and wrong:

```lean
theorem ackOpaque_term_wrong_at_one_one : runAckOpaque 1 1 ≠ ackOpaque 1 1 := by native_decide
theorem ackOpaque_term_wrong_often : (disagreements 4).length = 11 := by native_decide
theorem ackOpaque_term_right_at_one_zero : runAckOpaque 1 0 = ackOpaque 1 0 := by native_decide
```

Eleven of the sixteen inputs of the 4 × 4 square disagree — and the five that agree are
exactly the ones a small smoke test is most likely to pick (`m = 0`, and `(1,0)`).

This is the sharpest possible form of the user's observation: *the front end does not find
the rank of the function, it recognises a shape.*  `SnapshotsMy/Tco08Program.lean` is not
"Ackermann compiled", it is "the shape the classifier expects, compiled".

### 3.2 A refusal caused by a cosmetic change (`RankFlakiness/AckMeasureHelper.lean`)

Same Ackermann, with the first measure component written through an identity definition:

```lean
def idNat (x : Nat) : Nat := x
…
termination_by m n => (idNat m, n)
```

```
`ackId` was not translated: the measure mentions `idNat`, which the front end cannot
transcribe into a rank
```

The measure is the same measure.  `transMeasure`'s table does not contain `idNat`, and it
does not unfold definitions, so a function that is in every respect in the language is
refused.  Refusal is the *good* failure mode — but it shows how narrow the accepted set
is, and it is one step away from §3.1: had `idNat` been in the table with a form `linOf?`
cannot read, the same edit would have produced a wrong program instead of a refusal.

---

## 4. Why the trouble is concentrated in the rank, and not elsewhere

Worth stating, because it tells you what to change and what to leave alone.

* The **value fragment** of the translation (literals, `let`, join points, `case`,
  externs, calls of other declarations) is a transcription: each LCNF construct has one
  counterpart and a wrong translation would generally not type-check.
* The **rank** is the only part that is a *derivation*: a number the source does not
  contain, computed by analysing the source's termination argument, whose wrongness is
  invisible to the type system.
* And the rank is asked for something Lean never proved.  Lean proved "this measure
  decreases at each recursive call, under these `Prop` hypotheses".  The grammar asks for
  "this number bounds the height of the self-call tree of the *erased* body".  Bridging
  those two requires (a) the erased branches to be dead or to also decrease, and (b) a
  correct assignment of each call to a nesting level.  The front end asserts both.

Every design below is judged on one question: **does it ask the front end for something
Lean already proved?**

---

## 5. Improvements that keep the rank (cheap, do them regardless)

### 5.1 Never default — refuse

Two defaults in `mkSelfCall`/`mkSelfCallDup` turn ignorance into a wrong program:

```lean
let t := target.getD (fn.levels.size - 1)          -- "assume it is the innermost level"
let same := match a.nf with | some (some b, 0) => b == p.1 | _ => false   -- "no normal form ⇒ changed"
```

Both should be `throwError`.  §3.1 becomes a refusal, immediately, with no grammar change.
Similarly `mkMeasureNames`'s positional fallback should be dropped, or gated behind an
explicit flag.  Expect a handful of corpus functions to start failing; that is information,
not regression.

### 5.2 Make exhaustion observable, and check every emitted recursion

Add an instrumented evaluator — `evalDbg : … → τ.den × Bool`, the flag saying whether any
`exhausted` branch was reached — and have the test runner assert the flag is `false` over
the test domain.  Then auto-generate a `…Check.lean` for **every** translated recursive
declaration (boundary values plus a pseudorandom sample), instead of the nine hand-written
ones.  This does not prove anything, but it converts the silent failure of §3.1 into a red
build in seconds, and it is a few hours of work.

### 5.3 Emit the rank decision, and let it be reviewed

Each `<Module>Program.lean` should record, in its header, the measure it read, the level it
assigned to each self call, and *why* (`argument unchanged`, `linear delta 0`, `default`).
A `default` appearing anywhere is a review flag.  Cheap, and it makes the guesses auditable
instead of buried.

### 5.4 Check the rank *on the term*, not on the Lean source (the real fix)

This is the one that actually discharges obligation (F)'s termination half.  Define, inside
`LakeJs`, a predicate on terms:

```lean
/-- Every self call in the body of a `fix` is made at a strictly smaller rank. -/
def Descends : Term Sg Γ Ρ τ → Prop
```

realised as a verification-condition generator: walk the body of each `fix`, collect the
path condition of each `selfCall` occurrence (the `ite`/`caseTag` tests that guard it), and
require

```
pathCondition → rank[args := actuals] < rank[args := params]
```

with the whole thing quantified over the environment.  Then prove, **once**, the generic
metatheorem

```lean
theorem eval_not_exhausted (h : Descends t) : … -- the `exhausted` branch is never taken
```

and its corollary: under `Descends`, `fix` satisfies the unrolling equation it was meant to
satisfy.  The front end then *emits the proof* (`by decide` / an `omega`-generated term) in
the generated `Program.lean`.  If the front end's level assignment is wrong, the generated
file **does not elaborate** — the failure moves from runtime silence to compile time.

Two honest caveats:

* the VCs for the current corpus are linear arithmetic over `Nat`/`Int` plus `structSize`,
  so `omega`/`decide` can discharge most; a residual obligation can be left as an explicit
  `sorry`-free hole the driver reports;
* it will **reject `Tco07.boom`** and the other "terminates only because of an erased
  proof" functions, because after erasure the call `boom (3 * n)` genuinely does not
  decrease `n`.  That is the correct answer for a checked design: either such functions are
  refused, or their `Prop` arguments must be retained as checkable refinements (the
  direction `TERM_PROOF_FIELDS.md` / `ExamplesProofFields/` already explores), or they are
  accepted with the guarded semantics of §6.2, where the non-decreasing branch simply gets
  stuck at run time instead of returning a wrong number.

---

## 6. Other designs for `Term.lean`

Five are worth considering; the recommendation is the combination 6.2 + 6.3, i.e. §6.4.

### 6.1 Structural recursion as *syntax*, separate from the arithmetic path

Today a structurally recursive function — the majority of the corpus (🟦 S in the task's
table) — takes the same arithmetic route as a well-founded one: rank
`structSize x + 1` or `n + 1`, then the same level-assignment machinery.  That is
needlessly fragile, because structural descent needs no numbers at all.

Add a second recursion constructor whose descent is a **scoping** condition:

```lean
/-- Structural recursion: the self call may only be applied to a variable that a `caseTag`
    bound as a *field* of the recursion subject (or of something already smaller). -/
| fixStruct : (ps : List Ty) → (subject : Fin ps.length) →
    (body : Term Sg (ps ++ Γ) (⟨ps, τ, subject⟩ :: Ρ) τ) → Term Sg Γ Ρ (Ty.arrows ps τ)
```

with the context carrying a "smaller than the subject" marker that only `caseTag` on the
subject introduces, and `selfCall` requiring the new subject to be a marked variable.  This
is Coq's guard condition, but *in the types*, so Lean's kernel checks it when the generated
program elaborates.  Consequences:

* for every 🟦 S function the front end emits **no measure at all** — nothing to guess, and
  no `clique.size` fudge factor for structural cliques (the merged clique's calls are
  either on a marked field, or on the same value with a decreasing member index, which the
  marker can carry as a second, finite component);
* the metatheory is the easy half: SN for `fixStruct` is the recursor of the data layout;
* the remaining arithmetic machinery is used only where it is unavoidable, 🟥 W.

Cost: the context needs the marker, and `Subst`/`Reduce`/`Progress` need the extra index.
This is the single highest value-per-line change in the list, because it removes the
majority of the corpus — every 🟦 S entry of the task's table — from the flaky path
entirely.

### 6.2 Guarded recursion: check the descent at the call, do not count iterations

Change what the rank *means*.  Instead of "a number that is decremented once per level",
let `fix` carry a **measure** and let the evaluator recompute it at each self call:

```lean
| fixM : (ps : List Ty) →
    (measure : Term Sg (ps ++ Γ) Ρ (.prim .nat)) →
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) →
    (stuck : Term Sg (ps ++ Γ) Ρ τ) →
    Term Sg Γ Ρ (Ty.arrows ps τ)
```

Semantics: enter with `bound := measure[args]`; at a self call with actuals `a`, compute
`m' := measure[a]`; if `m' < bound` recurse with `bound := m'`, otherwise answer `stuck`.
Still `Nat.rec` on `bound`, so **terminating by construction exactly as before** — the
metatheory of `SN.lean` changes in one case, not in kind.

What this buys:

* the front end's obligation becomes *precisely what Lean's `decreasing_by` proved*: the
  measure decreases at each call.  No iteration bound, no height-of-call-tree reasoning, no
  `+1`, no `clique.size` factor;
* nested calls (`ack m (ack (m+1) n)`) and merged cliques need no special argument;
* a wrong measure can no longer be "too small": it can only fail to decrease, which is
  *observable* (`stuck`), and which §5.2's instrumentation catches on the first test.

Cost: the measure is evaluated once per call rather than once per entry.  In emitted code
that is a few arithmetic ops per iteration, and §5.4's static check — now an
**optimisation**, not a correctness requirement — licenses removing them.  That is the
right dependency direction: a bug in the static analysis costs performance, not
correctness.

### 6.3 A lexicographic rank, so that the ack currying disappears

Replace the single `Nat` by a fixed-length vector compared lexicographically:

```lean
| fixLex : (ps : List Ty) → (k : Nat) →
    (measure : Spine Sg (ps ++ Γ) Ρ (List.replicate k (.prim .nat))) → …
```

`Nat^k` under the lexicographic order is well-founded, and — crucially for this project —
the eliminator is still an ordinary nested `Nat.rec`, so the term stays kernel-computable
and the SN proof stays elementary (induction on the first component, inner induction on the
rest).

This removes, in one stroke, steps 4 and 5 of the table in §1.2 — `levelsOfComponents`,
`dupLevelsOfComponents`, `linOf?`, `levelDelta`, `mkSelfCall`, `mkSelfCallDup`,
`dupParamName`, the two nest shapes, and the two defaults.  Ackermann becomes **one**
`fix` with `ps = [nat, nat]` and `measure = [m, n]`, transcribed verbatim from
`termination_by m n => (m, n)`; the self call supplies both arguments and the evaluator
compares.  §3.1's edit then cannot change anything, because no analysis of the call's
arguments is performed at all.

It also fixes a case the current design fudges: a structural clique in which a member calls
another *without* descending (`cata` → `cataMap`, `RecursionSchemes01`).  Today that is paid
for by multiplying the rank by `clique.size` on the strength of a comment.  With a
lexicographic rank it is `[size, phase]`, where `phase` is the member's position in a
topological order of the non-descending calls — which exists precisely because Lean
accepted the clique.

### 6.4 Recommended: `fixLex` + guarded descent

Combine 6.2 and 6.3: `fix` carries a **vector of measure terms**, the evaluator recomputes
the vector at each self call and recurses only on a strict lexicographic decrease.  With
§6.1 for structural functions, the grammar then has exactly two recursion constructors, and
the front end's entire termination job is:

| kind | what the front end must produce | can it be wrong silently? |
| :-- | :-- | :-- |
| 🟦 S | which parameter is the subject | no — a wrong subject is a **type error** in the generated program |
| 🟥 W | the components of `termination_by`, transcribed | no — a wrong measure can only produce `stuck`, which is **observable** |

Both failure modes are loud.  That is the property the current design lacks, and it is the
reason to prefer this over any amount of hardening of §5.

### 6.5 Designs considered and not recommended

* **Carry `Acc`/`WellFounded`** (`fixAcc`).  Already argued against in
  `TERM_RANK_VS_ACC.md` §3, and those arguments stand: the evidence is erased before LCNF,
  and a term carrying Lean-level relations and proofs is no longer first-order, so it
  cannot be printed into `-Expr.txt`, re-elaborated, or compared.  Worth re-reading as the
  statement of what *cannot* be recovered after erasure.
* **Sized types / type-based termination** — put a size index in `Ty` and let the self call
  require a strictly smaller index.  This is the most elegant answer (termination *and*
  descent are typing), and it generalises §6.1 to the well-founded case.  It is also a
  rewrite of `Ty`, `RTy`, `Layout`, `Subst`, `Den` and the metatheory, plus a size-inference
  problem in the front end for measures like `101 - n`.  Not worth it now; worth knowing it
  is where §6.1 leads if the structural case is pushed further.
* **Two-level: raw term + separate certificate.**  Drop the rank from the grammar, accept
  possibly-divergent raw terms, and pair each program with a machine-checked termination
  certificate (`Program := { t : RawTerm // Descends t }`).  This is `CertGen.lean`'s
  original idea, and §5.4 is the same VC checker; the difference is only whether the
  certificate lives inside the type of `Term` or beside it.  Keeping it inside — as today —
  is better for this project, because the printed `-Expr.txt` then carries its own
  guarantee.
* **Clocked/guarded type theory (tick modalities).**  Correct, well-studied, and far too
  large a change for a first-order monomorphic backend.

---

## 7. Comparison

| design | (S) terminating | (F) faithful | front end must produce | failure mode | metatheory cost |
| :-- | :-- | :-- | :-- | :-- | :-- |
| today: counted rank + level nest | by construction | unchecked | an iteration bound **and** a level per call | **silent wrong answer** | none (done) |
| §5.1–5.3 hardening | by construction | unchecked, but audited | same | refusal / red test | none |
| §5.4 VC-checked rank | by construction | descent checked | same, plus a proof | compile error | one generic theorem |
| §6.1 `fixStruct` | by construction | descent by typing (S only) | the subject | type error | recursor per layout |
| §6.2 guarded measure | by construction | descent checked at run time | a decreasing measure | observable `stuck` | one case of SN reproved |
| §6.3 lexicographic rank | by construction | unchecked, but nothing to guess | the measure components | as above | nested `Nat.rec` |
| **§6.4 = 6.1 + 6.2 + 6.3** | by construction | descent checked; statically checkable | subject, or measure components | type error / observable `stuck` | the two above |

---

## 8. A migration that keeps the corpus green at every step

1. **Instrument and audit** (§5.2, §5.3).  Auto-generate a differential check for every
   emitted recursive declaration; assert no `exhausted` branch is reached.  Expect §3.1's
   class of bug to surface elsewhere in the corpus — that is the point.
2. **Remove the defaults** (§5.1).  Turn every "assume innermost" into a refusal.  Record
   which corpus functions are lost.
3. **`fixLex`** (§6.3).  One constructor, vector measure, verbatim transcription; delete
   `levelsOfComponents`, `dupLevelsOfComponents`, `linOf?`, `levelDelta`, `mkSelfCall`,
   `mkSelfCallDup`.  Regenerate the corpus; the functions lost at step 2 should come back,
   and `RankFlakiness/AckOpaqueArg.lean` should now be translated *correctly* (its check
   file flips from "wrong" to "agrees", which is the acceptance criterion).
4. **Guarded semantics** (§6.2).  Recompute the measure at each self call; rename
   `exhausted` to `stuck` and make reaching it observable in the debug evaluator.  Re-prove
   the one SN case.  Acceptance: every corpus check still passes and no `stuck` is reached.
5. **`fixStruct`** (§6.1).  Structural functions stop carrying a measure.  Acceptance:
   every 🟦 S function of the task's table translates with no arithmetic in its recursion,
   and a wrong subject fails to elaborate (test it by perturbing one on purpose).
6. **VC checker + generic theorem** (§5.4).  The generated program carries `Descends`;
   the emitter may then drop the runtime measure checks.  Acceptance: the theorem is
   `sorry`-free, and every corpus program elaborates with its proof.
7. **Translation validation** (the remaining half of (F)).  For each translated
   declaration, prove — not sample — `eval(term) args = f args` by induction, using the
   equation lemmas Lean already generates for `f` (`f.eq_def`, the `WF.eqns`).  For the
   fragment this backend accepts, those proofs are highly schematic and can be emitted
   alongside the program.  This is the only thing that would make "the backend is correct"
   a theorem rather than a test suite.

Steps 1–2 are days, 3–5 are the real work, 6–7 are research-shaped but well defined.

---

## 9. Answers to the two questions, stated plainly

**Is the current approach flaky?**  Yes, and not marginally: `RankFlakiness/` contains a
one-token perturbation of the project's own Ackermann snapshot that the backend compiles,
reports as `checked`, and gets wrong on 11 of 16 small inputs, with a machine-checked proof
of the disagreement.  The cause is structural, not a bug to patch: the grammar demands a
number nobody verifies, and the front end derives it by recognising shapes.

**Can it be improved, and are there other designs?**  Yes to both.  Without touching the
grammar, refusing instead of defaulting and instrumenting the `exhausted` branch converts
silent wrongness into loud failure (§5.1–5.3), and a verification condition checked on the
emitted term converts it into a compile error (§5.4).  With the grammar, the combination of
a structural constructor whose descent is a typing condition, a lexicographic measure
transcribed verbatim, and a guarded evaluator that checks the descent at each call (§6.4)
removes the guessing altogether: the front end is then only ever asked for things Lean has
already proved.
