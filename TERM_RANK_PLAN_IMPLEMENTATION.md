# What of `TERM_RANK_FLAKINESS_AND_ALTERNATIVES.md` is implemented

This note is the status of the migration that document's §8 lays out.  It says, step by
step, what the tree now contains, what was done differently from the sketch and why, and
what is deliberately left undone.  Everything claimed as done builds: `lake build`, plus
`lake build SnapshotsPBOPure SnapshotsMy SnapshotsPBOPartial RankFlakiness` for the
generated corpus, and there is no `sorry` in the library.

---

## The short version

The recommendation of §6.4 — a **lexicographic measure with guarded descent** — is
implemented end to end: in the grammar, in the evaluator, in the metatheory, in the worked
examples, in the front end, and in the regenerated corpus.  The counted rank is gone, and
with it every one of the six guessing steps that §1.2 tabulated.

The static verification-condition machinery of §5.4 is now in the tree as well: the
condition, its generic consequences, a rule calculus that reduces it to arithmetic, and
the condition discharged on the worked examples — see step 6 below.  The one item of §6.4
that remains unimplemented is `fixStruct` (§6.1, a second recursion constructor whose
descent is a typing condition), described at the end with the reason.

---

## Step 1 — instrument and audit (§5.2, §5.3)

**Done, in the form that fits the new semantics.**

* §5.3, *emit the measure decision and let it be reviewed*: every generated
  `<Module>Program.lean` now records, above each declaration's tree, the measure the front
  end used and where it came from.  For example, `SnapshotsPBOPure/Tco01Program.lean`:

  ```
  -- ════ 🎯 test : (fn nat nat)
  --      measure: structural recursion, on the argument Lean recorded (position 0); 1 component: [ ♯0 ]
  ```

  and `SnapshotsPBOPure/Tco04Program.lean`, for the merged clique:

  ```
  --      measure: mutual clique of 2 members; 2 components: [ …, … ] — the measure of the
  --      member the tag selects, then its phase
  ```

  There is nothing left to record about *level assignment*, because there are no levels;
  and there is no `default` to flag, because nothing defaults any more (see step 2).

* §5.2, *make exhaustion observable, and check every emitted recursion*: the driver now
  writes, beside the program, a `<Module>AutoCheck.lean` holding a **differential check
  for every translated declaration whose arguments and result are `Nat`, `Int` or `Bool`**
  — the emitted term and the Lean declaration it came from, run side by side over a sample
  of inputs.  Building the snapshot libraries runs them.  Eleven such files are in the tree
  (`SnapshotsPBOPure/Tco01AutoCheck.lean`, `SnapshotsMy/Tco08AutoCheck.lean`, …), and they
  all pass.

  This is the *purpose* of the instrumented `evalDbg` the plan sketched — a measure the
  front end read wrongly becomes a red build in seconds — rather than its letter.  An
  `evalDbg : … → τ.den × Bool` is not a small change under the current semantics: the
  evaluator is compositional and higher-order (`Term.lam` evaluates to a Lean function),
  so a flag saying "a `stuck` branch was reached" cannot be threaded out of a value
  without putting the whole evaluator in a writer monad and changing what every type
  denotes.  A differential check catches every `stuck` that changes an answer, which is
  every `stuck` that matters, and costs nothing in the semantics.

## Step 2 — remove the defaults (§5.1)

**Done, by deletion rather than by refusal.**  The two silent defaults were
`mkSelfCall`'s and `mkSelfCallDup`'s `target.getD …`: the front end guessing which level
of a nest a self call belonged to.  With one recursion per declaration there is no level
to guess, so `linOf?`, `Lin`, `levelDelta`, `mkSelfCallDup`, `levelsOfComponents`,
`dupLevelsOfComponents`, `dupParamName`, `mentions`, `LevelInfo` and
`Src.renameVars` are gone from `LakeJs/FrontEnd.lean`, and `mkSelfCall` is four lines that
check the arity and hand over the arguments.

No corpus function was lost: every module of `scripts/corpus-modules.txt` still translates,
and no generated program reports a declaration as `not translated:`.

## Step 3 — `fixLex` (§6.3)

**Done.**  The constructor is

```lean
| fix : (ps : List Ty) → (k : Nat) →
    (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k)) →
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) →
    (stuck : Term Sg (ps ++ Γ) Ρ τ) →
    Term Sg Γ Ρ (Ty.arrows ps τ)
```

`LakeJs/Lex.lean` supplies the lexicographic order on `NatVec k`, its well-foundedness,
and a kernel-computable runner, so a term still reduces by `rfl` inside the kernel.

The front end emits **one** `fix` per declaration, with the `termination_by` components
transcribed verbatim and in order; Ackermann is `fix (nat nat) measure [ ♯0, ♯1 ]`, and
`LakeJs/Examples/Ackermann.lean` is the same recursion written by hand and proved equal to
Lean's `ack`.

**The acceptance criterion the plan named for this step is met and machine-checked.**
`RankFlakiness/AckOpaqueArg.lean` — Ackermann with the unchanged argument of the inner
call written `2 * (m + 1) - (m + 1)` — used to be translated into a term that computed a
different function on 11 of the 16 inputs of the 4 × 4 square, with the driver reporting
`checked`.  It is now translated correctly:
`RankFlakiness.AckOpaqueArgCheck.ackOpaque_term_agrees` says the disagreement list is
empty.  The old counterexample statements are kept, commented out, in the same file.

A **mutual clique** is one `fix` over the tag and the parameters of every member, with the
two-component measure `[measure of the member the tag selects, phase]` — the `[size,
phase]` of §6.3.  The phase counts down along the order Lean records the members in, which
is what a member-to-member call that does not descend on the measure (`cata` → `cataMap`)
descends on.  The `clique.size` fudge factor, which was justified by a comment rather than
a proof, is gone.

## Step 4 — guarded semantics (§6.2)

**Done.**  `Term.eval`'s `fix` case is `Lex.guardedFix`: it recomputes the measure at each
self call and recurses only on a strict lexicographic decrease, answering `stuck`
otherwise.  `exhausted` is renamed `stuck` throughout, including in the printer.  The
metatheory was re-proved in this shape: `Term.fixFun_unfold`,
`Term.fixFun_stuck_of_not_lt`, `Term.fixFun_eq_of_descends` (`LakeJs/Reducibility.lean`),
`Term.fix_implements` / `Term.fix_implements_closed` (`LakeJs/Fundamental.lean`) — which
no longer carry the iteration-bound hypothesis the rank design needed — and
`Term.fix_implements_measure` / `Term.fix_implements_structural` (`LakeJs/CertGen.lean`).

Acceptance: every hand-written corpus check still passes, every generated differential
check passes, and no run reaches `stuck` except where it is meant to —
`LakeJs.Expr.Examples.boomTerm_at_two`, the `Tco07.boom` input Lean has no answer for at
all, and `tco04_test1_out_of_domain`.

## Step 5 — `fixStruct` (§6.1)

**Not implemented, deliberately.**  The construct the plan sketches makes structural
descent a *scoping* condition: the context has to carry a "smaller than the subject"
marker that only a `caseTag` on the subject introduces, and `selfCall` has to require a
marked variable.  In this tree a context is a `List Ty` and is threaded through `Env`,
`Subst`, `Den`, `Usage`, the metatheory and every example; adding an index to it is a
change to all of them, and to every hand-written term in `LakeJs/Examples/`.

What that would buy is smaller: with the guarded semantics of step 4, a structural
recursion already carries a measure that *cannot be wrong in a way that produces a wrong
answer* — `Term.structMeasure` is the size of the recursion subject's runtime tree, the
one measure that always descends on a strict sub-component, and if it ever failed to
descend the answer would be `stuck` and the differential check of step 1 would go red.
The plan itself ranks this as the change with the best value per line *against the counted
rank*; against the guarded measure, the argument is weaker, and the cost is the same.

It remains the right next change if the structural case is ever pushed further, and
nothing in the present design blocks it: `fixStruct` would be a second constructor beside
`fix`, not a replacement for it.

## Step 6 — VC checker and the generic theorem (§5.4)

**Done, in the form the guarded semantics calls for.**  Note first that this step changed
category when step 4 landed: under the counted rank it was the fix for a
soundness-of-translation gap; under the guarded semantics the plan's own §6.2 makes it the
statement that the run-time comparison is *never refused*, hence removable.  Both halves
are now in the tree.

**The condition and its consequences** (`LakeJs/Descends.lean`).  `Term.Descends measure
body δ γ ρ` says: *the body consults its self-reference only at arguments of strictly
smaller measure*.  It is a property of the emitted term and its environment — Lean's
`termination_by`, its `decreasing_by` proof and the front end's transcription of either do
not occur in it — and it is quantified over *all* argument environments, so the branches
erasure made reachable are included.  Three generic theorems follow, each proved once, at
the level of `Lex.guardedFix`, so no constructor of the grammar can invalidate them:

| theorem | reading |
| :-- | :-- |
| `Term.fixFun_unfold_of_descends` | the recursion equals its body run with **itself** — no guard, no `stuck` |
| `Term.fix_stuck_irrelevant` | the value does not depend on the `stuck` term at all: *the branch is unreachable* |
| `Term.fixFun_eq_of_equation` / `Term.fix_implements_of_equation` | any Lean function satisfying the same unrolling equation **is** the recursion |

`Term.descends_of_measure1` states the condition in `Nat` for a one-component measure,
which is the shape most corpus functions have.

**The verification-condition generator** (`LakeJs/DescentVC.lean`).  `Term.SelfIndepOn δ ρ
S Φ t` is the judgment *"under the path condition `Φ`, `t`'s value depends on the
self-reference only through its behaviour on `S`"*, with a rule for every construct of the
grammar but a nested `fix`: variables, literals, globals, externs, application,
abstraction, `let`, `if`, constructors, projections, tags, structural size, delay, force,
dispatch (`caseTag`, with a judgment of its own for `Alts`), blocks (`block`, and `Tail`'s
`ret`, `jmp`, `letT`, `iteT`, `caseT`, `join`, with `AltsT` beside them), and both kinds of
self call.  The rules are lemmas rather than an inductive definition, so a derivation is
built by `apply`ing them structurally; the `if` rule refines the path condition with the
truth of the test in each arm, the `let` rule records the value the binder took, and the
dispatch rules record the matched tag and the fields the branch bound.  **The only rule
that leaves a goal is the self-call rule, and the goal it leaves is exactly the obligation
Lean's `decreasing_by` discharges.**  `Term.descends_of_selfIndepOn` closes the circle back
to `Term.Descends`.

**Discharged on the corpus of worked examples** (`LakeJs/Examples/Descent.lean`).  The
condition is proved for `sumTo` (structural on a number), `sumList` (structural over
data), `joinCount` (a body that is a block of join points), Ackermann (a two-component
lexicographic measure, with a *nested* self call), the merged `testEven`/`testOdd` clique,
and `Nat.gcd`; four of those go through the rule calculus, and the arithmetic left over is
one `omega` per call.  From them the file reads off that the `stuck` branch of each is
unreachable, and it proves two faithfulness theorems in the *new* shape — descent and
equation separately, combined by the generic theorem — including one that did not exist
before (`sumListTerm_implements`).

**And it has teeth.**  `Descends` is *refuted*, in the same file, for the two recursions
that reach `stuck`: `Tco07.boom`, whose erased proof made a non-descending branch
reachable (`boomBody_not_descends`), and the recursion that calls itself at the same
argument (`spinBody_not_descends`).  So the condition is not vacuous, and the price the
plan predicted in §5.4 — "it will reject `Tco07.boom`" — is paid exactly there and
nowhere else.

What is still open in this step: emitting the condition and its proof into each generated
`<Module>Program.lean`, so that a front end that read a measure wrongly produces a file
that does not elaborate.  The pieces are in place (the statement, the rules, and the
arithmetic being `omega`-shaped); what is missing is the tactic that assembles the
derivation for a machine-generated body.

## Step 7 — translation validation

**Not implemented, but its shape is now fixed.**  Proving, rather than sampling,
`eval(term) args = f args` for each translated declaration is the research-shaped item the
plan marks as such.  Step 6 split the job into two mechanical halves:
`Term.fix_implements_of_equation` takes (1) the verification condition, which the rule
calculus reduces to arithmetic, and (2) the body run with the Lean function as its
self-reference being that function — a one-step check against `f`'s own equation lemmas,
with no induction in it.  `LakeJs/Examples/Descent.lean` carries this out by hand for
`sumTo`, `sumList`, `joinCount`, `Nat.gcd` and Ackermann.  What is missing is only the
tactic that assembles both halves for a machine-generated declaration.  The generated
differential checks of step 1 are the sampled approximation, and they now cover every
declaration the sampler can call rather than the nine that were hand-written.
