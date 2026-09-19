# Splitting `Term` by stack behaviour — assessment of the `StackProfile` proposal

*Companion to `TERM_ONE_GRAMMAR_ASSESSMENT.md` (the plan of record), `TERM_RANK_VS_ACC.md`
(why the recursion carries a measure and not an `Acc`) and
`TERM_RANK_FLAKINESS_AND_ALTERNATIVES.md` (why the measure is checked rather than
trusted).*

**Scope.**  It answers the three questions asked:

1. `fixAcc` is too permissive — it admits recursions that run in constant stack and
   recursions that will blow the stack, and does not distinguish them.  Does
   `inductive TermRecursiviness | primitive | nonprimitive`, or the `StackProfile` sketch,
   split them?  What would the implementation look like?
2. What optimisations would the split enable — should general recursion be trampolined
   automatically when emitting JavaScript, and is "loop-convertible ⇒ can only
   heap-overflow, generally recursive ⇒ can stack- *and* heap-overflow" correct?
3. Is the hierarchy more subtle than two points — should `fixAcc` split three ways
   (general recursion / loop / bounded loop)?

**Marking.**  Following the other notes in this tree: **[verified]** means I checked it
against the sources in this sandbox or it is a theorem in the checked-in artifact;
**[proposed]** means it is a design recommendation, not a fact about the tree.

**The checked artifact.**  `ExamplesStackProfile/Sketch.lean` (builds with
`lake build ExamplesStackProfile`, no `sorry`, axioms `[propext]` only).  It contains two
miniature languages — scale models of the relevant fragment of `LakeJs.Expr.Term` — so
that the central claim below is a theorem rather than an opinion.

---

## 0. The three answers, first

**1. The sketch is sound but empty.**  Under the index exactly as proposed, a
`constStack` term contains **no recursion at all**
(`ExamplesStackProfile.Sketch.MTerm.const_fixFree`, **[verified]**): `fixAcc` is
`deepStack` by construction, `lam` propagates its body's profile, and the one `constStack`
recursive construct, `loopJmp`, is only reachable from inside a `deepStack` body.  So
`constStack` ends up meaning "recursion-free", and the index never separates one recursive
function from another — which is exactly the job it was introduced to do.  The naming
`primitive`/`nonprimitive` is separately wrong: primitive recursion is a *definability*
class and has nothing to do with stack frames (§2).

**2. The fix is not "one more index on `Term`", it is an annotation on the arrow.**  What
costs stack is *calling* a function, and the caller sees the callee only through its type;
so a profile that is to survive higher-order code has to live in `Ty`, not in `Term`
(`ExamplesStackProfile.Latent`, **[verified]**: with the profile on the arrow,
`countdown` — a tail recursion — has type `base →⟨const⟩ base` and `sumdown` — the same
function written non-tail — has type `base →⟨deep⟩ base`, and the difference is visible at
a call site that never mentions either body).  That is a real change to the whole tower
(`Ty`, `RTy`, `RTyWf`, `Layout`, `Schema`, `Den`, `FrontEndTy`, …) for a property that is
**not a soundness property**: a stack overflow is a resource failure, not unsoundness, and
"terminating by construction" is untouched by it.  My recommendation is therefore
**option A of §5**: leave the grammar alone and add a *computed*, decidable
`Term.stackProfile` plus a theorem about an instrumented machine.  The information ends up
in the same place (a field the backend reads), at a small fraction of the cost, and it
does not put the existing `Descends`/`SN`/`Subst` proofs at risk.

**3. Yes, the hierarchy is more subtle — but not in the direction of "bounded loops".**
Four independent axes are being conflated (§2).  On the stack axis the tier that actually
pays off in codegen is not "bounds are known statically" (almost never true) but
**"the frame count is computable at loop entry"** — which holds exactly when the measure
is a single `nat` (`k = 1`), and fails for a lexicographic measure with `k ≥ 2`
(**[verified]**: the measure is `Lex.NatVec` and lower components are recomputed by the
body at every re-entry, so no function of the entry vector bounds the depth).  That gives
a three-point lattice `const < entryBounded < deep` with a *runtime* dispatch at the
outermost entry — measure the argument, take the fast native-recursive path if it is under
the engine budget, the trampolined path if not.  That answers "should we trampoline
automatically?" better than any static guess can (§6).

---

## 1. What is in the tree today — **[verified]**

For the discussion to be about this compiler and not a generic one:

* There is **one** recursion constructor, and it does not carry a `WellFounded` proof
  (`LakeJs/Expr.lean`):

  ```lean
  | fix : ∀ {Γ Ρ τ}, (ps : List Ty) → (k : Nat) →
      (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k)) →
      (body   : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) →
      (stuck  : Term Sg (ps ++ Γ) Ρ τ) →
      Term Sg Γ Ρ (Ty.arrows ps τ)
  | selfCall : ∀ {Γ Ρ ps τ}, (Ρ ∋ᵣ ⟨ps, τ⟩) → Spine Sg Γ Ρ ps → Term Sg Γ Ρ τ
  ```

  The measure is a `k`-component **lexicographic** vector of `nat`s, and the whole
  constructor lives in `Type` with no `Prop` fields.  The `fixAcc` of the proposal —
  `(α : Type) (r : α → α → Prop) (hwf : WellFounded r) (hdec : DecidableRel r)` — is the
  shape this tree deliberately moved *away* from (`TERM_RANK_VS_ACC.md` §3); re-adopting
  it would push `Term` from `Type` to `Type 1`, and would make it non-`DecidableEq`,
  non-printable and non-serialisable, which is why the sketch's `Type 1` is not a typo but
  a consequence.  Everything below is written against the `fix` that exists.

* **`selfCall` is a `Term`, not a `Tail`.**  `Tail`'s constructors are `ret`, `jmp`,
  `letT`, `iteT`, `caseT`, `join` — `jmp` goes to a *join point* only.  So today there is
  **no syntactic tail self call at all**: whether a self call is a tail call is a property
  of its *position*, not of its constructor.  Any stack-profile story, in a type index or
  not, has to add that distinction first.

* **`Term.eval` is a denotation, not a machine** (`LakeJs/Reduce.lean:196`):
  `| .ap f a => (f.eval δ γ ρ) (a.eval δ γ ρ)`.  It maps a term to a Lean value of type
  `τ.den`, and a recursion to `Lex.guardedFix`.  A *frame* is not a thing in that
  semantics, so **no statement about stack depth can even be phrased against the present
  evaluator.**  Any profile claim needs a second, instrumented semantics.  This is the
  single largest under-estimated cost in the proposal, and it is the same cost under every
  option in §5.

* Every `Term` terminates, and the guarded runner plus `Term.Descends`
  (`LakeJs/Descends.lean`, `LakeJs/DescentVC.lean`) is what turns "terminates" into
  "computes the Lean function it came from".  **Nothing in §2–§7 touches that**; the
  stack question is entirely downstream of it.

---

## 2. First: four axes are being conflated

The proposal's two namings (`primitive`/`nonprimitive`, and `constStack`/`deepStack`) are
not two names for one distinction.  There are four independent properties in play:

| # | axis | question | decidable from the tree? | already settled? |
|---|---|---|---|---|
| 1 | **termination** | does it stop? | yes, by construction | **yes** — `fix` + measure |
| 2 | **frame discipline** | how many frames while it runs? | yes, syntactically (tail positions) | no |
| 3 | **definability / growth rate** | primitive recursive? multiply recursive? | **no** | n/a |
| 4 | **allocation** | how much heap while it runs? | only approximately | no |

*Axis 3 is the one called "primitive".*  A primitive recursive function is one built from
zero/successor/projection by composition and a bounded recursion scheme; Ackermann is the
standard example of a total function that is not primitive recursive.  This grammar
expresses Ackermann comfortably — as two nested `fix`es, one per lexicographic component
(`TERM_RANK_VS_ACC.md` §1, **[verified]**) — so `Term` is nowhere near "primitive
recursive" as a class, and it is not a class you can read off a tree anyway (deciding it
would require deciding growth rates).  Worse, the axis is **orthogonal to the one you
care about**: `countdown n = if n = 0 then 0 else countdown (n-1)` is primitive recursive
*and* runs in constant stack; `sumList (x :: xs) = x + sumList xs` is primitive recursive
*and* pushes a frame per element.  So:

> **[verified, by counterexample above]** "Primitive recursive" and "constant stack" are
> not the same partition, not even nearly.  Do not name the index after axis 3.  The
> second naming in the proposal — `constStack` / `deepStack` — is the right notion; use it
> and drop `TermRecursiviness` entirely.

*Axis 2 is what you want*, and it is genuinely syntactic and genuinely decidable: "every
self call is in tail position, and every function this term calls is itself constant
stack".  The rest of this note is about how to record it.

---

## 3. The sketch, assessed

### 3.1 What it gets right

* The lattice is right: two (or three, §7) points ordered by "worse", with a join, and the
  join used wherever two subterms are evaluated in the same frame.  `Max` instance,
  `DecidableEq`, `join` by pattern match — all fine and all reusable.
* The intuition behind `loopJmp` is right: a self call in **tail** position is a `continue`
  of a `while (1)`, and is the only recursive shape that needs no frame.  That construct
  has to exist in some form, and it does not exist today (§1).
* Making `selfCall` (the non-tail one) `deepStack` is right.
* Separating `lift` out as an explicit coercion, rather than making the grammar
  subsumptive, is the honest choice *if* you index at all.

### 3.2 Finding 1 — `constStack` classifies nothing recursive — **[verified]**

`ExamplesStackProfile/Sketch.lean` transcribes the proposal's constructors and proves:

```lean
theorem MTerm.deep_of_hasFix (t : MTerm m Γ Ρ τ) : t.HasFix → m = SP.deep
theorem MTerm.const_fixFree  (t : MTerm .const Γ Ρ τ) : ¬ t.HasFix
theorem MTail.const_fixFree  (t : MTail .const Γ Ρ τ) : ¬ t.HasFix
```

Read the second one as the specification the index actually satisfies: **a `constStack`
term defines no recursion.**  The reason is a chain of three constructor signatures in the
sketch itself:

1. `fixAcc` produces `MTerm .deep` unconditionally, and demands
   `body : Term Sg .deepStack (ps ++ Γ) (⟨ps,τ⟩ :: Ρ) τ` unconditionally.  So **no
   recursion is ever `constStack`**, including one whose body is a single `loopJmp`.
2. `loopJmp` needs a non-empty `Ρ`, and the only constructor that extends `Ρ` is `fixAcc`.
   So the only place a `constStack` `loopJmp` can occur is inside a `deepStack` body,
   where its profile is joined away immediately.
3. `lam` propagates: `lam : Term m (σ :: Γ) → Term m Γ (σ ⇒ τ)`.  So the profile of a
   closure is the profile of its body, and every enclosing term inherits it.

Point 3 is also what makes the sketch *sound* — it is the brute-force answer to the
higher-order problem of §3.3 — and points 1–2 are what make that soundness vacuous.  The
two are not independent: propagate the latent cost through `lam` and you collapse
`constStack` to "recursion-free"; do not propagate it and you get §3.3's unsoundness.
There is no third option **at the `Term` index**.

### 3.3 Finding 2 — stack cost is *latent*, so it belongs on the arrow

The cost of `f x` is not a function of the costs of `f` and `x`.  Evaluating `f` may be
`O(1)` (it is a variable, or a `lam`, or a `fix` — all of which merely build a closure),
evaluating `x` may be `O(1)`, and yet running the call may push a million frames.  In the
sketch, `var : ∀ m, Var Γ τ → MTerm m Γ Ρ τ` is profile-polymorphic, so `ap (var f) (var x)`
is typeable at `constStack` no matter what closure `f` is bound to — the index of the term
says nothing about the closure.  The sketch escapes this only by the `lam` rule, i.e. by
never letting a deep closure exist inside a const term in the first place, which is
Finding 1.

The standard repair, and the one type theory actually offers here, is a **latent effect
annotation on the function type** — the same device as effect systems, `Async`-typing, and
cost/coeffect calculi:

```lean
inductive CTy | base | arr (p : SP) (σ τ : CTy)

| lam : CTail p (σ :: Γ) Ρ τ → CTerm .const Γ Ρ (.arr p σ τ)          -- closing over is free
| ap  : CTerm m₁ Γ Ρ (.arr p σ τ) → CTerm m₂ Γ Ρ σ →
        CTerm (m₁.join (m₂.join p)) Γ Ρ τ                             -- calling costs p
| fix : (ps) → (p : SP) → measure → (body : CTail p …) →
        CTerm .const Γ Ρ (CTy.arrows p ps τ)                          -- profile chosen, and exported
```

`ExamplesStackProfile.Latent` is this system, and **[verified]**:

```lean
theorem CTerm.deep_of_costly (t : CTerm m Γ Ρ τ) : t.Costly → m = SP.deep
theorem CTail.const_notCostly (t : CTail .const Γ Ρ τ) : ¬ t.Costly
```

where `Costly` = "makes a non-tail self call, or applies a function whose latent profile
is `deep`".  Now `constStack` says something about recursions, because a recursion can
*be* `constStack`:

```lean
def countdown : CTerm .const [] [] (CTy.arrows .const [.base] .base) := …  -- while (1)
def sumdown   : CTerm .const [] [] (CTy.arrows .deep  [.base] .base) := …  -- pushes frames
example : (CTerm.ap countdown (.lit 5)).Costly ↔ False := by simp [CTerm.Costly, countdown]
example : (CTerm.ap sumdown   (.lit 5)).Costly         := by simp [CTerm.Costly, sumdown]
```

Note what the last two lines show: the classification is visible **at the call site, from
the type alone**, without looking at either body.  That is the property the sketch cannot
have and the reason the annotation has to be on `Ty`.

### 3.4 Finding 3 — there is no principal profile

`var` is profile-polymorphic and `lift` exists, so one and the same term is typeable at
both profiles (`Sketch.varAtBothProfiles`, **[verified]**).  The index is an *upper bound*
chosen by whoever built the tree, not a fact recovered from it.  Consequences:

* two `Term`s that are equal as programs can differ as data, so `DecidableEq`, hashing,
  dumping and diffing all see spurious differences — relevant, because the test runner
  compares `-Expr.txt` dumps;
* a downstream pass that reads the index is trusting the front end's choice.  With a
  *computed* `Term.stackProfile` (option A) there is nothing to trust: the value is a
  function of the tree.

### 3.5 Finding 4 — the Lean cost of a computed index

`ap : … → Term Sg (m₁ ⊔ m₂) Γ Ρ τ` puts a **non-injective function application in an index
position**.  That is outside Lean's pattern-unification fragment, and the consequences are
not theoretical:

* Matching on a term at a *known* profile (`t : Term Sg .const Γ Ρ τ`) forces the
  elaborator to solve `m₁ ⊔ m₂ =?= .const`, which it cannot; you get either a failure or a
  `motive is not type correct`, and you work around it by generalising the index and
  carrying equations by hand.  Both mutual-family theorems in the artifact are stated as
  `… → m = SP.deep` for *arbitrary* `m` for precisely this reason — the direct statement
  over `.const` does not go through by `cases`.
* Binder order becomes load-bearing: `CTerm.Costly`'s `ap` equation needs the explicit
  `@CTerm.ap _ _ _ _ p _ _ f a` form to name the latent profile, which is unreadable and
  breaks whenever a constructor gains an argument.  (**[verified]** — the first version of
  the artifact got the arity wrong and the definition silently became `sorry`.)
* Every function over the grammar gains an index argument and every lemma an index
  hypothesis.  In this tree that is `Subst.lean`, `SubstLemmas.lean`, `LSubstLemmas.lean`,
  `Reduce.lean`, `Den.lean`, `Progress.lean`, `SN.lean`, `Descends.lean`, `DescentVC.lean`,
  `DescentSimp.lean`, `DescentTactic.lean`, `TailShape.lean`, `TailPos.lean`,
  `Usage.lean`, `InlineSize.lean`, `ExprPretty.lean`, `FromLcnf.lean`, `FrontEnd.lean` —
  several thousand lines of checked proof that has to be re-indexed for a property that
  **proves nothing about soundness**.  And with the profile on the arrow (§3.3, the only
  version that works) `Ty.lean`, `RTy.lean`, `RTyWf.lean`, `Layout.lean`, `Schema.lean`,
  `TySchema.lean` and `FrontEndTy.lean` go too — and `Ty` stops being in bijection with
  the erased Lean types, which is a property `FrontEndTy` currently relies on.

### 3.6 Finding 5 — and it is not a soundness property

The reason `Term` is intrinsically scoped, typed, linked and measured is that a violation
of any of those is **unsoundness**: a wrong answer, silently.  "Unrepresentable" is the
right bar there.  A stack overflow is a different kind of event: the program stops with a
diagnosable error and no wrong answer is produced.  Resource properties are conventionally
carried extrinsically — which is what this tree already does for every other resource-ish
property (`Tail.Flat`, `Usage`, `InlineSize` are all predicates/analyses over the grammar,
not indices in it).  Putting axis 2 in the type would be the only place where the project
pays intrinsic-typing prices for a non-soundness property.

---

## 4. So: does the split make sense at all?

**Yes — the distinction is real, useful and decidable.**  `fixAcc` *is* too permissive in
the sense asked: it lumps `while (1)` together with "recurse a million deep", and a
backend has to know which it is.  The disagreement is only about *where the answer is
recorded*: computed from the tree (cheap, unique, no proof debt) versus an index of the
tree (expensive, non-unique, and — in the shape proposed — empty).

---

## 5. Three ways to record it, with costs

### Option A — a computed analysis beside the grammar — **[proposed], recommended**

Leave `Expr.lean` alone except for one new constructor (the tail self call, which is
needed under every option):

```lean
-- LakeJs/Expr.lean, new Tail constructor
/-- A self call in tail position: a `continue` of the enclosing loop. -/
| selfJmp : ∀ {Γ Ω Ρ ps τ}, (Ρ ∋ᵣ ⟨ps, τ⟩) → Spine Sg Γ Ρ ps → Tail Sg Γ Ω Ρ τ
```

and add one new module:

```lean
-- LakeJs/StackProfile.lean
inductive StackProfile | const | entryBounded | deep    -- §7
def Term.stackProfile   : Term Sg Γ Ρ τ → StackProfile  -- mutual with Tail/Alts/Spine
def Sig.stackProfiles   : Sig → Array StackProfile      -- least fixed point over the module
```

`Term.stackProfile` is a structural recursion over the tree (decidable, total, unique),
and the module-level version is a three-line ascending fixpoint over `Sg` — which the
indexed version *cannot* do at all, because a mutual group of top-level declarations would
need its profiles known before any of them is built.  That alone is decisive for this
compiler, where mutual recursion across `Sg` is the common case (`MutualTail`,
`MutualSlots`, `Tco03`, `Tco04`).

What it costs, honestly:

1. `LakeJs/StackProfile.lean` — the lattice, the analysis, the fixpoint.  Small.
2. `LakeJs/Frames.lean` — **the real work**: a second, instrumented semantics in which a
   frame exists, since `Term.eval` cannot express one (§1).  The lightest version that
   still says something true is a *cost-annotated* evaluator
   `Term.evalD : … → τ.den × Nat` returning the maximum frame depth, defined by the same
   `Lex.guardedFix` recursion as `eval`, plus `Term.evalD_fst_eq_eval` (it computes the
   same value).
3. The theorems that make the claim honest:
   * `stackProfile t = .const → (t.evalD δ γ ρ).2 ≤ t.staticDepth` — depth bounded by a
     number read off the *term*, independent of the inputs.  This is the precise meaning
     of "cannot stack-overflow", and note it is **not** "depth ≤ 1": a const-profile term
     still nests `let`s and non-recursive calls, so the bound is a static constant, not a
     constant `1`.
   * `stackProfile t = .entryBounded → (t.evalD δ γ ρ).2 ≤ measureVal … + t.staticDepth` —
     the tier of §7, and the fact the runtime dispatch of §6 relies on.
   * `Term.stackProfile_rename` / `_subst` — stability under the passes, matching what
     `Tail.flat_rename` does for flatness.
4. `ExprPretty` / the `-Expr.txt` dump: print the profile next to each 🎯 target.  Free.

Nothing in `Descends`, `SN`, `Subst`, `Den` or `FromLcnf` changes, so nothing already
proved is put at risk.

### Option B — the profile on the arrow (`ExamplesStackProfile.Latent`) — **[proposed], not now**

The only *fully compositional* answer, and the only one that stays precise under
higher-order code (§3.3).  Adopt it if and when the corpus actually contains
higher-order code that passes deep-recursive functions as arguments and where option A's
conservative "unknown callee ⇒ `deep`" answer loses too much.  On the snapshot corpus as
listed in the original task that is **no file**: every recursion there is a direct call of
a named declaration.  Until then the cost (§3.5, including all of `Ty`) buys nothing.

### Option C — a profile *field* on `fix`, with a proof field — **[proposed], the middle path**

```lean
| fix : … → (profile : StackProfile) →
        (hprofile : profile = .const → body.SelfCallsAreTail) → …
```

This follows the pattern the tree already uses for `caseTag`'s `h : σ.caseOkAlts … = true`
and is documented in `TERM_PROOF_FIELDS.md`: the fact is *in* the tree, so a backend reads
it without re-running an analysis, and it cannot be wrong, because the constructor demands
the evidence.  It costs one field and a `decide`-able side condition, and it does not
touch `Ty`, indices, or unification.  Its drawback versus A is that the front end must
supply the proof (trivially, by `decide`) and that the field, being redundant, has to be
kept in sync by every pass that rebuilds a `fix`.

**Recommendation: A now; C when the JavaScript backend lands and wants the fact in the
tree; B only if higher-order deep recursion actually shows up.**

---

## 6. Question 2 — what it buys the backend

### 6.1 Codegen, tier by tier — **[proposed]**

| profile | emitted as | failure mode |
|---|---|---|
| `const` | `while (true) { … }` with parameter reassignment; `selfJmp` is `continue` | none from frames; still `OOM` if it allocates per iteration |
| `entryBounded` (§7) | native recursion, with a **guard at the outermost entry**: if `measure(args) > BUDGET`, call the trampolined copy instead | none, if `BUDGET` is set below the engine's limit |
| `deep` | trampoline / defunctionalised CPS by default | `OOM` (heap), not `RangeError` (stack) |

### 6.2 "Should we trampoline automatically, or only when the optimiser sees an overflow?"

**Only-when-the-optimiser-sees-it is not implementable as a sound rule** — **[proposed,
but the impossibility is standard]**.  Whether a given `deep` recursion overflows is a
question about *inputs*, not about the term: the depth is a function of the measure at
entry, and asking "is there an input whose measure exceeds 10⁴" is a reachability question
over arbitrary arithmetic.  A static analysis can only ever give a *sufficient* condition
("this one is fine"), never a decision procedure.  So the choice is a policy:

* **Default to correctness.**  Emit the trampoline for `deep`, because the alternative
  failure is a `RangeError` in production on an input nobody tested.  The cost is a
  constant factor (one heap cell per pending frame, one dispatch per step) on a class of
  functions that, on the snapshot corpus, is the minority.
* **Buy the fast path back with the `entryBounded` guard**, not with a static guess.  When
  `k = 1` the frame count *is* computable at entry, in `O(1)`, from values you already
  have; one comparison at the outermost call picks native recursion or the trampoline.
  Emit both bodies from the same `Term` — they are two renderings of one tree, so there is
  no correctness risk in having both.
* **Do not rely on the engine.**  Proper tail calls are in the ECMAScript standard but
  only JavaScriptCore ships them; V8 and SpiderMonkey do not.  So a `const`-profile
  function must be emitted as an actual `while` loop, not as a tail call and a hope.
* An explicit opt-out (`@[js_no_trampoline]`) is worth having for hot functions the author
  knows are shallow — but as an *opt-out*, so the unsafe choice is the one you have to ask
  for.

### 6.3 "Primitively-recursive ⇒ loop ⇒ only heap-overflow; general ⇒ no loop ⇒ both" — **not correct, on both halves**

Restating the claim and correcting it:

* **"Loop-convertible = primitive recursive" — no.**  Conversion to a bare `while` loop
  with no auxiliary storage is possible exactly when every self call is in **tail**
  position.  That is a syntactic property, and it cuts across axis 3 in both directions:
  `sumList (x :: xs) = x + sumList xs` is primitive recursive and *not* tail recursive
  (§2), while a tail-recursive loop over a well-founded measure can compute functions that
  are not primitive recursive at all.
* **"Generally recursive functions cannot be transformed to a while loop" — no.**  *Every*
  recursion becomes a `while` loop once you materialise the continuation as an explicit
  data structure — that is exactly what a trampoline, or defunctionalised CPS, is.  The
  transformation is always available; what changes is **where the frames live**.
* So the real dichotomy is not loop/not-loop, it is **which finite resource holds the
  activation records**:

  | | frames on | size | exhaustion |
  |---|---|---|---|
  | native recursion | the engine call stack | small, fixed, not configurable per-call (~10⁴ frames) | `RangeError: Maximum call stack size exceeded` |
  | trampoline / explicit stack | the heap | large, configurable (`--max-old-space-size`) | `OOM` |

  Both are finite; both can be exhausted.  Trampolining does not remove a failure mode, it
  **moves it to the resource that is 3–4 orders of magnitude larger and that the operator
  can size**.  That, and not "cannot overflow", is the honest selling point.
* **`const` stack ≠ constant memory.**  A tail-recursive loop that conses onto an
  accumulator allocates without bound and will OOM.  So the profile bounds *frames* only;
  it says nothing about the heap (axis 4), which would need a separate analysis — the
  natural home for which is `Usage.lean`/`InlineSize.lean`.

---

## 7. Question 3 — the finer hierarchy

Splitting `fixAcc` three ways is the right instinct, but "bounded loop (bounds are known)"
is the wrong third tier: in real code the bound is a function of the input, so the
statically-bounded class is nearly empty (literal-bounded `for` loops and not much else).
The tier that pays is **"the bound is computable at entry"**:

```lean
inductive StackProfile
  /-- Every self call is in tail position, and every callee is `const`.
      Frames ≤ a constant read off the term. -/
  | const
  /-- Non-tail self calls, but the measure is a single `nat` (`k = 1`), so the frame
      count is bounded by `measure(args)`, which is known *before* the loop is entered. -/
  | entryBounded
  /-- Anything else: lexicographic measure with `k ≥ 2`, or a callee of unknown profile. -/
  | deep
```

Why `k = 1` is the cut, **[verified]**: the runner is
`Lex.guardedFix (m : α → NatVec k)` over `Lex.NatVec.Lt`, the lexicographic order with the
most significant component first.  With `k = 1` each call strictly decreases one `nat`, so
the number of nested activations is at most `m(args)` — a number in hand at entry.  With
`k ≥ 2` the body *recomputes* the lower components at each call and may reset them to
anything (this is exactly what makes `ack` expressible, `TERM_RANK_VS_ACC.md` §1), so no
function of the entry vector bounds the depth.  The right ordinal bound is `ω^k`, which is
not a runtime budget.

Two further refinements worth keeping *out* of the lattice and in a separate attribute,
because they are different axes:

* **self-tail-recursive but calls a deep callee** — option A's fixpoint over `Sg` handles
  this by the join; no new tier needed.
* **`entryBounded` with a cheap measure vs. an expensive one** — evaluating the measure at
  entry is itself work (`Array.size` is `O(1)`, a `structSize` over a tree is not).  The
  runtime guard of §6.2 is only worth emitting when the measure is `O(1)`; that is a
  predicate on the measure spine, not a stack tier.

Finally, on "is the grouping more subtle, based on type theory?": the type-theoretic
hierarchy that *does* apply here is the latent-effect one of §3.3 (profiles on arrows,
joined at application, chosen at abstraction) — with the lattice above in place of the
two-point one.  That is a coeffect system, and it is a well-understood, sound design.  The
question is not whether it works; it is whether the precision is worth re-indexing `Ty`
and several thousand lines of proof for a corpus that is entirely first-order.  Today it is not.

---

## 8. Plan, in order — **[proposed]**

1. **Name it `StackProfile`**, not `TermRecursiviness`; drop `primitive`/`nonprimitive`
   (§2).
2. **Add `Tail.selfJmp`** to `LakeJs/Expr.lean` (§5) and teach `FromLcnf`/`FrontEnd` to
   emit it when a self call is in tail position.  This is a prerequisite for every option
   and is worth doing on its own: it is the constructor a `while` loop is emitted from.
3. **`LakeJs/StackProfile.lean`**: lattice, `Term.stackProfile`, `Sig.stackProfiles`
   fixpoint, renaming/substitution stability.
4. **`LakeJs/Frames.lean`**: the instrumented evaluator and `evalD_fst_eq_eval`.  Largest
   item; without it the profile is an unproved annotation.
5. **The three bound theorems** of §5.  These are what let the summary say "cannot
   stack-overflow" rather than "we believe it does not".
6. **Dump the profile** in `-Expr.txt` beside each 🎯 target, and add the per-file
   profile table to `SNAPSHOT_TERM_COVERAGE.md`.  Expected from the corpus: `const` for
   `Tco01`, `Tco03`, `Tco04`, `Tco06/07`, `MutualTail`, `AssignSteps`, `LoopEntry`,
   `MutualSlots`, `ScalarRepl`, `CaptureDerefRegression01`, `StringWalk`, `Fusion02`;
   `entryBounded` for `GcdEntry` and `CaseLeafTco`; `deep` for the tree recursions
   (`CaseJacobs`, `RecursionSchemes01`, `VanLaarhovenTraversals01`).  *These are
   predictions, not measurements — step 3 is what turns them into a table.*
7. **Backend**: `const → while`, `entryBounded → guarded native/trampoline pair`,
   `deep → trampoline`, opt-out attribute.
8. Revisit option B only if a snapshot appears that passes a `deep` function as an
   argument.

---

## 9. The checked artifact

`ExamplesStackProfile/Sketch.lean` — `lake build ExamplesStackProfile`, no `sorry`, axioms
`[propext]`.

| name | says |
|---|---|
| `Sketch.MTerm.deep_of_hasFix` | in the proposal as written, any term containing a recursion is indexed `deepStack` |
| `Sketch.MTerm.const_fixFree`, `Sketch.MTail.const_fixFree` | hence `constStack` = "contains no recursion"; the index never separates two recursive functions |
| `Sketch.varAtBothProfiles` | the index is not unique: one term, both profiles |
| `Latent.CTerm.deep_of_costly` | with the profile on the arrow, any term that pushes a frame is `deepStack` |
| `Latent.CTail.const_notCostly` | a `constStack` body makes no non-tail self call and applies no `deepStack` function |
| `Latent.countdown`, `Latent.sumdown` | a tail recursion at `base →⟨const⟩ base` and a non-tail one at `base →⟨deep⟩ base` |
| the two `example`s after them | the profile is readable **at the call site**, from the type alone |

What the artifact does **not** contain, and what no design in this note can claim until
step 4 of §8 exists: a theorem relating any profile to an actual frame count.  Both models
are typing disciplines; the operational meaning of `const` and `deep` is stipulated by
their names until there is a machine to measure against.
