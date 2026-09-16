# Assessment: indexing `Term` by a usage mask so that every bound variable must be used

*Subject: the proposal to add `Usage : Ctx → Type` and index `Term`/`Spine`/`Alts`/`Body`
by it, with `lamN` demanding `Usage.append (Usage.all params.reverse) uΓ` for its body, so
that a function ignoring one of its parameters is not a term at all.*

## Verdict in three lines

* **The design is sound and it does type-check.** I built a scaled-down version of exactly
  your declarations and it elaborates; `(v0) => v0` is accepted and `(v0, v1) => v0` is
  rejected, which is what you asked for. The evidence is in
  [`scripts/UsageProposalExperiment.lean`](scripts/UsageProposalExperiment.lean) — check it
  with `lake env lean scripts/UsageProposalExperiment.lean`; it is clean, and each
  rejection is pinned with `#guard_msgs`.
* **But it does not solve the problem you quoted**, and it breaks programs that must keep
  working. The `headOf` example you gave is an unused **`let` binding**, which the proposal
  as written still allows (`letE` takes `b : Bool`, and `b = false` is legal). Meanwhile
  the `lamN` rule makes `def f (_ : String) : String := "a"` — a real declaration in
  `SnapshotsPBOPure/FunctionCompose01.lean` — impossible to represent, so eleven modules of
  the corpus that compile today would have to be refused.
* **Recommendation: don't index `Term`.** Kill the unused bindings with a dead-code pass in
  `LakeJs/Simp.lean`, and, if you want the guarantee to be checked rather than hoped for,
  add an *extrinsic* `Term.support`/`Term.noUnusedLet` function plus a corpus check in
  `LakeJsTest`. That gets you the whole of the benefit at a small fraction of the cost. If
  you want the intrinsic version anyway, the right representation is co-de-Bruijn, not a
  usage mask (see §7).

---

## 1. What the proposal actually says

Read carefully, the design has two separable halves.

**(a) A bookkeeping half, which is not a restriction at all.** `var` is indexed by
`v.usage`, `lit`/`global`/`extern` by `Usage.none`, and every other constructor by the
pointwise `or` of its children. So for every term, the index is a *function of the term*:

> `u` is the exact set of variables of `Γ` that occur syntactically in `t`.

An index that is determined by the term carries no information. Formally,
`Term Γ u τ ≅ Σ (t : Term₀ Γ τ), support t = u`, where `Term₀` is today's unindexed term.
This half moves a computable function (`support`) into the type, where it must be reasoned
about with propositional equalities instead of being run.

**(b) A restricting half, which is the point: `lamN`** (and `lamProd`) demanding that the
body's mask starts with `params.length` `true` bits. That is a *relevance* discipline — every
binder must be used at least once — the "every" dual of linearity's "exactly once". It is a
coherent type system; it is the one you would get from quantitative/graded type theory with
the grade semiring `{1, ω}` and no `0`.

The user-facing effect is therefore: `lamN` is the only rule that rejects anything, and the
rest of the machinery exists to feed it.

## 2. Does it type-check? Yes — with four defects in the draft

The core elaborates as written. Four things are wrong or missing in the draft:

1. **`Usage.drop` does not exist, and is not trivial to write.** `loop` uses
   `Usage.drop σs.length ubody` where `ubody : Usage (σs.reverse ++ Γ)`. Its result type
   should be `Usage Γ`, which needs `(σs.reverse ++ Γ).drop σs.length = Γ` — i.e. a
   `List.length_reverse` rewrite inside a dependent type. Writing it as a mask-splitter
   (`Usage (Δ ++ Γ) → Usage Δ × Usage Γ`, by recursion on `Δ`) is cleaner; note you already
   avoid this in `letE` by *pattern-matching* the index as `.cons b u2`, which is the right
   trick and should be used everywhere.
2. **`loop` is inconsistent with `lamN`.** Loop slots are binders too, but the draft does
   not force them to be used. Either force them (and then a merged mutual loop with padded
   slots for members of different arities — `SnapshotsMy/MutualTail.js` — becomes a problem)
   or accept that the guarantee has a hole in exactly the construct this backend cares most
   about.
3. **The `Body`/`Alts` families need the same `.cons b` discipline for `letB`** — the draft
   has it — but `Body.cont` and `Body.ret` fix the mask in ways that will fight the merged
   loop, where one member's `cont` mentions only its own slots.
4. **`Var.usage`, `Usage.all` and `Usage.append` have to stay transparent.** The `lamN`
   rule works only because its index *computes*; in this project's `module` +
   `@[expose] public section` setting, make sure these definitions are exposed, or the
   index will be opaque to other modules and even `(v0) => v0` will fail to elaborate
   there.

None of these is fatal. The real costs are below.

## 3. It does not exclude the example you gave

Your motivating output is `SnapshotsMy/UnreachBranch.js`:

```js
const headOf = (v0) => {
  const v1 = v0._1;
  const v2 = v0._2; // UNUSED
  return v1;
};
```

The unused thing is `v2`, a `let`. Under the proposal, that term is
`letE (proj v0 2) (letE … body)` with the inner `b = false`, and the index is then simply
`u2` — perfectly well typed. The parenthetical in your draft ("if you also want to forbid
unused `let` bindings, replace `b` with `true`") is not an optional extra; **it is the only
part of the proposal that addresses the code you showed.**

And that variant is the *harmless* one: a dead `let` can always be deleted, because nothing
outside the term can observe it. A dead *parameter* often cannot, which is §4.

## 4. The `lamN` rule would refuse programs that currently compile

Measured on the generated corpus with
[`scripts/count-unused-bindings.mjs`](scripts/count-unused-bindings.mjs)
(`node scripts/count-unused-bindings.mjs`; the counts are lower bounds — the script is
lexical and treats a name reused in a sibling scope as used):

| binding kind | bound | never mentioned again | modules affected |
| --- | ---: | ---: | ---: |
| arrow-function parameters | 734 | **24** | 11 |
| `const`/`let` bindings | 1414 | **8** | 3 |

The eight `const`s are the dead-code case: `UnreachBranch` (2), `StringWalk` (1),
`HashContainers` (5). All eight are deletable.

The twenty-four parameters are not. They come from Lean sources like

```lean
-- SnapshotsPBOPure/FunctionCompose01.lean
def f (_ : String) : String := "a"
def g (_ : String) : String := "b"
def test1 := f ∘ g
```

which emits `const f = (_ignored) => "a";`, and

```lean
-- SnapshotsPBOPure/InlineReferencePrimOpInt.lean
def fn {α : Type} (_ : α) : Int := 0
```

which emits `const fn = (v) => 0;`. Also `DefaultRulesFunction01` (`test5 = (a) => (_ignored) => a`),
`InlineReferenceIfThenElse`, five more `InlineReference*` modules, `UnpackArray01`, and
`VanLaarhovenTraversals01` (three of `traverseFun1`'s seven parameters).

These are total, terminating, perfectly ordinary Lean functions. You cannot fix them by
dropping the parameter, because the parameter is part of the *type*, and therefore of the
calling convention: `f : String → String` is applied by `∘`'s output, by `test1`, and by any
importer of the module. Dropping it would change `f("x")` into `f()`, i.e. change the
interface of an exported declaration to match an accident of its body. So the only
available response is to **refuse the module** — and refusing `def f (_ : String) := "a"`
contradicts the stated goal that everything in `SnapshotsPBOPure` compiles.

This is the decisive argument. Relevance typing is a fine discipline for a *source*
language, where the programmer can be told "you wrote a parameter you never used". It is
the wrong discipline for a *backend* IR, whose job is to faithfully represent whatever the
front end legitimately produced.

## 5. What it costs inside this compiler

Producers pay; consumers do not. I checked both.

**Consumers are fine.** A recursion over `Term Γ u τ` with `u` an implicit variable —
`EmitJs`, `TyPretty`, `TermTotal.loopCount`, `Alts.select` — works unchanged; the index
stays a variable and never has to be inspected (`Term.size` in the experiment file).

**Producers pay at every constructor.** `Usage.or` is a commutative, idempotent monoid only
*propositionally*. In the experiment, even

```lean
example {Γ : Ctx} (u : Usage Γ) : u.or (Usage.none Γ) = u := rfl   -- fails
```

does not hold by `rfl` for an abstract `Γ`, so every place that builds a spine, reassociates
an application, or reorders two branches needs a rewrite. Swapping the arms of a
conditional — a one-line peephole today — becomes

```lean
def swapBranches … : Term Γ (uc.or (ut.or ue)) τ := by
  rw [Usage.or_comm ut ue]; exact Term.ite c e t
```

**Worse: a pass that deletes a use cannot keep its type.** `LakeJs/Simp.lean` is currently a
family of functions `Term Sg Γ τ → Term Sg Γ τ`; the type is what makes it safe. Under the
proposal, any rewrite that removes an occurrence (branch pruning, constant folding,
`FromLcnf`'s dropping of Lean-proved-unreachable branches, the η rule that replaces
`fun xs => f(xs)` by `f`) changes the index, so its type becomes
`Term Sg Γ u τ → Σ u', Term Sg Γ u' τ` — and if the deleted occurrence was the last use of a
parameter, **the simplified term does not exist**: the optimiser would have to be allowed to
fail, or to un-simplify. An IR in which improving a program can make it inexpressible is a
bad IR.

**The translation cannot use the index either.** `FromLcnf.lean` (1434 lines) and
`Compile.lean` (730 lines) build terms whose usage is unknown until the sub-terms exist, so
every intermediate result becomes `Σ u, Term Sg Γ u τ`, and every `lamN` becomes: take the
body's mask apart, check the parameter bits with a decidable equality, and either transport
or refuse. That is precisely `mkLam1` in the experiment file. Note what it shows: **the
dependent index does not perform the check, it only records the outcome of a check you had
to do anyway.** You could have run the same check on an unindexed term with none of the
transports.

## 6. And the guarantee is weaker than it sounds

Even in full strength (parameters *and* `let`s), "every bound variable occurs" is not "no
dead code":

* occurrence is **lexical**, so a variable mentioned only in a branch that can never be
  taken counts as used;
* it says nothing about a computation whose result is used only in a dead branch, about
  duplicated work, about unused loop slots, about unused globals or imports;
* conversely it *forbids* code that is not dead at all (§4).

So the property is neither necessary nor sufficient for the thing you presumably want,
which is "the emitted JavaScript contains no binding that cannot affect the result".

## 7. If you want it intrinsically anyway, use co-de-Bruijn

A usage mask attached as an index to an ordinary de Bruijn term is the awkward point of the
design space: the context is always the whole of `Γ`, so the mask and the term can drift
apart and must be kept in step by `or`-equations. The representation that makes relevance
*structural* is **co-de-Bruijn** (McBride and Allais, "Everybody's Got To Be Somewhere"),
where each subterm's context is *exactly* its support and the parent splits its context
between children with thinnings; a binder then carries one bit, and you get the discipline
you want simply by not providing the "unused" constructor. Supports are equal by
construction, not by rewriting, and the `or`-lemma noise disappears into a handful of
smart constructors.

The price is that the whole backend has to be written against thinnings, and that the
`Ty`-directed parts of `FromLcnf` get harder, not easier. Unless the relevance property is
itself a deliverable, I would not pay it.

## 8. What I would do instead (concrete, small)

1. **A dead-`let` pass in `LakeJs/Simp.lean`.** Add
   `Term.occursHead : Term Sg (σ :: Γ) τ → Bool` and a strengthening
   `Term.strengthen? : Term Sg (σ :: Γ) τ → Option (Term Sg Γ τ)` (the inverse of weakening:
   rebuild the term with `Var.tail v ↦ v`, failing on `Var.head`), then rewrite
   `letE e b ↦ b'` whenever `strengthen? b = some b'` **and** `e` is duplicable-free work you
   are willing to drop (all `Term`s are pure, so this side condition is only about cost, not
   semantics). This removes all eight unused `const`s, including your `headOf`. `strengthen?`
   is about 100 lines over the four mutual families — and it is work the indexed design would
   have forced you to write anyway, only there it would sit on the critical path.
2. **An extrinsic check, if you want the invariant guarded.** `def Term.support : Term Sg Γ τ → Mask Γ`
   (a plain `List Bool` of length `Γ.length`) plus `Term.noUnusedLet : Bool`, asserted over the
   whole corpus in `LakeJsTest` next to the existing `JsShape` token check. Keep *parameters*
   out of the assertion, for the reason in §4. If you later want a theorem, the honest one is
   `(Simp.simp t).noUnusedLet = true`, which is provable by induction and needs no change to
   `Term`.
3. **Report, don't refuse, for unused parameters.** A `note` line per declaration, in the same
   style the test run already uses for non-tail recursion, tells you when the *front end*
   handed you a constant function — which is real information — without making the backend
   unable to compile it.

## 9. Direct answers

> **Is this correct?**

Yes as a type system, and yes as Lean code modulo the four defects in §2 — I checked it
mechanically. But as written it enforces the rule for **function parameters only**, and your
motivating example is a `let`, so as written it does not exclude the `headOf` output you
quoted.

> **Does it make sense to allow only trees that use every parameter?**

No, not for this IR. A parameter belongs to the function's *type* and hence to its calling
convention, so an unused parameter cannot be removed and the rule turns "this program has a
redundant binding" into "this program cannot be compiled" — for eleven modules that compile
today, including `def f (_ : String) : String := "a"`. The same rule over `let` bindings is
harmless and is what you actually want, but it is far cheaper obtained by deleting the dead
`let` in `Simp` and checking the result, than by indexing four mutually recursive families
with a mask whose algebra holds only up to propositional equality and which makes
use-deleting optimisations untypable.
