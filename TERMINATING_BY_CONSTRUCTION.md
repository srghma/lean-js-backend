# `Term` terminating by construction: what was built, and why it looks like this

> **Superseded.**  `LakeJs/TermC.lean`, the second grammar this document describes, has been
> **removed**: the decision is now one grammar, with the recursion discipline intrinsic to it.
> The file is still in git history.  For the current assessment and plan — why a loop construct
> is not enough, what replaces `CTerm`, and which parts of the development below are reused —
> see `TERM_ONE_GRAMMAR_ASSESSMENT.md`.

The request was: **a term of the language should terminate by construction.**  It is now
implemented, in `LakeJs/TermC.lean`, as the grammar `CTerm`, and the guarantee is a
theorem with no side condition:

```lean
theorem CTerm.erase_terminating (t : CTerm Sg Γ τ) : t.erase.Terminating
theorem CTerm.sn    (t : CTerm Sg [] τ) : t.erase.SN
theorem CTerm.halts (t : CTerm Sg [] τ) : ∃ v, Steps t.erase v ∧ Value v
theorem CTerm.eval_total (t : CTerm Sg [] τ) : Steps t.erase t.eval ∧ Value t.eval
```

*Every* closed `CTerm` runs out of steps and reaches an answer — not "every `CTerm` that
passes a check", and not "every `CTerm` carrying an extra hypothesis".  Everything below
builds with no `sorry`, and the only axioms are `propext`, `Classical.choice`,
`Quot.sound`.

---

## 1. Why the certificate cannot be a field of `Term` itself

The literal reading of the request is: add the termination certificate as a field of
`Term.block`, so that `Term` *is* the terminating language.  That is impossible as
stated, and for a reason that is not an engineering one.

The certificate says that the block **runs out of steps**.  "Runs out of steps" is `SN`,
which is defined from `Step`, which is a relation **on `Term`**.  A constructor of `Term`
may not mention a relation defined on `Term`: `Term` does not exist yet while its own
constructors are being declared.  The same objection rules out a certificate phrased with
the evaluator, with the logical relation, or with any other semantic notion.

There are exactly two ways out.

* **Make the certificate syntactic** — a decidable shape condition, checkable while the
  term is being built, e.g. "the loop's counter is a variable that is structurally
  decomposed at every back edge".  This is representable inside `Term`.  It is also
  *incomplete*, necessarily: by the diagonal argument of `TERMINATING_TERM_ASSESSMENT.md`
  §2, no sound decidable criterion admits every Lean function Lean itself accepts as
  total.  A syntactic discipline is an ergonomic fast path, never the whole language.

* **Stratify.**  Build the plain grammar first; define `Step`, `SN` and `Tail.Certified`
  on it; then define a *second* grammar whose constructors take the certificate as a
  field.  This is what `CTerm` is.

The second was chosen, and the stratification costs nothing:

```lean
def     CTerm.ofTerminating (t : Term Sg Γ τ) (h : t.Terminating) : CTerm Sg Γ τ
theorem CTerm.erase_ofTerminating : (CTerm.ofTerminating t h).erase = t
```

Every term the extrinsic predicate admits is the erasure of a `CTerm`, and erasing gives
the original back.  The intrinsic and the extrinsic certified languages are the **same
language**; `CTerm` is `Term.Terminating` with the proof obligations distributed over the
constructors instead of collected in a predicate.  (The reverse composite is an equality
of proof fields, which are `Prop`s, hence irrelevant.)

## 2. What the constructors ask for

`CTerm` is `Term` constructor for constructor.  Only two constructors ask for anything
extra, and they are exactly the two places where `Term.Terminating` is not automatic:

| constructor | extra field | why |
| :-- | :-- | :-- |
| `CTerm.block b hg cert` | `cert : b.Certified`, `hg : τ.ground = true` | a block is the one construct that can repeat work |
| `CTerm.proj e i j hOne h hg` | `hg : τ.ground = true` | a field read at a function type waits on hereditary reducibility |

Everything else — `var`, `lam`, `ap`, `lit`, `global`, `extern`, `lazyMk`, `lazyForce`,
`letE`, `ite`, `ctor`, `tagOf`, `caseTag` — is the constructor of `Term` with `CTerm`
subterms and **no** proof argument.  In particular:

* **the λ-calculus core is free.**  `Term.ap` asks for `σ ⇒ τ` and `σ`, so `x x` is not
  typeable at any `Ty`; there is no fixed-point combinator and no recursive constructor.
* **recursive data is free**, because `RTy.wf` is strictly positive: a recursive
  declaration may not mention itself in the domain of an arrow, so Curry's `Ω` — which
  `LakeJs/DivergeNeg.lean` used to write at `μX. { f : X → Nat, … }` — is not even a type
  any more.

So the whole proof obligation of the language is *one field of one constructor*, and it
is the field the assessment predicted (`TERMINATING_TERM_ASSESSMENT.md` §4.2).

## 3. How a block is actually written

Writing `b.Certified` by hand is not the intended route.  `LakeJs/CertGen.lean` produces
certificates mechanically, and `LakeJs/TermC.lean` wraps them as smart constructors:

```lean
def CTerm.blockFlat     (b) (hg : τ.ground = true) (hb : b.Flat)     : CTerm Sg Γ τ
def CTerm.blockLoopFree (b) (hg : τ.ground = true) (hb : b.LoopFree) : CTerm Sg Γ τ
```

* `blockFlat` — a block with no label in it: straight-line code with branches;
* `blockLoopFree` — a block **all of whose labels are join points**, nested ones
  included.

Both side conditions are structural and are discharged by `⟨rfl, trivial, …⟩` or by
`decide`-like bookkeeping, so the decidable part of the language needs no proof at the use
site.  `cBlockLet` and `cSharedTail` in `LakeJs/TermC.lean` are worked examples: a
jump-free block, and a block with a join point reached from both arms of a branch, neither
of which mentions a certificate.

## 4. The guarantee has teeth

The grammar would be worthless if the certificate were satisfiable by anything.  It is
not:

```lean
theorem CTerm.erase_ne_loopForever (t : CTerm Sg [] (.prim .nat)) : t.erase ≠ loopForever
```

`loopForever` — `l: while (true) { continue l }` — is a perfectly good `Term`, and it is
the erasure of no `CTerm` whatsoever.  That is the intended difference between the two
grammars: `Term` can express a divergent program, which the backend still needs (the
`partial` Lean functions of `SnapshotsPBOPartial` must stay compilable), and `CTerm`
cannot.

## 5. What is still missing, and it is one thing

**A certificate generator for the loop.**  Today a `CTerm` may contain a block whose
labels are join points; a block with a *self* label — a `while` — needs its certificate
supplied by hand, and no generator produces one.

This is not an oversight and it is not fixable by a better shape condition: by §2 of the
assessment, the loop certificate of a general compiled Lean function has to be
**transported from the termination proof Lean already has** for the source function
(`termination_by` / `decreasing_by`, or the structural descent `brecOn` was compiled
from).  That is front-end work, and it cannot be exercised while `LakeJs/FromLcnf.lean`
and `LakeJs/Compile.lean` are empty.

Two intermediate generators are worth having when the front end returns, in this order:

1. **Structural descent** — the loop's designated parameter is a field of the value it had
   on the previous iteration.  This covers `brecOn`-compiled functions, which are the bulk
   of `SnapshotsPBOPure`.
2. **A counted loop** — the loop carries a `nat` parameter that strictly decreases at every
   back edge.  This is the "variant rule" of the block language: one proof, reusable by
   every `termination_by` measure that is a `Nat`.

Both are instances of one missing lemma — *a block whose transition relation on closed
parameter values is well founded is certified* — which is the semantic counterpart of the
join-point generator of `LakeJs/CertGen.lean`, with the induction on a measure of the
closing environment rather than on `Tail.inlineSize`.

The other standing restriction is unchanged: a certified block answers at a value type,
and so does a field read, until hereditary reducibility for constructors is proved
(`TERMINATING_TERM_ASSESSMENT.md` §4.3(3)).  Every compiled root answers with data, so no
program of the corpus is affected.

## 6. Where to look

| file | what it holds |
| :-- | :-- |
| `LakeJs/TermC.lean` | `CTerm`, `CSpine`, `CAlts`; `erase`; the termination theorems; `ofTerminating` and the round trip; the smart constructors and the examples |
| `LakeJs/Terminating.lean` | `Tail.Certified`, `Term.Terminating`, `CertifiedTerm` — the extrinsic layer `CTerm` is built on |
| `LakeJs/CertGen.lean` | the certificate generators, and the proof that the diverging block has none |
| `LakeJs/TermTotal.lean` | `SN`, halting and the fuel-free evaluator the guarantee is drawn from |
| `TERMINATING_TERM_ASSESSMENT.md` | the design space (A–E), the diagonal argument, the plan of record |
