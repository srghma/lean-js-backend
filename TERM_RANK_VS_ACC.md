# Ackermann, ranks, and `Acc`: what the grammar can and cannot represent

This note answers four questions about the one grammar of `LakeJs.Expr`:

1. can `ack` be turned into a `Term`, given that its `termination_by` is lexicographic?
2. is the rank just *fuel*, and does it have to be decremented all the time?
3. could the recursion carry Lean's `Acc` (or a `WellFounded` proof) instead of a rank —
   which would also admit functions whose termination proof is classical?
4. can the three de Bruijn families (`Var`, `LVar`, `RVar`) be collapsed into one?

Every claim below that is marked **proved** is a theorem in this project, built and
`sorry`-free; the rest is design discussion, marked as such.

---

## 1. `ack`: yes, and the ranks stay small — **proved**

```lean
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
```

The worry is real but is about one particular *shape*: if you insisted on one `fix` taking
`(m, n)` and one `Nat` rank counting all of its recursive calls, that rank would be about
the size of `ack m n`, and computing it would mean running the function.

The grammar does not force that shape.  `Term.fix ps rank body exhausted` answers with
`Ty.arrows ps τ`, and `τ` may itself be a function type, so a lexicographic recursion is
written as **one ranked recursion per component**:

* the outer `fix` takes `m`, is ranked by `m + 1`, and answers with a function
  `nat ⇒ nat`;
* inside it, the inner `fix` takes `n` and is ranked by `n + 1`;
* `ack m (…)` — the call that drops the first component — is a call of the **outer**
  self-reference, which is still in the recursion context (`self1` in the dump).  Making
  that call re-enters the outer recursion, which builds a fresh inner one: the inner rank
  is *reset*, which is exactly what "lexicographic" means.

`LakeJs/Examples/Ackermann.lean` builds that term and proves

```lean
theorem ackTerm_eq (m n : Nat) : Term.runNat2 ackTerm m n = ack m n
```

— faithfulness at **every** pair of arguments, not on sample inputs.  Both ranks are an
argument plus one; nothing anywhere computes a number of the size of `ack m n`.  The
*number of iterations* is of course still enormous — it is what `ack` costs — but no
single rank is.

So a lexicographic `termination_by` does not need a lexicographic rank in the grammar; it
needs the clique to be **curried into one `fix` per component**.  That is a translation
the front end performs, and it is the same trick as the tag-parameter merge that
`Tco03`/`Tco04` already use for a mutual clique.

Two caveats, stated honestly:

* the currying is a real transformation, not a transcription, and it is not written yet:
  the front end in this tree is the classifier (`LakeJs.Totality`), which accepts `ack`
  (Lean records it as well-founded recursion), while the LCNF-to-`Term` translation is not
  part of this tree (see `TERM_TOTAL_IMPLEMENTATION.md` §5);
* the alternative — a rank slot holding a list of `Nat`s compared lexicographically —
  remains a sensible extension, and is the only thing that would let a lexicographic
  measure be transcribed *verbatim*.  It changes `RSig` and `Term.fix` and nothing else.
  It is not needed for `ack`.

---

## 2. The rank is not fuel

Fuel is a resource threaded through a computation that may run out *before the answer* —
so a fuelled evaluator answers in `Option`, and a fuelled program is a different program.
The rank is neither of those:

* it is **an upper bound on the number of iterations**, computed once, at entry, from the
  arguments.  It does not have to be tight, and it is not part of the answer;
* **no term can see it.**  `RSig` records the argument types and the result type of a
  recursion and nothing else, so a `Term.selfCall` has no syntax for naming, inspecting,
  restoring or raising a rank.  The seal is the absence of a slot, not a check;
* the evaluator answers in `τ.den`, never in `Option`: there is no "out of fuel" value.
  A rank that was too small would make the term answer the `exhausted` branch — a wrong
  answer, caught by the faithfulness theorems, not an error case in the semantics.

Where the counting-down is real is the **evaluator**: `Term.eval` runs the object
recursion as `Nat.rec` on the rank, so evaluating inside the Lean kernel costs one
`Nat.rec` unrolling per iteration.  That is a property of this particular (denotational,
kernel-reducible) evaluator, not of the language: an emitter is free to print a `while`
whose condition is the function's own test and to keep no counter at all, because the rank
was only ever needed to justify that the loop stops.

---

## 3. Carrying `Acc` instead: what it buys and what it costs

The alternative is

```lean
| fixAcc : (r : α → α → Prop) → (hwf : WellFounded r) → (measure : Env ps → α) → …
```

run by `WellFounded.fix`.  It needs no counter, and it admits measures that cannot be
computed.  Three facts decide against it here; `LakeJs/Examples/RankVsAcc.lean` states
them, and **proves the first**.

### 3.1 After erasure the evidence does not exist — **proved**

The front end reads the `saveBase` LCNF phase, from which every `Prop` argument has been
erased.  For a function that terminates *because* of such an argument, the function the
front end sees does not terminate, so there is no `Acc` to carry — not "hard to find",
but "does not exist".  `Tco07.boom` is the smallest case: after erasure its call relation
is `y = 3 * x`, and

```lean
theorem not_acc_boomStep : ¬ Acc boomStep 2
```

is proved.  A `fixAcc` term for the erased `boom` therefore cannot be built at all —
while the ranked term is built and *runs*: `boomTerm_at_two` says it answers `0` at an
input Lean's `boom` cannot even be applied to.

This is the heart of the matter.  The rank survives erasure because it is a number
computed from the arguments that survive, and it is sound for a reason that never mentions
the erased proof.

### 3.2 A carried `Acc` is not syntax

`r`, `hwf` and `measure` are Lean objects over *denotations*, not `Term`s.  A `Term`
carrying them is no longer a first-order tree: it cannot be printed into a `-Expr.txt`,
re-elaborated from one, or compared with the output of a pass — and print/re-elaborate/
compare is the round-trip milestone of `TERM_ONE_GRAMMAR_ASSESSMENT.md` §7.  A rank is an
ordinary `Term`: it prints, parses and optimises like everything else.

### 3.3 What is genuinely lost

A measure that is **not computable** has no rank term, because the evaluator must evaluate
the rank at entry.  The `findFirst` example is exactly that: its measure is
`h.choose - n`, and `h.choose` is `Classical.choose`.  Lean compiles such a function
(the proof is erased and the code loops), so *emitting JavaScript* for it would be fine;
what fails is the verified model, which would have to produce a bound it cannot compute.
This backend refuses it.  No function of the snapshot corpus is affected.

If one wanted it anyway, the honest options are: expose a computable bound (often there is
one — for `findFirst`, none, since the search may run arbitrarily long); or add a second,
clearly-marked recursion constructor carrying `Acc`, accepting that terms built with it
are not printable and that the front end can only produce it for functions with **no**
erased `Prop` arguments in their termination argument.  That is a genuine widening of the
language, and it is also a genuine weakening of "terminating by construction", since the
evidence then lives in a proof rather than in the shape of the syntax.

---

## 4. One de Bruijn family instead of four — **done**

`Var`, `LVar` and `RVar` were three copies of the same inductive at three entry types, and
`GlobalRef` was a fourth copy differing only in that its index is a *projection* of the
entry.  They are now all one family, parameterised by that projection:

```lean
inductive DeBruijnProj {α β : Type} (f : α → β) : List α → β → Type
  | head : DeBruijnProj f (x :: xs) (f x)
  | tail : DeBruijnProj f xs b → DeBruijnProj f (x :: xs) b

abbrev DeBruijn (xs : List α) (x : α) : Type := DeBruijnProj id xs x

abbrev Var  (Γ : Ctx)  (τ : Ty)       : Type := DeBruijn Γ τ
abbrev LVar (Ω : LCtx) (ps : List Ty) : Type := DeBruijn Ω ps
abbrev RVar (Ρ : RCtx) (r : RSig)     : Type := DeBruijn Ρ r

abbrev GlobalRef (ds : List GlobalDecl) (τ : Ty) : Type :=
  DeBruijnProj GlobalDecl.ty ds τ
```

with `DeBruijnProj.index` in place of the separate `index` functions, and
`Var.head`/`Var.tail` (and the label, recursion and global versions — the latter still
spelled `GlobalRef.here`/`GlobalRef.there`) kept as `@[match_pattern]` abbreviations, so
that existing code, existing patterns and the `♯n` notation are unchanged.  The whole
library — substitution, the lemmas, the evaluator, the metatheory and the examples —
builds essentially unmodified, because the four families were the same structure.

The projection also removes the duplicated lookups: `DeBruijnProj.entry` gives the entry
an index points at, `DeBruijnProj.entry_mem` says it is one of the entries — together
they are all that `GlobalRef.name` and `GlobalRef.name_mem` now are — and
`DeBruijnProj.f_entry` records that `f` of the entry is the index (`rfl` at `f := id`,
and "a reference's declaration has the reference's type" at `f := GlobalDecl.ty`).

Notes on the edges:

* the three notations `∋`, `∋ₗ`, `∋ᵣ` are worth keeping even though they now mean the same
  function: they say *which* scope is meant at a glance, and a mistyped one is still a
  type error, since the entry types differ;
* the cost of the generalisation is that a `match` on a `DeBruijn` now also scrutinises
  the index `id x`, so a handful of `simp only […]` steps that used to unfold the old
  match equations became plain `rfl`;
* the saving is one inductive to eliminate over and one `index` function instead of four;
  the renaming and substitution machinery is still written per scope, because it moves
  different contexts, but it could now be shared where the operations coincide.
