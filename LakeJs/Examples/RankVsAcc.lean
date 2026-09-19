module

public import LakeJs.Examples.WellFounded

@[expose] public section

set_option autoImplicit false

/-!
# Why a computed measure, and not an `Acc` field

The alternative to a computed measure is to let `Term.fix` carry Lean's own termination
evidence:

```lean
| fixAcc : (r : α → α → Prop) → (hwf : WellFounded r) → (measure : Env ps → α) → …
```

and to run it with `WellFounded.fix`.  That would need no comparison at run time, and it
would admit functions whose measure is not computable.  Three facts decide against it for
this backend; the first is the one this file *proves*.

## 1. After erasure the evidence does not exist

The front end reads the `saveBase` LCNF phase, from which every `Prop` argument has been
erased.  For a function that terminates only *because* of such an argument, the function
the front end sees genuinely does not terminate, so there is no `Acc` for it to carry —
not "it is hard to find", but "it does not exist".

`Tco07.boom` is the smallest case:

```lean
def Safe (n : Nat) : Prop := n = 1
def boom (n : Nat) (h : Safe n) : Nat :=
  if hn : n = 1 then 0 else boom (3 * n) (by simp [Safe] at h; omega)
termination_by n
```

After erasure the call relation is `boomStep y x := y = 3 * x`, and
`not_acc_boomStep` below says that no value except `0` is accessible for it.  So a
`fixAcc` term for the erased `boom` cannot be built at all, while the measured term is
built and *runs*: `LakeJs.Expr.Examples.boomTerm_at_two` says it answers at `2`, an input
Lean's `boom` cannot even be applied to.

The measure survives erasure because it is a *number computed from the surviving
arguments*, and it is sound for a reason that does not mention the erased proof: the
semantics recurses only when the measure at the call is strictly smaller than the measure
of the activation the call is made from, so the recursion stops whatever the reason Lean
had.  It is weaker — outside the precondition the term answers the `stuck` branch rather
than Lean's (non-existent) value — and that weakness is stated per example rather than
glossed over.

## 2. A carried `Acc` is not syntax

`r`, `hwf` and `measure` are Lean objects over *denotations*, not `Term`s.  A `Term`
carrying them is no longer a first-order tree: it cannot be printed to a `-Expr.txt`,
re-elaborated from one, or compared with the output of another pass — and the round-trip
milestone of `TERM_ONE_GRAMMAR_ASSESSMENT.md` §7 is exactly that.  A measure component is
an ordinary `Term`, so it prints, parses and optimises like everything else.

## 3. What is genuinely lost

A measure that is not computable — `Classical.choose`, for instance — has no `Term`,
because the evaluator has to evaluate the measure at every self call.  Lean will happily define such
a function (the proof is erased and the compiled code loops), and this backend will refuse
it.  That is a real restriction, and it is the price of the other two points; no function
of the corpus is affected.

A lexicographic measure is *not* in that category: see `LakeJs.Examples.Ackermann`, where
`(m, n)` becomes the two-component measure of a single recursion.
-/

namespace LakeJs.Expr.Examples

/-- The call relation of `Tco07.boom` **after erasure**: the body calls itself at `3 * n`
    (and the `Prop` argument that ruled that branch out is gone). -/
def boomStep (y x : Nat) : Prop := y = 3 * x

/-- Nothing but `0` is accessible for the erased call relation: the chain
    `x → 3x → 9x → ⋯` never comes back. -/
theorem acc_boomStep_eq_zero : ∀ x : Nat, Acc boomStep x → x = 0 := by
  intro x h
  induction h with
  | intro y _ ih =>
    by_cases hy : y = 0
    · exact hy
    · exact absurd (ih (3 * y) rfl) (by omega)

/-- **The erased `boom` has no well-founded certificate.**  So a `Term` constructor that
    carried Lean's `Acc` could not represent it, whereas the measured `boomTerm` both
    exists and answers (`boomTerm_at_two`). -/
theorem not_acc_boomStep : ¬ Acc boomStep 2 := by
  intro h
  exact absurd (acc_boomStep_eq_zero 2 h) (by decide)

/-- The contrast, side by side: the measured term answers at the very input for which no
    `Acc` exists. -/
example : ¬ Acc boomStep 2 ∧ Term.runNat1 boomTerm 2 = 0 :=
  ⟨not_acc_boomStep, boomTerm_at_two⟩

end LakeJs.Expr.Examples

end
