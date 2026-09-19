/-
The term the front end emitted for `RankFlakiness/AckOpaqueArg.lean`, run against the Lean
function it was translated from.

`ackOpaque` *is* Ackermann: the only difference from `SnapshotsMy/Tco08.lean` is that the
first argument of the inner recursive call is written `2 * (m + 1) - (m + 1)` rather than
`m + 1`.

**This file used to record a counterexample.**  Under the old, counted-rank grammar the
driver translated `ackOpaque`, reported `checked` — so the emitted term was a term of the
grammar and terminating by construction — and computed a *different function*, with no
diagnostic anywhere: 11 of the 16 inputs of the 4 × 4 square disagreed.  The cause was the
rank, not the grammar.  The front end decided which level of the nest of ranked `fix`es a
self call belonged to by a syntactic linear normal form of its arguments;
`2 * (m + 1) - (m + 1)` has no such normal form, so the call — which leaves `m` unchanged
— was taken to be a call of the *outer*, `m`-ranked recursion, whose rank ran out and
whose `exhausted` branch answered `0`.

Under the current grammar there is no level to assign and no iteration bound to compute:
`ackOpaque` becomes the single `fix (nat nat) measure [ ♯0, ♯1 ]` — `termination_by
m n => (m, n)`, transcribed verbatim — and a self call simply supplies both arguments,
whatever they are written as.  The disagreement is therefore gone, which is the acceptance
criterion the migration named for this file.  The theorems below check that: they are the
negations of the ones this file used to hold, and the old statements are kept, commented
out, underneath them.
-/

import RankFlakiness.AckOpaqueArgProgram
import RankFlakiness.AckOpaqueArg

open LakeJs LakeJs.Expr ProgramRankFlakinessAckOpaqueArg

namespace RankFlakiness.AckOpaqueArgCheck

/-- `ackOpaque`, as the emitted term computes it. -/
def runAckOpaque (m n : Nat) : Nat := Term.run tm_ackOpaque m n

/-- The emitted term and the Lean function, side by side. -/
def table (bound : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range bound).flatMap fun m =>
    (List.range bound).map fun n => (m, n, runAckOpaque m n, ackOpaque m n)

/-- The disagreements on the `bound` × `bound` square. -/
def disagreements (bound : Nat) : List (Nat × Nat × Nat × Nat) :=
  (table bound).filter fun (_, _, a, b) => a != b

/-- The emitted term agrees with the Lean function everywhere on the 4 × 4 square: the
    translation of `ackOpaque` is faithful. -/
theorem ackOpaque_term_agrees : disagreements 4 = [] := by native_decide

/-- The smallest input the old translation got wrong. -/
theorem ackOpaque_term_right_at_one_one : runAckOpaque 1 1 = ackOpaque 1 1 := by
  native_decide

/-- An input the old translation happened to get right. -/
theorem ackOpaque_term_right_at_one_zero : runAckOpaque 1 0 = ackOpaque 1 0 := by
  native_decide

/-
The statements this file used to hold, against the counted-rank grammar.  They are false
of the term the current front end emits — the disagreement they record has been fixed —
so they are kept here as the record of what changed rather than as claims:

  -- #eval disagreements 4
  -- [(1, 1, 1, 3), (1, 2, 1, 4), (1, 3, 1, 5), (2, 0, 1, 3), (2, 1, 2, 5), (2, 2, 2, 7),
  --  (2, 3, 2, 9), (3, 0, 2, 5), (3, 1, 1, 13), (3, 2, 1, 29), (3, 3, 1, 61)]

  /-- The smallest disagreement: the emitted term answers `1` where `ackOpaque 1 1 = 3`. -/
  theorem ackOpaque_term_wrong_at_one_one : runAckOpaque 1 1 ≠ ackOpaque 1 1 := by
    native_decide

  /-- Eleven of the sixteen inputs of the 4 × 4 square disagree. -/
  theorem ackOpaque_term_wrong_often : (disagreements 4).length = 11 := by native_decide
-/

end RankFlakiness.AckOpaqueArgCheck
