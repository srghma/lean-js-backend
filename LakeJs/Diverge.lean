module

public import LakeJs.Progress

@[expose] public section

/-!
# A closed term that never answers: why the *whole* language has no total evaluator

`LakeJs.Reduce` runs a `Term`, and `LakeJs.Progress` says it never gets stuck: a closed
term is an answer or it takes a step.  The remaining question is whether the steps ever
*stop* — whether the evaluator is **total**, so that running a closed term needs no fuel
and always ends in a value.

For the language as a whole the answer is **no**, and this file proves it with the
smallest possible witness.  A `Tail.label` with `self = true` is the one construct that
repeats work, and a block whose only label is a loop that jumps straight back to itself

```
l: while (true) { continue l }
```

is a closed term of *any* type that steps only to itself:

* `loopForever_step_self` — it takes a step, to itself;
* `loopForever_not_value` — it is not an answer;
* `loopForever_steps_eq` — *every* term it reaches is itself, so there is no answer
  anywhere in its reduction, however long one runs it.

That is the honest scope statement for totality: an evaluator of the full language must
either take a fuel or fail to be a function.  `LakeJs.TermTotal` proves the positive
result for the fragment that leaves `Term.block` out — which is the fragment the front
end produces for a non-recursive declaration with no shared tail, and which is where a
*total* evaluator lives.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

/-- `l: while (true) { continue l }`: the block whose one label takes no arguments, is a
    loop, and does nothing but jump to itself.  It is closed — no variable and no free
    label — and it is a term of every type. -/
def loopForever {Sg : Sig} {τ : Ty} : Term Sg [] τ :=
  .block (.label (ps := []) true (.jmp .head .nil) (.jmp .head .nil))

/-- **It steps to itself.**  Substituting the loop for its own label turns the jump that
    entered it back into the same loop, so the reduction sequence is infinite. -/
theorem loopForever_step_self {Sg : Sig} {τ : Ty} :
    Step (loopForever (Sg := Sg) (τ := τ)) loopForever :=
  Step.blockStep StepT.labelLoop

/-- It is not an answer: no `Value` is a loop. -/
theorem loopForever_not_value {Sg : Sig} {τ : Ty} :
    ¬ Value (loopForever (Sg := Sg) (τ := τ)) := by
  intro hv
  cases hv with
  | neutral hn => cases hn with | block htn => cases htn

/-- **The only term it steps to is itself.** -/
theorem loopForever_step_eq {Sg : Sig} {τ : Ty} {t : Term Sg [] τ}
    (h : Step (loopForever (Sg := Sg) (τ := τ)) t) : t = loopForever := by
  cases h with
  | blockStep hst => cases hst with | labelLoop => rfl

/-- …and so the only term it *reaches* is itself. -/
theorem loopForever_steps_eq {Sg : Sig} {τ : Ty} {t : Term Sg [] τ}
    (h : Steps (loopForever (Sg := Sg) (τ := τ)) t) : t = loopForever := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => subst ih; exact loopForever_step_eq hstep

/-- **A closed term of the full language need never answer.**  There is no value the
    loop reaches, so no evaluator of the whole language is a total function of a closed
    term: a self-label has to be left out, and `LakeJs.TermTotal` leaves it out. -/
theorem loopForever_no_answer {Sg : Sig} {τ : Ty} :
    ¬ ∃ v : Term Sg [] τ, Steps loopForever v ∧ Value v := by
  rintro ⟨v, hsteps, hv⟩
  exact loopForever_not_value (loopForever_steps_eq hsteps ▸ hv)

end LakeJs.Expr

end
