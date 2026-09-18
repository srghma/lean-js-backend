module

public import LakeJs.Fundamental

@[expose] public section

/-!
# The evaluator is total on the fragment: no fuel, and always an answer

This is the conclusion of `LakeJs.SN`, `LakeJs.Fragment`, `LakeJs.Reducibility` and
`LakeJs.Fundamental`.

* `Term.simple_sn` — **a closed term of the fragment runs out of steps**.
* `Term.simple_halts` — and therefore **reaches an answer**: there is a `v` with
  `Steps t v` and `Value v`.
* `Term.evalSN` — the evaluator itself, as a **function**: it recurses on the proof that
  the term runs out of steps, so it takes **no fuel** and has no failure case, and it
  answers with a `v` *together with* the reduction that reaches it and the proof that it
  is an answer.
* `Term.eval`, `Term.eval_steps`, `Term.eval_value`, `Term.eval_total` — the same, for a
  closed term of the fragment, with the side condition discharged once and for all.

## What the fragment leaves out, and why

No evaluator of the *whole* language can be total: `LakeJs.Diverge` exhibits a closed
term, `loopForever`, that steps only to itself and so reaches no answer at all
(`loopForever_no_answer`).  A `Tail.label` with `self = true` is the one construct of the
language that repeats work, and the whole block grammar is excluded here — along with a
field read at a function or delayed result type, which the argument of
`LakeJs.Reducibility` does not cover.  `LakeJs.Fragment` is the precise statement of the restriction, and
`EVALUATOR_TOTALITY.md` discusses it.

## Why the evaluator is noncomputable

`Step` is a *relation*, and not a deterministic one: `Step.quick` lets
`lean_sharecommon_quick v` answer straight away while `Step.apArg` would run its argument
first.  So "the" next term is a choice, and `Term.evalSN` makes it with `Classical.choose`
— which costs nothing in the statement being proved, since every choice leads to an
answer.  What is *not* a choice is that the recursion stops: that is the content of
`Term.simple_sn`.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

open scoped Classical

variable {Sg : Sig}

/-! ## A closed term of the fragment runs out of steps -/

/-- **A closed term of the fragment runs out of steps.**  The fundamental theorem under
    the empty substitution, which changes nothing. -/
theorem Term.simple_sn {τ : Ty} (t : Term Sg [] τ) (hs : t.simple = true) : t.SN := by
  have h := Term.fundamental t VSub.id RedSub.nil hs
  rw [Term.subst_id] at h
  exact h.sn

/-- **A closed term of the fragment reaches an answer.** -/
theorem Term.simple_halts {τ : Ty} (t : Term Sg [] τ) (hs : t.simple = true) :
    ∃ v : Term Sg [] τ, Steps t v ∧ Value v :=
  (t.simple_sn hs).halts

/-! ## The evaluator -/

/-- **The evaluator, as a total function.**  It recurses on the proof that `t` runs out
    of steps — not on a fuel — and it has no failure case: progress says a closed term is
    either an answer, and then it is the answer, or takes a step, and then the same
    function runs on what it steps to, which runs out of steps in turn.

    It answers with the term *together with* the reduction that reaches it and the proof
    that it is an answer, so the specification is the type. -/
noncomputable def Term.evalSN {τ : Ty} {t : Term Sg [] τ} (h : t.SN) :
    { v : Term Sg [] τ // Steps t v ∧ Value v } :=
  Acc.rec (motive := fun t _ => { v : Term Sg [] τ // Steps t v ∧ Value v })
    (fun t _ ih =>
      if hv : Value t then ⟨t, .refl, hv⟩
      else
        let hex : ∃ t' : Term Sg [] τ, Step t t' := (Term.progress t).resolve_left hv
        let hst : Step t (Classical.choose hex) := Classical.choose_spec hex
        let r := ih _ hst
        ⟨r.1, Steps.head hst r.2.1, r.2.2⟩)
    h

/-- **The answer a closed term of the fragment evaluates to.**  Total: every closed term
    of the fragment has one, and no fuel is asked for. -/
noncomputable def Term.eval {τ : Ty} (t : Term Sg [] τ) (hs : t.simple = true) :
    Term Sg [] τ :=
  (Term.evalSN (t.simple_sn hs)).1

/-- The evaluator's answer is reached from the term. -/
theorem Term.eval_steps {τ : Ty} (t : Term Sg [] τ) (hs : t.simple = true) :
    Steps t (t.eval hs) :=
  (Term.evalSN (t.simple_sn hs)).2.1

/-- **The evaluator's answer is an answer.** -/
theorem Term.eval_value {τ : Ty} (t : Term Sg [] τ) (hs : t.simple = true) :
    Value (t.eval hs) :=
  (Term.evalSN (t.simple_sn hs)).2.2

/-- **Totality, in one statement**: running a closed term of the fragment answers with a
    value, reached by the reduction relation, with no fuel anywhere in sight. -/
theorem Term.eval_total {τ : Ty} (t : Term Sg [] τ) (hs : t.simple = true) :
    Steps t (t.eval hs) ∧ Value (t.eval hs) :=
  ⟨t.eval_steps hs, t.eval_value hs⟩

/-! ## The fragment is not empty

A sanity check that the side condition `t.simple = true` is satisfiable, and that the
evaluator really does reduce: `(fun x => x) 1` is a closed term of the fragment, and it
reaches the literal `1`. -/

/-- `(fun x => x) 1`, a closed term of the fragment. -/
def idAp : Term Sg [] (.prim .nat) :=
  .ap (.lam (.var .head)) (.lit (.nat 1))

/-- It is in the fragment. -/
theorem idAp_simple : (idAp (Sg := Sg)).simple = true := rfl

/-- And it reduces to `1`, in one β step. -/
theorem idAp_steps : Steps (idAp (Sg := Sg)) (.lit (.nat 1)) :=
  Steps.single (Step.beta (Value.lit _))

end LakeJs.Expr

end
