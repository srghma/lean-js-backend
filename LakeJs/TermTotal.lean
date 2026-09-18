module

public import LakeJs.Fundamental

@[expose] public section

/-!
# The evaluator is total on the certified language: no fuel, and always an answer

This is the conclusion of `LakeJs.SN`, `LakeJs.Fragment`, `LakeJs.Terminating`,
`LakeJs.Reducibility` and `LakeJs.Fundamental`.

* `Term.terminating_sn` — **a closed certified term runs out of steps**.
* `Term.terminating_halts` — and therefore **reaches an answer**: there is a `v` with
  `Steps t v` and `Value v`.
* `Term.evalSN` — the evaluator itself, as a **function**: it recurses on the proof that
  the term runs out of steps, so it takes **no fuel** and has no failure case, and it
  answers with a `v` *together with* the reduction that reaches it and the proof that it
  is an answer.
* `Term.eval`, `Term.eval_steps`, `Term.eval_value`, `Term.eval_total` — the same, for a
  closed certified term, with the side condition discharged once and for all.
* `CertifiedTerm.eval` and `CertifiedTerm.eval_total` — the same again, for a term that
  carries its certificate with it.

The old, *decidable* fragment `Term.simple` is a special case: it has no block in it, so
its certificate is vacuous (`Term.terminating_of_simple`), and `Term.simple_sn`,
`Term.simple_halts` and `Term.evalSimple` below are the corollaries.

## What is left out, and why

No evaluator of the *whole* language can be total: `LakeJs.Diverge` exhibits a closed
term, `loopForever`, that steps only to itself and so reaches no answer at all
(`loopForever_no_answer`).  What the certificate buys is that a block is admitted as soon
as it can be *proved* to run out of steps, rather than refused outright; by the diagonal
argument of `TERMINATING_TERM_ASSESSMENT.md` §2 no decidable criterion could admit every
terminating one.  `LakeJs.CertGen` derives certificates mechanically for the block shapes
that admit it.

Two restrictions remain inside the certified language: a certified block answers at a
value type, and so does a field read (`LakeJs.Fragment`, `LakeJs.Terminating`).  Both wait
on hereditary reducibility for constructors.

## Why the evaluator is noncomputable

`Step` is a *relation*, and not a deterministic one: `Step.quick` lets
`lean_sharecommon_quick v` answer straight away while `Step.apArg` would run its argument
first.  So "the" next term is a choice, and `Term.evalSN` makes it with `Classical.choose`
— which costs nothing in the statement being proved, since every choice leads to an
answer.  What is *not* a choice is that the recursion stops: that is the content of
`Term.terminating_sn`.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

open scoped Classical

variable {Sg : Sig}

/-! ## A closed certified term runs out of steps -/

/-- **A closed certified term runs out of steps.**  The fundamental theorem under the
    empty substitution, which changes nothing. -/
theorem Term.terminating_sn {τ : Ty} (t : Term Sg [] τ) (hs : t.Terminating) : t.SN := by
  have h := Term.fundamental t VSub.id RedSub.nil hs
  rw [Term.subst_id] at h
  exact h.sn

/-- **A closed certified term reaches an answer.** -/
theorem Term.terminating_halts {τ : Ty} (t : Term Sg [] τ) (hs : t.Terminating) :
    ∃ v : Term Sg [] τ, Steps t v ∧ Value v :=
  (t.terminating_sn hs).halts

/-- **A closed term of the decidable fragment runs out of steps.** -/
theorem Term.simple_sn {τ : Ty} (t : Term Sg [] τ) (hs : t.simple = true) : t.SN :=
  t.terminating_sn (t.terminating_of_simple hs)

/-- **A closed term of the decidable fragment reaches an answer.** -/
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

/-- **The answer a closed certified term evaluates to.**  Total: every closed certified
    term has one, and no fuel is asked for. -/
noncomputable def Term.eval {τ : Ty} (t : Term Sg [] τ) (hs : t.Terminating) :
    Term Sg [] τ :=
  (Term.evalSN (t.terminating_sn hs)).1

/-- The evaluator's answer is reached from the term. -/
theorem Term.eval_steps {τ : Ty} (t : Term Sg [] τ) (hs : t.Terminating) :
    Steps t (t.eval hs) :=
  (Term.evalSN (t.terminating_sn hs)).2.1

/-- **The evaluator's answer is an answer.** -/
theorem Term.eval_value {τ : Ty} (t : Term Sg [] τ) (hs : t.Terminating) :
    Value (t.eval hs) :=
  (Term.evalSN (t.terminating_sn hs)).2.2

/-- **Totality, in one statement**: running a closed certified term answers with a value,
    reached by the reduction relation, with no fuel anywhere in sight. -/
theorem Term.eval_total {τ : Ty} (t : Term Sg [] τ) (hs : t.Terminating) :
    Steps t (t.eval hs) ∧ Value (t.eval hs) :=
  ⟨t.eval_steps hs, t.eval_value hs⟩

/-! ## The certified term, evaluated -/

/-- **Running a closed `CertifiedTerm`.**  The certificate travels with the term, so
    there is no side condition left to discharge at the call site. -/
noncomputable def CertifiedTerm.eval {τ : Ty} (t : CertifiedTerm Sg [] τ) :
    Term Sg [] τ :=
  t.term.eval t.cert

/-- **Every closed `CertifiedTerm` evaluates to an answer.** -/
theorem CertifiedTerm.eval_total {τ : Ty} (t : CertifiedTerm Sg [] τ) :
    Steps t.term t.eval ∧ Value t.eval :=
  t.term.eval_total t.cert

/-! ## The certified language is not empty

A sanity check that the side condition is satisfiable, and that the evaluator really does
reduce: `(fun x => x) 1` is a closed term of the decidable fragment, and it reaches the
literal `1`. -/

/-- `(fun x => x) 1`, a closed term of the fragment. -/
def idAp : Term Sg [] (.prim .nat) :=
  .ap (.lam (.var .head)) (.lit (.nat 1))

/-- It is in the decidable fragment. -/
theorem idAp_simple : (idAp (Sg := Sg)).simple = true := rfl

/-- And therefore certified. -/
theorem idAp_terminating : (idAp (Sg := Sg)).Terminating :=
  Term.terminating_of_simple _ idAp_simple

/-- And it reduces to `1`, in one β step. -/
theorem idAp_steps : Steps (idAp (Sg := Sg)) (.lit (.nat 1)) :=
  Steps.single (Step.beta (Value.lit _))

end LakeJs.Expr

end
