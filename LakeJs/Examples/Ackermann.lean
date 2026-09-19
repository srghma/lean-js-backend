module

public import LakeJs.Examples.Ops

@[expose] public section

set_option autoImplicit false

-- Running the term inside the kernel unrolls the recursion once per call of `ack`, and
-- even a small `ack` performs a great many of them.
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Ackermann: **one** recursion, with a two-component lexicographic measure

```lean
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
```

Lean elaborates this by well-founded recursion on the **lexicographic** order of
`(m, n)`, and `Term.fix` carries exactly that: a `k`-component measure, compared
lexicographically by the evaluator at each self call.  So the translation is verbatim —

* `ps = [nat, nat]`: the two arguments, `m` and `n`;
* `k = 2` and `measure = [m, n]`: Lean's `termination_by m n => (m, n)`, transcribed;
* the three calls of the body are ordinary self calls, and the evaluator checks each of
  them: `(m, n - 1)` keeps the head and descends in the tail, `(m - 1, …)` descends in the
  head, whatever its second argument is — including the *nested* call
  `ack m (ack (m + 1) n)`, which no analysis of the arguments has to understand.

This is what the lexicographic measure buys, and it is worth spelling out because the
previous design could not do it.  With a single counted `Nat` rank, Ackermann had to be **curried
into two nested recursions**, one per component of the measure, and the front end had to
decide, for each self call, *which* of the two it belonged to — a syntactic analysis of
the call's arguments, with a default when it could not tell.  `RankFlakiness/` contains
the counterexample that made the point: a one-token change to the *unchanged* argument of
the inner call, which Lean accepts with the same `termination_by`, defeated the analysis
and produced a term the driver reported as `checked` and which computed a different
function.

Here there is nothing to analyse.  The measure is read off `termination_by`, the calls are
calls, and the descent is checked when the term runs.

The theorem below is the general statement: the term is Lean's `ack`, at **every** pair of
arguments.
-/

namespace LakeJs.Expr.Examples

open LakeJs
open LakeJs.Ty
open LakeJs.Expr.Ops

variable {Sg : Sig}

/-- The Lean function the term is meant to implement. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

/-- `ack 0 n = n + 1`. -/
theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by simp [ack]

/-- `ack (k + 1) 0 = ack k 1`: the call that drops the first component. -/
theorem ack_succ_zero (k : Nat) : ack (k + 1) 0 = ack k 1 := by simp [ack]

/-- `ack (k + 1) (i + 1) = ack k (ack (k + 1) i)`: the nested call. -/
theorem ack_succ_succ (k i : Nat) : ack (k + 1) (i + 1) = ack k (ack (k + 1) i) := by
  simp [ack]

/-- The signature of the recursion: two `Nat` arguments, a `Nat` answer.  There is only
    one, where the counted-rank encoding needed two nested ones. -/
abbrev ackSig : RSig := ⟨[Ty.nat, Ty.nat], Ty.nat⟩

/-- The body, in the context `m :: n :: []`:

    ```
    if m = 0 then n + 1
    else if n = 0 then self (m - 1) 1
    else self (m - 1) (self m (n - 1))
    ```

    Every call is a call of the *same* recursion; the evaluator compares `[m, n]`
    lexicographically at each of them. -/
def ackBody : Term Sg [Ty.nat, Ty.nat] [ackSig] Ty.nat :=
  .ite (natEq (♯0) (Term.natL 0))
    (natAdd (♯1) (Term.natL 1))
    (.ite (natEq (♯1) (Term.natL 0))
      (.selfCall .head (.cons (natSub (♯0) (Term.natL 1)) (.cons (Term.natL 1) .nil)))
      (.selfCall .head
        (.cons (natSub (♯0) (Term.natL 1))
          (.cons (.selfCall .head
              (.cons (♯0) (.cons (natSub (♯1) (Term.natL 1)) .nil))) .nil))))

/-- `ack`, as a term: one `fix` of two arguments, with the measure `[m, n]`. -/
def ackTerm : Term Sg [] [] (.nat ⇒ .nat ⇒ .nat) :=
  .fix [Ty.nat, Ty.nat] 2 (.cons (♯0) (.cons (♯1) .nil)) ackBody (Term.natL 0)

/-- The Lean function, as a function of an argument environment. -/
def ackFun (as : Env [Ty.nat, Ty.nat]) : Ty.nat.den :=
  ack (as.get .head) (as.get (.tail .head))

/-- The measure, as a function of an argument environment: `(m, n)`. -/
def ackMeasure (as : Env [Ty.nat, Ty.nat]) : Lex.NatVec 2 :=
  .cons (as.get .head) (.cons (as.get (.tail .head)) .nil)

/-- **Faithfulness**: the term is `ack`, at every pair of arguments.  The only thing the
    proof has to supply is the descent of `[m, n]` at each of the three calls — which is
    what Lean's own `decreasing_by` established. -/
theorem ackTerm_implements (δ : GEnv Sg.decls) :
    (ackTerm (Sg := Sg)).Implements δ ackFun := by
  intro args
  refine Term.fix_implements_closed _ ackBody (Term.natL 0) δ ackFun ackMeasure
    (fun as => ?_) (fun g as hg => ?_) args
  · match as with
    | .cons _ (.cons _ .nil) => rfl
  · match as with
    | .cons m (.cons n .nil) =>
      cases (m : Nat) with
      | zero =>
        show (show Nat from n) + 1 = ack 0 n
        rw [ack_zero]
      | succ k =>
        cases (n : Nat) with
        | zero =>
          have hdrop : Lex.NatVec.Lt (ackMeasure (.cons (k : Nat) (.cons (1 : Nat) .nil)))
              (ackMeasure (.cons (k + 1 : Nat) (.cons (0 : Nat) .nil))) :=
            Lex.NatVec.Lt.head (Nat.lt_succ_self k)
          show g (.cons (k : Nat) (.cons (1 : Nat) .nil)) = ack (k + 1) 0
          rw [hg (.cons (k : Nat) (.cons (1 : Nat) .nil)) hdrop, ack_succ_zero]
          rfl
        | succ i =>
          have htail : Lex.NatVec.Lt
              (ackMeasure (.cons (k + 1 : Nat) (.cons (i : Nat) .nil)))
              (ackMeasure (.cons (k + 1 : Nat) (.cons (i + 1 : Nat) .nil))) :=
            Lex.NatVec.Lt.tail (Lex.NatVec.Lt.head (Nat.lt_succ_self i))
          have hhead : Lex.NatVec.Lt
              (ackMeasure (.cons (k : Nat) (.cons (ack (k + 1) i) .nil)))
              (ackMeasure (.cons (k + 1 : Nat) (.cons (i + 1 : Nat) .nil))) :=
            Lex.NatVec.Lt.head (Nat.lt_succ_self k)
          have hinner : g (.cons (k + 1 : Nat) (.cons (i : Nat) .nil)) = ack (k + 1) i := by
            rw [hg (.cons (k + 1 : Nat) (.cons (i : Nat) .nil)) htail]
            rfl
          show g (.cons (k : Nat)
                  (.cons (g (.cons (k + 1 : Nat) (.cons (i : Nat) .nil))) .nil))
              = ack (k + 1) (i + 1)
          rw [hinner, hg (.cons (k : Nat) (.cons (ack (k + 1) i) .nil)) hhead,
            ack_succ_succ]
          rfl

/-- The term, at a pair of arguments. -/
theorem ackTerm_eq (m n : Nat) : Term.runNat2 ackTerm m n = ack m n := by
  have h := ackTerm_implements (Sg := ⟨[], by decide⟩) .nil (.cons m (.cons n .nil))
  show Env.apply ((ackTerm (Sg := ⟨[], by decide⟩)).evalClosed .nil)
      (.cons m (.cons n .nil)) = ack m n
  exact h


example : Term.runNat2 ackTerm 0 5 = 6 := rfl
example : Term.runNat2 ackTerm 1 3 = 5 := rfl
example : Term.runNat2 ackTerm 2 2 = 7 := rfl

-- Larger values are not reduced here: `ack 3 1` is a few thousand calls, and the kernel
-- unrolls the recursion once per call.  The general theorem gives them with no
-- computation at all.
/-- `ack 3 1`, from the theorem rather than from the kernel. -/
example : Term.runNat2 ackTerm 3 1 = ack 3 1 := ackTerm_eq 3 1

end LakeJs.Expr.Examples

end
