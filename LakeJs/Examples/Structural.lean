module

public import LakeJs.Examples.Ops
public import LakeJs.Program

@[expose] public section

set_option autoImplicit false

/-!
# Worked examples, kind S: structurally recursive Lean functions

Each example is a Lean function from the snapshot corpus (or modelled on one), the `Term`
the front end is meant to produce for it, and a proof that the two agree **on every
input** — not merely on the inputs a `#eval` tries.

A structural recursion becomes one `Term.fix` whose measure is a measure of the recursion
subject: `n` when the subject is a `Nat`, and `Term.structMeasure` — the size of the
value's runtime tree — when it is a datatype.  Nothing is added to it, because nothing
counts iterations: the evaluator recomputes the measure at every self call and recurses
only on a strict decrease.

The faithfulness proofs all go through `Term.fix_implements_measure`: supply the Lean
function, the measure, the fact that the measure term computes it, and the one-step
argument that the body is right given a self-reference that is right at smaller
measure.
-/

namespace LakeJs.Expr.Examples

open LakeJs
open LakeJs.Ty
open LakeJs.Expr.Ops

variable {Sg : Sig}

/-! ## 1. `sumTo`: a non-tail structural recursion on `Nat`

```lean
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n
```

The recursive call sits under an addition, so this is not a tail recursion: `Term.fix`
allows a self call in any position. -/

/-- The Lean function the term is meant to implement. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- The measure: the argument itself. -/
def sumToMeasure : Term Sg [Ty.nat] [] Ty.nat := ♯0

/-- The body: `if n = 0 then 0 else n + self(n - 1)`. -/
def sumToBody : Term Sg [Ty.nat] [⟨[Ty.nat], Ty.nat⟩] Ty.nat :=
  .ite (natEq (♯0) (Term.natL 0))
    (Term.natL 0)
    (natAdd (♯0) (.selfCall .head (.cons (natSub (♯0) (Term.natL 1)) .nil)))

/-- `fix (n) { … }`, ranked by `n + 1`. -/
def sumToTerm : Term Sg [] [] (.nat ⇒ .nat) :=
  .fix [Ty.nat]  1 (Term.measure1 sumToMeasure) sumToBody (Term.natL 0)

/-- The Lean function, as a function of an argument environment. -/
def sumToFun (as : Env [Ty.nat]) : Ty.nat.den := sumTo (as.get .head)

/-- **Faithfulness**: the term is `sumTo`, at every argument. -/
theorem sumToTerm_implements (δ : GEnv Sg.decls) :
    (sumToTerm (Sg := Sg)).Implements δ sumToFun := by
  intro args
  refine Term.fix_implements_measure sumToMeasure sumToBody (Term.natL 0) δ .nil .nil
    sumToFun (fun as => as.get .head) (fun as => ?_) (fun g as hg => ?_) args
  · cases args with
    | cons _ _ => cases as with | cons _ _ => rfl
  · match as with
    | .cons n .nil =>
      cases (n : Nat) with
      | zero => rfl
      | succ k =>
        show (k + 1) + g (.cons (k : Nat) .nil) = sumTo (k + 1)
        rw [hg (.cons (k : Nat) .nil) (by exact Nat.lt_succ_self k)]
        rfl

example : Term.runNat1 sumToTerm 0 = 0 := rfl
example : Term.runNat1 sumToTerm 5 = 15 := rfl
example : Term.runNat1 sumToTerm 10 = sumTo 10 := rfl

/-! ## 2. A mutual pair, merged into one `fix` with a tag

```lean
mutual
def testEven : Nat → Bool | 0 => true  | n + 1 => testOdd n
def testOdd  : Nat → Bool | 0 => false | n + 1 => testEven n
end
```

(`SnapshotsPBOPure/CaptureDerefRegression01.lean`.)  Two Lean functions that call each
other are **one** `Term.fix` whose first parameter is a tag saying which member of the
clique is running; the two Lean names become thin wrappers that supply the tag.  A jump
from one member to the other is a self call with the tag flipped, and the single rank is
shared. -/

mutual
/-- Is `n` even? -/
def testEven : Nat → Bool
  | 0 => true
  | n + 1 => testOdd n
/-- Is `n` odd? -/
def testOdd : Nat → Bool
  | 0 => false
  | n + 1 => testEven n
end

/-- The body of the merged clique, in the context `tag :: n :: []`. -/
def parityBody : Term Sg [Ty.nat, Ty.nat] [⟨[Ty.nat, Ty.nat], Ty.bool⟩] Ty.bool :=
  .ite (natEq (♯1) (Term.natL 0))
    (.ite (natEq (♯0) (Term.natL 0)) (Term.boolL true) (Term.boolL false))
    (.selfCall .head
      (.cons (natSub (Term.natL 1) (♯0))
        (.cons (natSub (♯1) (Term.natL 1)) .nil)))

/-- The merged clique, ranked by `n + 1`. -/
def parityMerged : Term Sg [] [] (.nat ⇒ .nat ⇒ .bool) :=
  .fix [Ty.nat, Ty.nat]  1 (Term.measure1 (♯1)) parityBody (Term.boolL false)

/-- The Lean functions of the clique, selected by the tag. -/
def parityFun (as : Env [Ty.nat, Ty.nat]) : Ty.bool.den :=
  if as.get .head = 0 then testEven (as.get (.tail .head))
  else testOdd (as.get (.tail .head))

/-- **Faithfulness of the whole clique**: at tag `0` the merged recursion is `testEven`,
    at any other tag it is `testOdd`, at every argument. -/
theorem parityMerged_implements (δ : GEnv Sg.decls) :
    (parityMerged (Sg := Sg)).Implements δ parityFun := by
  intro args
  refine Term.fix_implements_measure (♯1) parityBody (Term.boolL false) δ .nil .nil
    parityFun (fun as => as.get (.tail .head)) (fun as => ?_) (fun g as hg => ?_) args
  · match as with
    | .cons _ (.cons _ .nil) => rfl
  · match as with
    | .cons tag (.cons n .nil) =>
      cases (n : Nat) with
      | zero =>
        by_cases ht : (tag : Nat) = 0
        · subst ht; rfl
        · show (if cond (decide ((tag : Nat) = 0)) true false then true else false)
              = parityFun (.cons tag (.cons (0 : Nat) .nil))
          simp [parityFun, Env.get, ht, testOdd]
      | succ k =>
        show g (.cons (1 - tag : Nat) (.cons (k : Nat) .nil))
            = parityFun (.cons tag (.cons (k + 1 : Nat) .nil))
        rw [hg (.cons (1 - tag : Nat) (.cons (k : Nat) .nil))
          (by exact Nat.lt_succ_self k)]
        by_cases ht : (tag : Nat) = 0
        · simp [parityFun, Env.get, ht, testEven]
        · have h1 : (1 : Nat) - (tag : Nat) = 0 :=
            Nat.sub_eq_zero_of_le (Nat.one_le_iff_ne_zero.mpr ht)
          simp [parityFun, Env.get, ht, h1, testOdd]

/-! ### The clique as a module

The packed recursion is one declaration and the two Lean names are wrappers over it, so
a caller reaches `testEven` and `testOdd` by name and **cannot choose a rank**. -/

/-- The type of the packed recursion. -/
abbrev parityTy : Ty := .nat ⇒ .nat ⇒ .bool

/-- The private declaration holding the merged clique. -/
def declParity : GlobalDecl := ⟨"parityMerged", parityTy⟩
/-- The public declaration `testEven`. -/
def declEven : GlobalDecl := ⟨"testEven", .nat ⇒ .bool⟩
/-- The public declaration `testOdd`. -/
def declOdd : GlobalDecl := ⟨"testOdd", .nat ⇒ .bool⟩

/-- The signature of the parity module. -/
def paritySig : Sig := ⟨[declOdd, declEven, declParity], by decide⟩

/-- `testEven`, as a wrapper that supplies tag `0`. -/
def testEvenWrapper : Term ⟨[declParity], by decide⟩ [] [] (.nat ⇒ .bool) :=
  ƛ ((Term.global .here) ⬝ Term.natL 0 ⬝ (♯0))

/-- `testOdd`, as a wrapper that supplies tag `1`. -/
def testOddWrapper : Term ⟨[declEven, declParity], by decide⟩ [] [] (.nat ⇒ .bool) :=
  ƛ ((Term.global (.there .here)) ⬝ Term.natL 1 ⬝ (♯0))

/-- The module: the packed recursion, then the two wrappers. -/
def parityProgram : Program paritySig.decls :=
  .cons declOdd (by decide) testOddWrapper
    (.cons declEven (by decide) testEvenWrapper
      (.cons declParity (by decide) parityMerged .nil))

/-- Run the module's `testEven`. -/
def runTestEven (n : Nat) : Bool :=
  parityProgram.run (Sg := paritySig) (τ := .nat ⇒ .bool) (.global (.there .here)) n

/-- Run the module's `testOdd`. -/
def runTestOdd (n : Nat) : Bool :=
  parityProgram.run (Sg := paritySig) (τ := .nat ⇒ .bool) (.global .here) n

example : runTestEven 0 = testEven 0 := rfl
example : runTestEven 7 = testEven 7 := rfl
example : runTestOdd 7 = testOdd 7 := rfl
example : runTestEven 10 = testEven 10 := rfl
example : runTestOdd 11 = testOdd 11 := rfl

/-! ## 3. A structural recursion over data: summing a list

```lean
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs
```

A cons list is the built-in recursive sum: tag `0` is `[]`, tag `1` is `x :: xs` with the
head and the tail as its fields, which the alternative **binds**.  The rank is
`Term.structRank`, the size of the argument's runtime tree plus one — and the size of a
tail really is smaller than the size of the list, which is what makes the measure work. -/

/-- The Lean function. -/
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- The list type of the example. -/
abbrev natList : Ty := .list Ty.nat

/-- `case xs of | [] => 0 | x :: t => x + self t`, with the two fields bound. -/
def sumListBody : Term Sg [natList] [⟨[natList], Ty.nat⟩] Ty.nat :=
  .caseTag (♯0)
    (.cons 0 [] (by rfl) (Term.natL 0)
      (.cons 1 [Ty.nat, natList] (by rfl)
        (natAdd (♯0) (.selfCall .head (.cons (♯1) .nil)))
        .nilFull))
    (by rfl)

/-- `fix (xs) { … }`, ranked by the size of `xs`'s runtime tree. -/
def sumListTerm : Term Sg [] [] (natList ⇒ .nat) :=
  .fix [natList]  1 (Term.structMeasure (♯0)) sumListBody (Term.natL 0)

example : (show Nat from Term.run sumListTerm ([] : List Nat)) = 0 := rfl
example : (show Nat from Term.run sumListTerm ([1, 2, 3] : List Nat)) = 6 := rfl
example : (show Nat from Term.run sumListTerm ([4, 5] : List Nat)) = sumList [4, 5] := rfl

/-! ## 4. A block of join points

`Term.block` opens the tail grammar and `Tail.join` binds a join point — a label whose
body is typed in the *outer* label context, so it cannot jump back into itself.  There is
no loop construct at all, which is why a block repeats no work. -/

/-- `fun n => block { join k(x) { x + x }; if n = 0 then k(1) else k(n) }`: a shared tail
    reached from both arms of a branch. -/
def sharedTailTerm : Term Sg [] [] (.nat ⇒ .nat) :=
  ƛ (.block
    (.join [Ty.nat]
      (.ret (natAdd (♯0) (♯0)))
      (.iteT (natEq (♯0) (Term.natL 0))
        (.jmp .head (.cons (Term.natL 1) .nil))
        (.jmp .head (.cons (♯0) .nil)))))

example : Term.runNat1 sharedTailTerm 0 = 2 := rfl
example : Term.runNat1 sharedTailTerm 5 = 10 := rfl

end LakeJs.Expr.Examples

end
