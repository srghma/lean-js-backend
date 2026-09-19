module

public import LakeJs.Examples.Ops

@[expose] public section

set_option autoImplicit false

/-!
# Worked examples over sequences and strings

The corpus contains a family of well-founded recursions that walk a string or an array by
an index, with the measure `size - i`:

* `SnapshotsPBOPure/Tco05.lean`'s `span` — the inner `go` whose `i + 1` is bounded by
  `arr.size`, for which Lean infers a well-founded recursion;
* `SnapshotsMy/StringWalk.lean`'s `test4` (`i + 1` bounded by `s.length`).

They need the primitives that read a sequence, which the runtime already supplies:
`lean_array_get_size`, `lean_array_get`, `lean_array_push` and `lean_string_length` are
`Term.extern`s like any other, and `LakeJs.Examples.Ops` names the calls.

The rank of such a walk is `size - i + 1`, and it is read **once, at entry** — the
recursion does not get to recompute `arr.size - i` at every step, which is the seal the
plan asks for: the iteration count is fixed before the first iteration runs.
-/

namespace LakeJs.Expr.Examples

open LakeJs
open LakeJs.Ty
open LakeJs.Expr.Ops

variable {Sg : Sig}

/-! ## 1. `span`: walking an array by an index (`SnapshotsPBOPure/Tco05.lean`)

```lean
def span (p : Int → Bool) (arr : Array Int) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if h : i < arr.size then
      let x := arr[i]
      if p x then go (i + 1) else some i
    else none
  go 0
```

The predicate is fixed to `0 < x` here, because a `Term` names the operation it applies.
The answer is an `Option Nat`, whose layout has tag `0` for `none` and tag `1` for `some`,
so the two answers are `Term.ctor`s. -/

/-- The Lean function: the first index whose element is not positive. -/
def spanGo (arr : List Int) (i : Nat) : Option Nat :=
  if h : i < arr.length then
    if 0 < arr.getD i 0 then spanGo arr (i + 1) else some i
  else
    none
termination_by arr.length - i
decreasing_by exact Nat.sub_succ_lt_self _ _ h

/-- The answer type of the walk. -/
abbrev optNatTy : Ty := .option Ty.nat

/-- `if i < size arr then (if 0 < arr[i] then self(arr, i + 1) else some i) else none`. -/
def spanBody :
    Term Sg [.array Ty.int, Ty.nat] [⟨[.array Ty.int, Ty.nat], optNatTy⟩] optNatTy :=
  .ite (natLt (♯1) (arrLen (♯0)))
    (.ite (intLt (Term.intL 0) (arrGet (♯0) (♯1)))
      (.selfCall .head
        (.cons (♯0) (.cons (natAdd (♯1) (Term.natL 1)) .nil)))
      (.ctor 1 [Ty.nat] (by rfl) (.cons (♯1) .nil)))
    (.ctor 0 [] (by rfl) .nil)

/-- `fix (arr, i) { … }`, ranked by `size arr - i + 1` — the `termination_by` measure,
    transcribed, plus one. -/
def spanTerm : Term Sg [] [] (.array Ty.int ⇒ .nat ⇒ optNatTy) :=
  .fix [.array Ty.int, Ty.nat]
     1 (Term.measure1 (natSub (arrLen (♯0)) (♯1)))
    spanBody (.ctor 0 [] (by rfl) .nil)

/-- `Option Nat` as a runtime tree. -/
def optNatToData : Option Nat → Data
  | none => Ty.buildVal optNatTy 0 []
  | some n => Ty.buildVal optNatTy 1 [Ty.toData Ty.nat n]

/-- Run the term. -/
def spanRun (arr : List Int) (i : Nat) : Data := Term.run spanTerm arr i

example : spanRun [1, 2, 0, 4] 0 = optNatToData (some 2) := rfl
example : spanRun [1, 2, 3] 0 = optNatToData none := rfl
example : spanRun [] 0 = optNatToData none := rfl
example : spanRun [1, 2, 0, 4] 3 = optNatToData none := rfl

/-! ## 2. `StringWalk.test4`: walking a string by an index

```lean
def test4 (s : String) : Nat :=
  let rec go (i : Nat) (acc : Nat) : Nat :=
    if i < s.length then go (i + 1) (acc + i) else acc
  go 0 0
```

Lean infers the well-founded recursion with the measure `s.length - i`; the rank is that
measure plus one. -/

/-- The Lean function. -/
def walkGo (s : String) (i acc : Nat) : Nat :=
  if _h : i < s.length then walkGo s (i + 1) (acc + i) else acc
termination_by s.length - i
decreasing_by exact Nat.sub_succ_lt_self _ _ _h

/-- `if i < length s then self(s, i + 1, acc + i) else acc`. -/
def walkBody :
    Term Sg [Ty.string, Ty.nat, Ty.nat] [⟨[Ty.string, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  .ite (natLt (♯1) (strLength (♯0)))
    (.selfCall .head
      (.cons (♯0)
        (.cons (natAdd (♯1) (Term.natL 1))
          (.cons (natAdd (♯2) (♯1)) .nil))))
    (♯2)

/-- `fix (s, i, acc) { … }`, ranked by `length s - i + 1`. -/
def walkTerm : Term Sg [] [] (.string ⇒ .nat ⇒ .nat ⇒ .nat) :=
  .fix [Ty.string, Ty.nat, Ty.nat]
     1 (Term.measure1 (natSub (strLength (♯0)) (♯1)))
    walkBody (Term.natL 0)

/-- The Lean function, as a function of an argument environment. -/
def walkFun (as : Env [Ty.string, Ty.nat, Ty.nat]) : Ty.nat.den :=
  walkGo (as.get .head) (as.get (.tail .head)) (as.get (.tail (.tail .head)))

/-- **Faithfulness**: the term is `walkGo`, at every string, index and accumulator. -/
theorem walkTerm_implements (δ : GEnv Sg.decls) :
    (walkTerm (Sg := Sg)).Implements δ walkFun := by
  intro args
  refine Term.fix_implements_measure (natSub (strLength (♯0)) (♯1)) walkBody
    (Term.natL 0) δ .nil .nil walkFun
    (fun as => String.length (as.get .head) - as.get (.tail .head))
    (fun as => ?_) (fun g as hg => ?_) args
  · match as with
    | .cons _ (.cons _ (.cons _ .nil)) => rfl
  · match as with
    | .cons s (.cons i (.cons acc .nil)) =>
      show (if cond (decide ((i : Nat) < String.length s)) true false then
              g (.cons s (.cons ((i : Nat) + 1) (.cons ((acc : Nat) + i) .nil)))
            else (acc : Nat))
          = walkFun (.cons s (.cons i (.cons acc .nil)))
      by_cases hi : (i : Nat) < String.length s
      · have hlt : String.length s - ((i : Nat) + 1) < String.length s - i :=
          Nat.sub_succ_lt_self _ _ hi
        rw [if_pos (by simp [hi]),
          hg (.cons s (.cons ((i : Nat) + 1) (.cons ((acc : Nat) + i) .nil)))
            (by simpa [Env.get] using hlt)]
        show walkGo s ((i : Nat) + 1) ((acc : Nat) + i) = walkGo s i acc
        conv => rhs; rw [walkGo]
        rw [dif_pos hi]
      · rw [if_neg (by simp [hi])]
        show (acc : Nat) = walkGo s i acc
        conv => rhs; rw [walkGo]
        rw [dif_neg hi]

/-- Run the term. -/
def walkRun (s : String) (i acc : Nat) : Nat := Term.run walkTerm s i acc

example : walkRun "abcd" 0 0 = 6 := rfl
example : walkRun "" 0 0 = 0 := rfl
example : walkRun "ab" 0 0 = 1 := rfl

/-! ## 3. Building a sequence: a walk whose accumulator is an array

A walk that *builds* an array rather than folding it into a scalar.  The accumulator is a
parameter of sequence type, and the rank is still read off the input only — which is why
the accumulator growing is no threat to termination. -/

/-- The Lean function: double every element, by an index walk. -/
def doubleGo (xs : List Int) (i : Nat) (acc : List Int) : List Int :=
  if _h : i < xs.length then doubleGo xs (i + 1) (acc ++ [2 * xs.getD i 0]) else acc
termination_by xs.length - i
decreasing_by exact Nat.sub_succ_lt_self _ _ _h

/-- `if i < size xs then self(xs, i + 1, push acc (2 * xs[i])) else acc`. -/
def doubleBody :
    Term Sg [.array Ty.int, Ty.nat, .array Ty.int]
      [⟨[.array Ty.int, Ty.nat, .array Ty.int], .array Ty.int⟩] (.array Ty.int) :=
  .ite (natLt (♯1) (arrLen (♯0)))
    (.selfCall .head
      (.cons (♯0)
        (.cons (natAdd (♯1) (Term.natL 1))
          (.cons (arrPush (♯2) (intMul (Term.intL 2) (arrGet (♯0) (♯1)))) .nil))))
    (♯2)

/-- `fix (xs, i, acc) { … }`, ranked by `size xs - i + 1`.  The exhausted branch answers
    with the accumulator, which is the answer the walk would have given anyway. -/
def doubleTerm : Term Sg [] [] (.array Ty.int ⇒ .nat ⇒ .array Ty.int ⇒ .array Ty.int) :=
  .fix [.array Ty.int, Ty.nat, .array Ty.int]
     1 (Term.measure1 (natSub (arrLen (♯0)) (♯1)))
    doubleBody (♯2)

/-- Run the term on an array, from index `0` and the empty accumulator. -/
def doubleRun (xs : List Int) : List Int := Term.run doubleTerm xs 0 []

example : doubleRun [1, 2, 3] = [2, 4, 6] := rfl
example : doubleRun [] = [] := rfl
example : doubleRun [-1, 5] = [-2, 10] := rfl

end LakeJs.Expr.Examples

end
