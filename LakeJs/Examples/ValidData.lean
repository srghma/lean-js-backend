module

public import LakeJs.Examples.Ops
public import LakeJs.Program

@[expose] public section

set_option autoImplicit false

/-!
# A worked example with *data*: a clique whose measure is a call to another declaration

`TERM_VALID_DATA_WALKTHROUGH.md` §7.2 adds a plan item the numeric examples cannot show:

> **The measure is subject to the whitelist.**  A measure may be a call to a compiled
> declaration.  That declaration must itself pass the classifier and become a terminating
> `Term`.

This file is that shape, in miniature.  A module of four declarations:

| # | declaration | what it is |
| :-- | :-- | :-- |
| 0 | `Forest.len` | a structural recursion over the data, measured by `Term.structMeasure` |
| 1 | `sum._mutual` | the merged clique, **measured by a call to `Forest.len`** |
| 2 | `sumEven` | a public wrapper, tag `0` |
| 3 | `sumOdd` | a public wrapper, tag `1` |

Because a module is a telescope (`Program`), declaration 1 can mention only declaration 0,
so the measure cannot be circular: the measure of a recursion is computed by a declaration
that is *already* known to terminate.  A measure is an ordinary `Term`, so nothing special
has to be said about it — it inherits totality from the grammar like everything else.

The data is `List Nat`, whose layout is the built-in recursive sum: tag `0` is `[]` with
no fields, tag `1` is `x :: xs` with the head and the tail, which the alternative binds.
-/

namespace LakeJs.Expr.Examples

open LakeJs
open LakeJs.Ty
open LakeJs.Expr.Ops

/-! ## The data -/

/-- The datatype of the module: a list of naturals. -/
abbrev forestTy : Ty := .list Ty.nat

/-! ## Declaration 0: `len`, a structural recursion over the data -/

/-- `case xs of | [] => 0 | x :: t => 1 + self t`. -/
def forestLenBody {Sg : Sig} :
    Term Sg [forestTy] [⟨[forestTy], Ty.nat⟩] Ty.nat :=
  .caseTag (♯0)
    (.cons 0 [] (by rfl) (Term.natL 0)
      (.cons 1 [Ty.nat, forestTy] (by rfl)
        (natAdd (Term.natL 1) (.selfCall .head (.cons (♯1) .nil)))
        .nilFull))
    (by rfl)

/-- `fix (xs) { … }`, measured by the size of `xs`'s runtime tree. -/
def forestLen {Sg : Sig} : Term Sg [] [] (forestTy ⇒ .nat) :=
  .fix [forestTy]  1 (Term.structMeasure (♯0)) forestLenBody (Term.natL 0)

example : (show Nat from Term.run forestLen ([] : List Nat)) = 0 := rfl
example : (show Nat from Term.run forestLen ([3, 1, 4] : List Nat)) = 3 := rfl

/-! ## Declaration 1: the merged clique, measured by a call to `len`

```lean
mutual
def sumEven : List Nat → Nat | [] => 0 | h :: t => h + sumOdd t
def sumOdd  : List Nat → Nat | [] => 0 | _ :: t => sumEven t
end
```
-/

mutual
/-- Sum the entries at even positions. -/
def sumEven : List Nat → Nat
  | [] => 0
  | h :: t => h + sumOdd t
/-- Sum the entries at odd positions. -/
def sumOdd : List Nat → Nat
  | [] => 0
  | _ :: t => sumEven t
end

/-- The declaration holding `len`. -/
def declForestLen : GlobalDecl := ⟨"Forest.len", forestTy ⇒ .nat⟩
/-- The private declaration holding the merged clique. -/
def declSumMerged : GlobalDecl := ⟨"sumEven._mutual", .nat ⇒ forestTy ⇒ .nat⟩
/-- The public declaration `sumEven`. -/
def declSumEven : GlobalDecl := ⟨"sumEven", forestTy ⇒ .nat⟩
/-- The public declaration `sumOdd`. -/
def declSumOdd : GlobalDecl := ⟨"sumOdd", forestTy ⇒ .nat⟩

/-- The signature of the module, newest declaration first. -/
def forestSig : Sig :=
  ⟨[declSumOdd, declSumEven, declSumMerged, declForestLen], by decide⟩

/-- The signature the merged clique is written against: `len` alone. -/
def lenOnlySig : Sig := ⟨[declForestLen], by decide⟩

/-- The body of the merged clique, in the context `tag :: xs :: []`: a dispatch on the tag
    and then a dispatch on the list. -/
def sumMergedBody :
    Term lenOnlySig [Ty.nat, forestTy] [⟨[Ty.nat, forestTy], Ty.nat⟩] Ty.nat :=
  .ite (natEq (♯0) (Term.natL 0))
    -- tag 0: `sumEven xs`
    (.caseTag (♯1)
      (.cons 0 [] (by rfl) (Term.natL 0)
        (.cons 1 [Ty.nat, forestTy] (by rfl)
          (natAdd (♯0) (.selfCall .head (.cons (Term.natL 1) (.cons (♯1) .nil))))
          .nilFull))
      (by rfl))
    -- tag 1: `sumOdd xs`
    (.caseTag (♯1)
      (.cons 0 [] (by rfl) (Term.natL 0)
        (.cons 1 [Ty.nat, forestTy] (by rfl)
          (.selfCall .head (.cons (Term.natL 0) (.cons (♯1) .nil)))
          .nilFull))
      (by rfl))

/-- The merged clique: `fix (tag, xs)`, **measured by `len xs`** — a call of declaration
    0, which is why a measure has to pass the classifier too. -/
def sumMerged : Term lenOnlySig [] [] (.nat ⇒ forestTy ⇒ .nat) :=
  .fix [Ty.nat, forestTy]
     1 (Term.measure1 ((Term.global .here) ⬝ (♯1)))
    sumMergedBody (Term.natL 0)

/-! ## Declarations 2 and 3: the public wrappers -/

/-- `sumEven`, as a wrapper that supplies tag `0`. -/
def sumEvenTerm :
    Term ⟨[declSumMerged, declForestLen], by decide⟩ [] [] (forestTy ⇒ .nat) :=
  ƛ ((Term.global .here) ⬝ Term.natL 0 ⬝ (♯0))

/-- `sumOdd`, as a wrapper that supplies tag `1`. -/
def sumOddTerm :
    Term ⟨[declSumEven, declSumMerged, declForestLen], by decide⟩ [] []
      (forestTy ⇒ .nat) :=
  ƛ ((Term.global (.there .here)) ⬝ Term.natL 1 ⬝ (♯0))

/-- The module: `len`, the packed recursion, then the two wrappers. -/
def forestProgram : Program forestSig.decls :=
  .cons declSumOdd (by decide) sumOddTerm
    (.cons declSumEven (by decide) sumEvenTerm
      (.cons declSumMerged (by decide) sumMerged
        (.cons declForestLen (by decide) forestLen .nil)))

/-- Run the module's `len`. -/
def runForestLen (xs : List Nat) : Nat :=
  forestProgram.run (Sg := forestSig) (τ := forestTy ⇒ .nat)
    (.global (.there (.there (.there .here)))) xs

/-- Run the module's `sumEven`. -/
def runSumEven (xs : List Nat) : Nat :=
  forestProgram.run (Sg := forestSig) (τ := forestTy ⇒ .nat) (.global (.there .here)) xs

/-- Run the module's `sumOdd`. -/
def runSumOdd (xs : List Nat) : Nat :=
  forestProgram.run (Sg := forestSig) (τ := forestTy ⇒ .nat) (.global .here) xs

example : runForestLen [] = 0 := rfl
example : runForestLen [3, 1, 4] = [3, 1, 4].length := rfl

example : runSumEven [] = sumEven [] := rfl
example : runSumEven [3, 1, 4, 1, 5] = sumEven [3, 1, 4, 1, 5] := rfl
example : runSumEven [3, 1, 4, 1, 5] = 12 := rfl
example : runSumOdd [3, 1, 4, 1, 5] = sumOdd [3, 1, 4, 1, 5] := rfl
example : runSumOdd [3, 1, 4, 1, 5] = 2 := rfl

end LakeJs.Expr.Examples

end
