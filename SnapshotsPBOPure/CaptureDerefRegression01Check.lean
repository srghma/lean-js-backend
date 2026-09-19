/-
The terms `SnapshotsPBOPure/CaptureDerefRegression01Program.lean` was generated with, run
against the Lean functions of `SnapshotsPBOPure/CaptureDerefRegression01.lean` they were
translated from.

`test2` and `test3` return a closure over the pair they were handed, and the mutual
`testEven` / `testOdd` become one ranked recursion.  `Term` has no fuel argument, so
running one of these terms is an ordinary total Lean computation; what these checks add is
that the rank is enough and that the terms compute the same functions as the declarations
they came from.  (`test4` and `test5` answer with a *record of functions*, which the
runtime tree does not store, so they are not checked by value here.)
-/

import SnapshotsPBOPure.CaptureDerefRegression01Program
import SnapshotsPBOPure.CaptureDerefRegression01

open LakeJs LakeJs.Expr ProgramSnapshotsPBOPureCaptureDerefRegression01

namespace SnapshotsPBOPure.CaptureDerefRegression01Check

/-- The declarations `test2` is written against, as a program. -/
def pTest2 : Program sig_test2.decls := .cons d_test1 (by decide) tm_test1 .nil

/-- The declarations `test3` is written against, as a program. -/
def pTest3 : Program sig_test3.decls := .cons d_test2 (by decide) tm_test2 pTest2

/-- The declarations `test4` is written against, as a program. -/
def pTest4 : Program sig_test4.decls := .cons d_test3 (by decide) tm_test3 pTest3

/-- The declarations `test5` is written against, as a program. -/
def pTest5 : Program sig_test5.decls := .cons d_test4 (by decide) tm_test4 pTest4

/-- The declarations the merged clique is written against, as a program. -/
def pClique : Program sig_testEven___testOdd__clique_.decls :=
  .cons d_test5 (by decide) tm_test5 pTest5

/-- The declarations `testEven` is written against, as a program. -/
def pTestEven : Program sig_testEven.decls :=
  .cons d_testEven___testOdd__clique_ (by decide) tm_testEven___testOdd__clique_ pClique

/-- The declarations `testOdd` is written against, as a program. -/
def pTestOdd : Program sig_testOdd.decls :=
  .cons d_testEven (by decide) tm_testEven pTestEven

/-- A pair of `Int`s, as the runtime tree holds it. -/
def pair (a b : Int) : Data := .node 0 [.leaf .int a, .leaf .int b]

/-- The two fields of a runtime pair. -/
def unpair : Data → Int × Int
  | .node _ [.leaf .int a, .leaf .int b] => (a, b)
  | _ => (0, 0)

/-- `test1`, as the emitted term computes it. -/
def runTest1 (a b c : Int) : Int := Term.run tm_test1 (pair a b) c

/-- `test2`, as the emitted term computes it. -/
def runTest2 (a b c : Int) : Int := Program.run pTest2 tm_test2 (pair a b) c

/-- `test3`, as the emitted term computes it: a `Box` is a newtype, so it is the function
    it wraps. -/
def runTest3 (a b c : Int) : Int := Program.run pTest3 tm_test3 (pair a b) c

/-- `testEven`, as the emitted term computes it. -/
def runTestEven (n : Nat) (a b : Int) : Int × Int :=
  unpair (Program.run pTestEven tm_testEven n (pair a b))

/-- `testOdd`, as the emitted term computes it. -/
def runTestOdd (n : Nat) (a b : Int) : Int × Int :=
  unpair (Program.run pTestOdd tm_testOdd n (pair a b))

/-- `testEven` and `testOdd` of the module, on the two fields of the `Box2` they carry.
    The `Box2` of the module is `private`, so it cannot be built here; this is the same
    recursion on the pair the runtime tree holds, and it is what the emitted terms are
    compared with. -/
def evenOddModel : Bool → Nat → Int × Int → Int × Int
  | _, 0, p => p
  | true, n + 1, (x, y) => evenOddModel false n (y + 1, x + 2)
  | false, n + 1, (x, y) => evenOddModel true n (y + 3, x + 4)

/-- The emitted terms and the Lean functions agree on every triple below. -/
theorem tests_agree :
    ([(0 : Int), 1, -3, 7].all fun a => [(0 : Int), 2, -5].all fun b =>
      [(0 : Int), 4, -6].all fun c =>
        runTest1 a b c == test1 (a, b) c && runTest2 a b c == test2 (a, b) c &&
          runTest3 a b c == (test3 (a, b)).1 c) = true := by native_decide

/-- The merged recursion computes the mutual recursion it came from: the rank is enough
    at every depth below, so neither member is cut short. -/
theorem mutual_agrees :
    ((List.range 12).all fun n => [(0 : Int), 3, -4].all fun a =>
      [(1 : Int), -2].all fun b =>
        runTestEven n a b == evenOddModel true n (a, b) &&
          runTestOdd n a b == evenOddModel false n (a, b)) = true := by native_decide

end SnapshotsPBOPure.CaptureDerefRegression01Check
