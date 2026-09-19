/-
The terms `SnapshotsPBOPure/RecursionSchemes01Program.lean` was generated with, run
against the Lean functions of `SnapshotsPBOPure/RecursionSchemes01.lean` they were
translated from.

`cata` and `cataMap` are polymorphic and mutually recursive, and they answer with
*different* types.  The front end compiles them at the type the only caller uses
(`cata @ Int`), merges the clique into one ranked recursion whose answer is the union of
the two result types, and reads each member's summand back out of it.  `FixExpr` is a
one-field structure over `ExprF FixExpr`, so it is erased: a value of it is the `ExprF`
tree itself.

`Term` has no fuel argument — `Term.fix` carries the rank it was translated with — so
running one of these terms is an ordinary total Lean computation.  What these checks add
is that the rank is *enough*, so the recursion is not cut short, and that the terms
compute the same functions as the declarations they came from.
-/

import SnapshotsPBOPure.RecursionSchemes01Program
import SnapshotsPBOPure.RecursionSchemes01

open LakeJs LakeJs.Expr ProgramSnapshotsPBOPureRecursionSchemes01

namespace SnapshotsPBOPure.RecursionSchemes01Check

/-- The declarations `eval` is written against, as a program. -/
def pEval : Program sig_eval.decls := .cons d_bump (by decide) tm_bump .nil

/-- The declarations the merged clique is written against, as a program. -/
def pClique : Program sig_cata___Int___cataMap___Int__clique_.decls :=
  .cons d_eval (by decide) tm_eval pEval

/-- The declarations `cata @ Int` is written against, as a program. -/
def pCata : Program sig_cata___Int.decls :=
  .cons d_cata___Int___cataMap___Int__clique_ (by decide)
    tm_cata___Int___cataMap___Int__clique_ pClique

/-- The declarations `cataMap @ Int` is written against, as a program. -/
def pCataMap : Program sig_cataMap___Int.decls :=
  .cons d_cata___Int (by decide) tm_cata___Int pCata

/-- The declarations `test1` is written against, as a program. -/
def pTest1 : Program sig_test1.decls :=
  .cons d_cataMap___Int (by decide) tm_cataMap___Int pCataMap

/-- The declarations `test2` is written against, as a program. -/
def pTest2 : Program sig_test2.decls := .cons d_test1 (by decide) tm_test1 pTest1

/-- The size of a `FixExpr`, for the recursion below. -/
def fixSize : FixExpr → Nat
  | ⟨.Lit _⟩ => 1
  | ⟨.Add a b⟩ => fixSize a + fixSize b + 1
  | ⟨.Mul a b⟩ => fixSize a + fixSize b + 1

/-- A `FixExpr`, as the runtime tree the emitted terms run on: the `FixExpr` wrapper is
    erased, so a node is the constructor of its `ExprF` layer. -/
def toData : FixExpr → Data
  | ⟨.Lit n⟩ => .node 0 [.leaf .int n]
  | ⟨.Add a b⟩ => .node 1 [toData a, toData b]
  | ⟨.Mul a b⟩ => .node 2 [toData a, toData b]
termination_by e => fixSize e
decreasing_by all_goals simp [fixSize]; omega

/-- `test1`, as the emitted term computes it. -/
def runTest1 (e : FixExpr) : Int := Program.run pTest1 tm_test1 (toData e)

/-- `test2`, as the emitted term computes it: its algebra is a local function, `bump`
    followed by `eval`. -/
def runTest2 (e : FixExpr) : Int := Program.run pTest2 tm_test2 (toData e)

/-- `cata eval`, as the emitted term computes it. -/
def runCataEval (e : FixExpr) : Int :=
  Program.run pCata tm_cata___Int (Program.run pEval tm_eval) (toData e)

/-- A `Lit`. -/
def lit (n : Int) : FixExpr := ⟨.Lit n⟩

/-- The trees the checks run on: they are up to five levels deep, so a rank that was not
    enough would show. -/
def samples : List FixExpr :=
  let l1 := lit 1
  let l2 := lit 2
  let l3 := lit 3
  let a := ⟨.Add l1 l2⟩
  let m := ⟨.Mul l3 a⟩
  let deep := ⟨.Add m ⟨.Mul a ⟨.Add l3 ⟨.Mul l2 l1⟩⟩⟩⟩
  [l1, l2, a, m, ⟨.Add a m⟩, deep, ⟨.Mul deep deep⟩, ⟨.Add deep ⟨.Add deep m⟩⟩]

/-- The emitted term and `test1` agree on every tree above. -/
theorem test1_agrees : (samples.all fun e => runTest1 e == test1 e) = true := by
  native_decide

/-- `cata eval`, run through the emitted terms, is `test1` too — the merged clique and
    the entry point of each member agree with the Lean functions. -/
theorem cata_agrees : (samples.all fun e => runCataEval e == cata eval e) = true := by
  native_decide

/-- The emitted term and `test2` agree: the algebra it hands the clique is a local
    function, which the front end compiles as an abstraction. -/
theorem test2_agrees : (samples.all fun e => runTest2 e == test2 e) = true := by
  native_decide

end SnapshotsPBOPure.RecursionSchemes01Check
