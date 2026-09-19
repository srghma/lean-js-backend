/-
The terms `SnapshotsPBOPure/CaseJacobsProgram.lean` was generated with, run against the
Lean functions of `SnapshotsPBOPure/CaseJacobs.lean` they were translated from.

`renderExpr` is structurally recursive on an `Expr`, so its rank is the structural size of
the tree it is handed.  `Term` has no fuel argument, so running one of these terms is an
ordinary total Lean computation; what these checks add is that the rank is enough — the
recursion is not cut short — and that the terms compute the same functions as the
declarations they came from.
-/

import SnapshotsPBOPure.CaseJacobsProgram
import SnapshotsPBOPure.CaseJacobs

open LakeJs LakeJs.Expr ProgramSnapshotsPBOPureCaseJacobs

namespace SnapshotsPBOPure.CaseJacobsCheck

/-- The declarations `Expr.ctorIdx` is written against, as a program. -/
def pCtorIdx : Program sig_Expr_ctorIdx.decls :=
  .cons d_renderExpr (by decide) tm_renderExpr .nil

/-- The declarations `instToStringExpr` is written against, as a program. -/
def pToString : Program sig_instToStringExpr.decls :=
  .cons d_Expr_ctorIdx (by decide) tm_Expr_ctorIdx pCtorIdx

/-- The declarations `test1` is written against, as a program. -/
def pTest1 : Program sig_test1.decls :=
  .cons d_instToStringExpr (by decide) tm_instToStringExpr pToString

/-- An `Expr`, as the runtime tree the emitted terms run on: the constructors in
    declaration order are `add`, `mul`, `succ` and `zero`. -/
def toData : _root_.Expr → Data
  | .add a b => .node 0 [toData a, toData b]
  | .mul a b => .node 1 [toData a, toData b]
  | .succ a => .node 2 [toData a]
  | .zero => .node 3 []

/-- `renderExpr`, as the emitted term computes it. -/
def runRender (e : _root_.Expr) : String := Term.run tm_renderExpr (toData e)

/-- `test1`, as the emitted term computes it. -/
def runTest1 (e : _root_.Expr) : String := Program.run pTest1 tm_test1 (toData e)

/-- The trees the checks run on: every branch of `test1` is taken by one of them, and the
    deep ones would show a rank that was not enough. -/
def samples : List _root_.Expr :=
  let z : _root_.Expr := .zero
  let s : _root_.Expr := .succ z
  let ss : _root_.Expr := .succ s
  let a : _root_.Expr := .add s ss
  let m : _root_.Expr := .mul a z
  [ z, s, ss, .add z z, .mul z s, .add s z, a, m, .mul z m, .add (.succ a) m
  , .mul (.add a m) (.succ (.mul m a)), .add (.mul m (.add a ss)) (.succ (.succ m)) ]

/-- The emitted term and `renderExpr` agree on every tree above. -/
theorem renderExpr_agrees :
    (samples.all fun e => runRender e == renderExpr e) = true := by native_decide

/-- The emitted term and `test1` agree on every tree above. -/
theorem test1_agrees : (samples.all fun e => runTest1 e == test1 e) = true := by
  native_decide

end SnapshotsPBOPure.CaseJacobsCheck
