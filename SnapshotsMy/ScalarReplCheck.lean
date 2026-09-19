/-
The terms `SnapshotsMy/ScalarReplProgram.lean` was generated with, run against the Lean
functions of `SnapshotsMy/ScalarRepl.lean` they were translated from.

`test1` and `test2` are `for` loops over a `Std.Legacy.Range`, which Lean compiles by
specializing its own range loop at the body of each of them.  Such a specialization has
no declaration of its own — only a compiled body — so the rank of the loop is the measure
Lean recorded for the declaration it was specialized from, `range.stop - i`, read against
the parameters the specialization kept.  What these checks add is that the rank is
*enough*: neither loop is cut short, and each term computes the same function as the Lean
declaration it came from.
-/

import SnapshotsMy.ScalarReplProgram
import SnapshotsMy.ScalarRepl

open LakeJs LakeJs.Expr ProgramSnapshotsMyScalarRepl

namespace SnapshotsMy.ScalarReplCheck

/-- The declarations the range loop of `test1` is written against: none. -/
def pLoop1 :
    Program sig__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test1_spec_0.decls :=
  .nil

/-- The declarations `dist` is written against, as a program. -/
def pDist : Program sig__private_SnapshotsMy_ScalarRepl_0_dist.decls :=
  .cons d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test1_spec_0
    (by decide)
    tm__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test1_spec_0
    pLoop1

/-- The declarations `bigger` is written against, as a program. -/
def pBigger : Program sig__private_SnapshotsMy_ScalarRepl_0_bigger.decls :=
  .cons d__private_SnapshotsMy_ScalarRepl_0_dist (by decide)
    tm__private_SnapshotsMy_ScalarRepl_0_dist pDist

/-- The declarations `sumOpt` is written against, as a program. -/
def pSumOpt : Program sig__private_SnapshotsMy_ScalarRepl_0_sumOpt.decls :=
  .cons d__private_SnapshotsMy_ScalarRepl_0_bigger (by decide)
    tm__private_SnapshotsMy_ScalarRepl_0_bigger pBigger

/-- The declarations `clampSum` is written against, as a program. -/
def pClampSum : Program sig__private_SnapshotsMy_ScalarRepl_0_clampSum.decls :=
  .cons d__private_SnapshotsMy_ScalarRepl_0_sumOpt (by decide)
    tm__private_SnapshotsMy_ScalarRepl_0_sumOpt pSumOpt

/-- The declarations `test1` is written against, as a program. -/
def pTest1 : Program sig_test1.decls :=
  .cons d__private_SnapshotsMy_ScalarRepl_0_clampSum (by decide)
    tm__private_SnapshotsMy_ScalarRepl_0_clampSum pClampSum

/-- The declarations `test3` is written against, as a program. -/
def pTest3 : Program sig_test3.decls := .cons d_test1 (by decide) tm_test1 pTest1

/-- The declarations `test4` is written against, as a program. -/
def pTest4 : Program sig_test4.decls := .cons d_test3 (by decide) tm_test3 pTest3

/-- The declarations `test5` is written against, as a program. -/
def pTest5 : Program sig_test5.decls := .cons d_test4 (by decide) tm_test4 pTest4

/-- The declarations `test6` is written against, as a program. -/
def pTest6 : Program sig_test6.decls := .cons d_test5 (by decide) tm_test5 pTest5

/-- The declarations the range loop of `test2` is written against, as a program. -/
def pLoop2 :
    Program sig__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test2_spec_0.decls :=
  .cons d_test6 (by decide) tm_test6 pTest6

/-- The declarations `test2` is written against, as a program. -/
def pTest2 : Program sig_test2.decls :=
  .cons d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test2_spec_0
    (by decide)
    tm__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test2_spec_0
    pLoop2

/-- `test1`, as the emitted term computes it. -/
def runTest1 (n : Nat) : Nat := Program.run pTest1 tm_test1 n

/-- `test2`, as the emitted term computes it. -/
def runTest2 (n : Nat) : Nat := Program.run pTest2 tm_test2 n

/-- `test3`, as the emitted term computes it. -/
def runTest3 (a b : Nat) : Nat := Program.run pTest3 tm_test3 a b

/-- `test5`, as the emitted term computes it. -/
def runTest5 (a b : Nat) : Nat := Program.run pTest5 tm_test5 a b

/-- `test6`, as the emitted term computes it. -/
def runTest6 (n : Nat) : Nat := Program.run pTest6 tm_test6 n

/-- The numbers the checks run on. -/
def samples : List Nat := [0, 1, 2, 3, 7, 12, 25]

/-- The emitted term for `test1` sums `0` to `n - 1`, as `test1` does. -/
theorem test1_agrees : (samples.all fun n => runTest1 n == test1 n) = true := by
  native_decide

/-- The emitted term for `test2` runs the two nested range loops, as `test2` does. -/
theorem test2_agrees : (samples.all fun n => runTest2 n == test2 n) = true := by
  native_decide

/-- The emitted term for `test3` is the same function as `test3`. -/
theorem test3_agrees :
    (samples.all fun a => samples.all fun b => runTest3 a b == test3 a b) = true := by
  native_decide

/-- The emitted term for `test5` is the same function as `test5`. -/
theorem test5_agrees :
    (samples.all fun a => samples.all fun b => runTest5 a b == test5 a b) = true := by
  native_decide

/-- The emitted term for `test6` is the same function as `test6`. -/
theorem test6_agrees : (samples.all fun n => runTest6 n == test6 n) = true := by
  native_decide

end SnapshotsMy.ScalarReplCheck
