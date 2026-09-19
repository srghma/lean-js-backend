/-
The terms `SnapshotsPBOPure/CaseLeafTcoProgram.lean` was generated with, run against the
Lean functions of `SnapshotsPBOPure/CaseLeafTco.lean` they were translated from.

`test1Fuel` appends arrays, and Lean compiles `Array.append` into an `unsafe` loop over
`USize`; the front end compiles the Lean definition instead, from the model of
`LakeJs.CoreModels`, at the element type the call uses (`Array.append @ Int`).  `Term` has
no fuel argument — `Term.fix` carries the rank it was translated with — so running one of
these terms is an ordinary total Lean computation.  What these checks add is that the
ranks are *enough*, so no recursion is cut short, and that the terms compute the same
functions as the declarations they came from.
-/

import SnapshotsPBOPure.CaseLeafTcoProgram
import SnapshotsPBOPure.CaseLeafTco

open LakeJs LakeJs.Expr ProgramSnapshotsPBOPureCaseLeafTco

namespace SnapshotsPBOPure.CaseLeafTcoCheck

/-- The declarations `LakeJs.CoreModels.arrayAppendFrom @ Int` is written against. -/
def pAppendFrom : Program sig_LakeJs_CoreModels_arrayAppendFrom___Int.decls :=
  .cons d_Array_back____Int (by decide) tm_Array_back____Int .nil

/-- The declarations `Array.append @ Int` is written against. -/
def pAppend : Program sig_Array_append___Int.decls :=
  .cons d_LakeJs_CoreModels_arrayAppendFrom___Int (by decide)
    tm_LakeJs_CoreModels_arrayAppendFrom___Int pAppendFrom

/-- The declarations `test1Fuel` is written against. -/
def pTest1Fuel : Program sig_test1Fuel.decls :=
  .cons d_Array_append___Int (by decide) tm_Array_append___Int pAppend

/-- The declarations `test1FuelCalled` is written against. -/
def pCalled : Program sig_test1FuelCalled.decls :=
  .cons d_test1Fuel (by decide) tm_test1Fuel pTest1Fuel

/-- `Array.append`, as the emitted term computes it. -/
def runAppend (as bs : List Int) : List Int := Program.run pAppend tm_Array_append___Int as bs

/-- `Array.back?`, as the emitted term computes it: the tagged union is `none` at tag `0`
    and `some` at tag `1`. -/
def runBack? (as : List Int) : Option Int :=
  match Term.run tm_Array_back____Int as with
  | .node 1 [.leaf .int i] => some i
  | _ => none

/-- `test1Fuel`, as the emitted term computes it. -/
def runTest1Fuel (n : Nat) (b : Bool) (as : List Int) : List Int :=
  Program.run pTest1Fuel tm_test1Fuel n b as

/-- The arrays the checks run on. -/
def samples : List (List Int) :=
  [[], [1], [2], [1, 2], [0, 2], [1, 0, 2], [3, 4, 5], [1, 5, 2], [7], [1, 2, 3, 4, 5]]

/-- The model of `Array.append` the front end compiled agrees with `Array.append`. -/
theorem append_agrees :
    (samples.all fun as => samples.all fun bs =>
      runAppend as bs == (as.toArray ++ bs.toArray).toList) = true := by native_decide

/-- The compiled `Array.back?` agrees with `Array.back?`. -/
theorem back?_agrees :
    (samples.all fun as => runBack? as == as.toArray.back?) = true := by native_decide

/-- The emitted term and `test1Fuel` agree, at every fuel up to 6 and both booleans. -/
theorem test1Fuel_agrees :
    ((List.range 7).all fun n => [true, false].all fun b => samples.all fun as =>
      runTest1Fuel n b as == (test1Fuel n b as.toArray).toList) = true := by native_decide

end SnapshotsPBOPure.CaseLeafTcoCheck
