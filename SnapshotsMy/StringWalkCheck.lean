/-
The terms `SnapshotsMy/StringWalkProgram.lean` was generated with, run against the Lean
functions of `SnapshotsMy/StringWalk.lean` they were translated from.

A `String.Pos.Raw` is a one-field structure over `Nat`, so the type language holds a
position as the byte index it is, and `test2` — which answers with a position — answers
with that index here.  The four walks are ranked by the measures their `termination_by`
clauses give (`s.utf8ByteSize - p.byteIdx`, the one Lean inferred for `test4.go`, and —
for the `for` loop of `test3` — the one Lean inferred for the range loop the compiler
specialized); what these checks add is that those ranks are *enough*, so no walk is cut
short, and that each term computes the same function as the Lean declaration it came
from.
-/

import SnapshotsMy.StringWalkProgram
import SnapshotsMy.StringWalk

open LakeJs LakeJs.Expr ProgramSnapshotsMyStringWalk

namespace SnapshotsMy.StringWalkCheck

/-- The declarations the range loop of `test3` is written against, as a program. -/
def pRangeLoop :
    Program sig__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0.decls :=
  .cons d_test4_go (by decide) tm_test4_go .nil

/-- The declarations `String.Pos.Raw.atEnd` is written against, as a program. -/
def pAtEnd : Program sig_String_Pos_Raw_atEnd.decls :=
  .cons d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0
    (by decide)
    tm__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0
    pRangeLoop

/-- The declarations `String.Pos.Raw.next` is written against, as a program. -/
def pNext : Program sig_String_Pos_Raw_next.decls :=
  .cons d_String_Pos_Raw_atEnd (by decide) tm_String_Pos_Raw_atEnd pAtEnd

/-- The declarations `instDecidableEqChar` is written against, as a program. -/
def pCharEq : Program sig_instDecidableEqChar.decls :=
  .cons d_String_Pos_Raw_next (by decide) tm_String_Pos_Raw_next pNext

/-- The declarations `test3` is written against, as a program. -/
def pTest3 : Program sig_test3.decls :=
  .cons d_instDecidableEqChar (by decide) tm_instDecidableEqChar pCharEq

/-- The declarations `test4` is written against, as a program. -/
def pTest4 : Program sig_test4.decls := .cons d_test3 (by decide) tm_test3 pTest3

/-- The declarations `test1.go` is written against, as a program. -/
def pTest1Go : Program sig_test1_go.decls := .cons d_test4 (by decide) tm_test4 pTest4

/-- The declarations `test2.go` is written against, as a program. -/
def pTest2Go : Program sig_test2_go.decls :=
  .cons d_test1_go (by decide) tm_test1_go pTest1Go

/-- The declarations `test1` is written against, as a program. -/
def pTest1 : Program sig_test1.decls := .cons d_test2_go (by decide) tm_test2_go pTest2Go

/-- The declarations `test2` is written against, as a program. -/
def pTest2 : Program sig_test2.decls := .cons d_test1 (by decide) tm_test1 pTest1

/-- `test1`, as the emitted term computes it. -/
def runTest1 (s : String) (c : Char) : Nat := Program.run pTest1 tm_test1 s c

/-- `test2`, as the emitted term computes it: the byte index of the position. -/
def runTest2 (s : String) (c : Char) : Nat := Program.run pTest2 tm_test2 s c

/-- `test3`, as the emitted term computes it. -/
def runTest3 (s : String) (n : Nat) : Nat := Program.run pTest3 tm_test3 s n

/-- `test4`, as the emitted term computes it. -/
def runTest4 (s : String) : Nat := Program.run pTest4 tm_test4 s

/-- The strings the checks run on: ASCII, and multi-byte characters, so that a walk that
    stepped by one byte per character would be caught. -/
def samples : List String :=
  ["", "a", "abc", "banana", "aaaa", "λ", "aλb", "ζωή", "a𝔸a", "héllo wörld"]

/-- The characters the checks run on. -/
def probes : List Char := ['a', 'b', 'λ', '𝔸', ' ']

/-- The emitted term for `test1` counts the occurrences of a character, as `test1` does. -/
theorem test1_agrees :
    (samples.all fun s => probes.all fun c => runTest1 s c == test1 s c) = true := by
  native_decide

/-- The emitted term for `test2` finds the same position as `test2`. -/
theorem test2_agrees :
    (samples.all fun s => probes.all fun c =>
      runTest2 s c == (test2 s c).byteIdx) = true := by native_decide

/-- The emitted term for `test3` runs the `for` loop the same number of times, and sums
    the same byte sizes, as `test3` does. -/
theorem test3_agrees :
    (samples.all fun s => ([0, 1, 2, 5].all fun n => runTest3 s n == test3 s n)) = true := by
  native_decide

/-- The emitted term for `test4` sums the indices of the string, as `test4` does. -/
theorem test4_agrees : (samples.all fun s => runTest4 s == test4 s) = true := by
  native_decide

end SnapshotsMy.StringWalkCheck
