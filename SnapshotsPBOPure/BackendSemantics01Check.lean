/-
The terms `SnapshotsPBOPure/BackendSemantics01Program.lean` was generated with, run
against the Lean constants they were translated from.

`test3` is the interesting one: it is a `Char` written as the `UInt32` of its code point
together with a proof that the code point is valid.  The proof is erased, and the
front end compiles `Char.mk` as the conversion the runtime provides —
`lean_uint32_to_nat` and then `lean_char_of_nat_aux` — so the term is an ordinary term of
the language rather than a wrapper the language has no counterpart for.  These checks say
that it computes the character Lean does.
-/

import SnapshotsPBOPure.BackendSemantics01Program
import SnapshotsPBOPure.BackendSemantics01

open LakeJs LakeJs.Expr ProgramSnapshotsPBOPureBackendSemantics01

namespace SnapshotsPBOPure.BackendSemantics01Check

/-- The scalar constant of the module, as the emitted program computes it. -/
theorem test1_agrees : (Program.run Program.nil tm_test1) = test1 := by native_decide

/-- The other scalar constant. -/
theorem test2_agrees : (Program.run prog_test1 tm_test2) = test2 := by native_decide

/-- The character written as its code point: the emitted term builds the very character
    Lean's `Char.mk` does. -/
theorem test3_agrees : (Program.run prog_test2 tm_test3) = test3 := by native_decide

/-- The character written with `Char.ofNat`, which the front end reads as a literal. -/
theorem test4_agrees : (Program.run prog_test3 tm_test4) = test4 := by native_decide

end SnapshotsPBOPure.BackendSemantics01Check
