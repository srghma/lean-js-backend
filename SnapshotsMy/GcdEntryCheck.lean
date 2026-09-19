/-
The terms `SnapshotsMy/GcdEntryProgram.lean` was generated with, run against the Lean
functions they were translated from.

`Nat.gcd` is implemented in C (`@[extern "lean_nat_gcd"]`), so the compiled module keeps
no body for it; the front end compiles the Lean definition instead, from the model of
`LakeJs.CoreModels`, and ranks the recursion by the `termination_by` measure Lean's own
source gives it.  What these checks add is that the rank is *enough* — the recursion is
not cut short — and that the term computes the same function as `Nat.gcd`.
-/

import SnapshotsMy.GcdEntryProgram
import SnapshotsMy.GcdEntry

open LakeJs LakeJs.Expr ProgramSnapshotsMyGcdEntry

namespace SnapshotsMy.GcdEntryCheck

/-- The declarations `gcd2` is written against, as a program. -/
def pGcd2 : Program sig_gcd2.decls := .cons d_Nat_gcd (by decide) tm_Nat_gcd .nil

/-- The declarations `run` is written against, as a program. -/
def pRun : Program sig_run.decls := .cons d_gcd2 (by decide) tm_gcd2 pGcd2

/-- `Nat.gcd`, as the emitted term computes it. -/
def runGcd (m n : Nat) : Nat := Term.run tm_Nat_gcd m n

/-- `gcd2`, as the emitted term computes it. -/
def runGcd2 (m n : Nat) : Nat := Program.run pGcd2 tm_gcd2 m n

/-- The emitted term and `Nat.gcd` agree on every pair below 60. -/
theorem gcd_agrees :
    ((List.range 60).all fun m => (List.range 60).all fun n =>
      runGcd m n == Nat.gcd m n) = true := by native_decide

/-- The entry point of the module agrees with the Lean function it came from. -/
theorem gcd2_agrees :
    ((List.range 40).all fun m => (List.range 40).all fun n =>
      runGcd2 m n == gcd2 m n) = true := by native_decide

/-- The constant of the module, as the emitted program computes it. -/
theorem run_agrees : (Program.run pRun tm_run : Nat) = run := by native_decide

end SnapshotsMy.GcdEntryCheck
