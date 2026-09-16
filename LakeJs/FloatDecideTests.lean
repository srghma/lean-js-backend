/-
Tests for the `float_decide` guard: it succeeds on floating point goals and refuses
everything else.
-/
import RequestProject.FloatDecide
import RequestProject.JSFloat.Basic
import RequestProject.JSFloat32.Basic
import RequestProject.JsFloatArray
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace FloatDecide.Tests

/-! ### Accepted: genuine statements about the models -/

example : (1.0 : JSFloat).toBits = 0x3FF0000000000000 := by float_decide
example : (0.1 : JSFloat32).toBits = 0x3DCCCCCD := by float_decide
example : (JsFloatArray.empty.push 1.0).size = 1 := by float_decide

/-! ### Rejected: no floating point content at all -/

example : (2 : Nat) + 2 = 4 := by
  fail_if_success float_decide
  decide

example : (List.range 5).length = 5 := by
  fail_if_success float_decide
  decide

/-! ### Rejected: a floating point goal contaminated by outside constants -/

example : (1.0 : JSFloat).toBits = 0x3FF0000000000000 ∧ Real.pi = Real.pi := by
  fail_if_success float_decide
  exact ⟨by float_decide, rfl⟩

end FloatDecide.Tests
