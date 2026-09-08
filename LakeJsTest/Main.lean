import Spec
import Spec.RunSpec

open Spec

def tests : Spec := do
  describe "LakeJs" do
    it "initial test" do
      Spec.Assert.assertEq "smoke test" (1 + 1) 2
  -- To be enabled once LakeJs.Js / LakeJs.Optimizer are complete:
  -- describe "OptimizeLeanArrayMk" do
  --   LakeJsTest.optimizeLeanArrayMkSpec

def main (args : List String) : IO UInt32 := do
  Spec.runSpecFromArgsAndReturnExitCode args tests
