import SnapshotsPBOPure.Tco01Descends
import SnapshotsPBOPure.Tco01

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops ProgramSnapshotsPBOPureTco01
open DescendsSnapshotsPBOPureTco01

set_option maxHeartbeats 2000000

namespace FaithfulSnapshotsPBOPureTco01

def fun_test : Env [Ty.nat] → Ty.nat.den := fun as => _root_.test (as.get .head)

theorem bd_test_equation (δ : GEnv sig_test.decls) :
    ∀ as : Env [Ty.nat],
      bd_test.eval δ (as.append .nil) (.cons fun_test .nil) = fun_test as
  | .cons _ .nil => by faithful_eq fun_test _root_.test

theorem tm_test_implements (δ : GEnv sig_test.decls) : tm_test.Implements δ fun_test :=
  Term.fix_implements_of_equation _ bd_test _ δ fun_test
    (tm_test_descends δ) (bd_test_equation δ)

theorem run_test_eq (n : Nat) : Program.run Program.nil tm_test n = _root_.test n :=
  tm_test_implements Program.nil.env (.cons n .nil)

end FaithfulSnapshotsPBOPureTco01
