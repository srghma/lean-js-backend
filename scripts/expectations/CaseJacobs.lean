import SnapshotsPBOPure.CaseJacobs
open Expr
#eval renderExpr (add zero zero)
#eval renderExpr (mul (succ zero) (add zero (succ (succ zero))))
#eval (test1 (add zero zero), test1 (mul zero (succ zero)), test1 (add (succ zero) zero))
#eval (test1 (mul (succ zero) zero), test1 (mul (add zero (succ zero)) zero), test1 (add zero (succ zero)))
#eval (test1 (add (succ zero) (succ zero)), test1 (mul (succ zero) (succ zero)), test1 zero, test1 (succ zero))
