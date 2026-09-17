import SnapshotsPBOPure.RecursionSchemes01
open ExprF
def lit (n : Int) : FixExpr := ⟨.Lit n⟩
def add (a b : FixExpr) : FixExpr := ⟨.Add a b⟩
def mul (a b : FixExpr) : FixExpr := ⟨.Mul a b⟩
#eval (test1 (lit 5), test1 (add (lit 2) (lit 3)), test1 (mul (add (lit 2) (lit 3)) (lit 4)))
#eval (test2 (lit 5), test2 (add (lit 2) (lit 3)), test2 (mul (add (lit 2) (lit 3)) (lit 4)))
#eval (eval (.Lit 7), eval (.Add 2 3), eval (.Mul 2 3))
#eval (match bump (.Lit 7) with | .Lit n => n | _ => -1)
