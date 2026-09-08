prelude
import Init.System.IO
import Init.Data.String

inductive Expr where
  | add (a : Expr) (b : Expr)
  | mul (a : Expr) (b : Expr)
  | succ (a : Expr)
  | zero

def renderExpr : Expr → String
  | .add a b => "Add(" ++ renderExpr a ++ " " ++ renderExpr b ++ ")"
  | .mul a b => "Mul(" ++ renderExpr a ++ " " ++ renderExpr b ++ ")"
  | .succ a => "Succ(" ++ renderExpr a ++ ")"
  | .zero => "Zero"

def test1 : Expr → String
  | .add .zero .zero => "e1"
  | .mul .zero x => "e2: " ++ renderExpr x
  | .add (.succ x) y => "e3: " ++ renderExpr x ++ " " ++ renderExpr y
  | .mul x .zero => "e4: " ++ renderExpr x
  | .mul (.add x y) z => "e5: " ++ renderExpr x ++ " " ++ renderExpr y ++ " " ++ renderExpr z
  | .add x .zero => "e6: " ++ renderExpr x
  | x => "e7: " ++ renderExpr x

def main : IO Unit := do
  IO.println (test1 (.add .zero .zero))
  IO.println (test1 (.mul (.add .zero (.succ .zero)) (.succ .zero)))
