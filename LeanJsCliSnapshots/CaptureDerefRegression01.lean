prelude
import Init.System.IO
import Init.Data.Int.Basic

inductive Box a where
  | mk : a → Box a

def test1 (a : Int) (_ : Int) (b : Int) : Int := a + b

def test2 (a : Int) (_ : Int) : Int → Int := fun b => a + b

def test3 (a : Int) (_ : Int) : Box (Int → Int) := .mk (fun b => a + b)

def main : IO Unit := do
  IO.println (test1 3 0 4)
  IO.println (test2 3 0 4)
  match test3 3 0 with
  | .mk f => IO.println (f 4)
