prelude
import Init.System.IO
import Init.Data.Int.Basic

structure FloatLetResult where
  b : Int
  c1 : Int
  c2 : Int
deriving Repr

def test (f : Int → Int) : FloatLetResult :=
  let b := f 1
  let c := f 2
  { b, c1 := c, c2 := c }

def main : IO Unit := do
  IO.println (repr (test (fun x => x + 10)))
