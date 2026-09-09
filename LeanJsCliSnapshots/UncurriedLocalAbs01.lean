prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.Array.Basic

def test (x y : Int) : Int :=
  let fn a b := 
    #[ x, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b ].foldl (fun s i => s + i) 0
  fn x y + fn y x

def main : IO Unit := do
  IO.println (test 1 2)
