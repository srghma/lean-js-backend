prelude
import Init.System.IO
import Init.Data.Int.Basic

def test1 (x : Int) : Int :=
  1 + (((((2 + x) + x) + x) + x) + 3) + 4

def test2 (x : Int) : Int :=
  1 + (2 + (x + (x + (x + (x + 3))))) + 4

def test3 (x : Int) : Int :=
  1 + (2 + (x + (x + (x + (x + 3))))) + 4 + (((((5 + x) + x) + x) + x) + 6) + 7

def test4 (x : Int) : Int :=
  1 * (((((2 * x) * x) * x) * x) * 3) * 4

def test5 (x : Int) : Int :=
  1 * (2 * (x * (x * (x * (x * 3))))) * 4

def test6 (x : Int) : Int :=
  1 * (2 * (x * (x * (x * (x * 3))))) * 4 * (((((5 * x) * x) * x) * x) * 6) * 7

def main : IO Unit := do
  IO.println (test1 2)
  IO.println (test2 2)
  IO.println (test3 2)
  IO.println (test4 2)
  IO.println (test5 2)
  IO.println (test6 2)
