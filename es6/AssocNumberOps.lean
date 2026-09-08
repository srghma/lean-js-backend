prelude
import Init.System.IO
import Init.Data.Float

def test1 (x : Float) : Float :=
  1.0 + (((((2.0 + x) + x) + x) + x) + 3.0) + 4.0

def test2 (x : Float) : Float :=
  1.0 + (2.0 + (x + (x + (x + (x + 3.0))))) + 4.0

def test3 (x : Float) : Float :=
  1.0 + (2.0 + (x + (x + (x + (x + 3.0))))) + 4.0 + (((((5.0 + x) + x) + x) + x) + 6.0) + 7.0

def test4 (x : Float) : Float :=
  1.0 * (((((2.0 * x) * x) * x) * x) * 3.0) * 4.0

def test5 (x : Float) : Float :=
  1.0 * (2.0 * (x * (x * (x * (x * 3.0))))) * 4.0

def test6 (x : Float) : Float :=
  1.0 * (2.0 * (x * (x * (x * (x * 3.0))))) * 4.0 * (((((5.0 * x) * x) * x) * x) * 6.0) * 7.0

def main : IO Unit := do
  IO.println (test1 2.5)
  IO.println (test2 2.5)
  IO.println (test3 2.5)
  IO.println (test4 2.5)
  IO.println (test5 2.5)
  IO.println (test6 2.5)
