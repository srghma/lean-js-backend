prelude
import Init.System.IO
import Init.Data.Float

def test1 (a b : Float) : Float := a + b
def test2 (a b : Float) : Float := a - b
def test3 (a b : Float) : Bool := a == b
def test4 (a b : Float) : Bool := a != b
def test5 (a b : Float) : Bool := decide (a < b)
def test6 (a b : Float) : Bool := decide (a > b)
def test7 (a b : Float) : Bool := decide (a <= b)
def test8 (a b : Float) : Bool := decide (a >= b)
def test9 (a b : Float) : Float := a * b
def test10 (a b : Float) : Float := a / b
def test11 (a : Float) : Float := -a
def test12 (a b c : Float) : Float := a - (b - c)
def test13 (a b c : Float) : Float := a / (b / c)

def main : IO Unit := do
  IO.println (toString (test1 1.0 2.0))
  IO.println (toString (test2 1.0 2.0))
  IO.println (test3 1.0 1.0)
  IO.println (test4 1.0 1.0)
  IO.println (test5 1.0 2.0)
  IO.println (test6 1.0 2.0)
  IO.println (test7 1.0 1.0)
  IO.println (test8 1.0 1.0)
  IO.println (toString (test9 2.0 3.0))
  IO.println (toString (test10 10.0 3.0))
  IO.println (toString (test11 5.0))
  IO.println (toString (test12 1.0 2.0 3.0))
  IO.println (toString (test13 1.0 2.0 3.0))
