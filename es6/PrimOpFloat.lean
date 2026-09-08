prelude
import Init.System.IO
import Init.Data.Float

def test1 (a b : Float) : Float := a + b
def test2 (a b : Float) : Float := a - b
def test3 (a b : Float) : Float := a * b
def test4 (a b : Float) : Float := a / b
def test5 (a : Float) : Float := -a
def test6 (a b : Float) : Bool := decide (a < b)
def test7 (a b : Float) : Bool := decide (a <= b)


def main : IO Unit := do
  IO.println (test1 1.5 2.5)
  IO.println (test2 1.5 2.5)
  IO.println (test3 1.5 2.5)
  IO.println (test4 1.5 2.5)
  IO.println (test5 1.5)
  IO.println (test6 1.5 2.5)
  IO.println (test7 1.5 2.5)
