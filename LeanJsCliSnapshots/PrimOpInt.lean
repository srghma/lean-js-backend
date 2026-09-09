prelude
import Init.System.IO
import Init.Data.Int
import Init.Data.Bool

def test1 (a b : Int) : Int := a + b
def test2 (a b : Int) : Int := a - b
def test3 (a b : Int) : Bool := a == b
def test4 (a b : Int) : Bool := a != b
def test5 (a b : Int) : Bool := decide (a < b)
def test6 (a b : Int) : Bool := decide (a > b)
def test7 (a b : Int) : Bool := decide (a <= b)
def test8 (a b : Int) : Bool := decide (a >= b)
def test9 (a b : Int) : Int := a * b
def test10 (a b : Int) : Int := a / b
def test11 (a : Int) : Int := -a


def main : IO Unit := do
  IO.println (test1 10 20)
  IO.println (test2 10 20)
  IO.println (test3 10 20)
  IO.println (test4 10 20)
  IO.println (test5 10 20)
  IO.println (test6 10 20)
  IO.println (test7 10 20)
  IO.println (test8 10 20)
  IO.println (test9 10 20)
  IO.println (test10 10 20)
  IO.println (test11 10)
