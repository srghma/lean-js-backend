prelude
import Init.System.IO
import Init.Data.Char.Basic

def test1 (a b : Char) : Bool := a == b
def test2 (a b : Char) : Bool := a != b
def test3 (a b : Char) : Bool := decide (a < b)
def test4 (a b : Char) : Bool := decide (a > b)
def test5 (a b : Char) : Bool := decide (a <= b)
def test6 (a b : Char) : Bool := decide (a >= b)


def main : IO Unit := do
  IO.println (test1 'a' 'b')
  IO.println (test2 'a' 'b')
  IO.println (test3 'a' 'b')
  IO.println (test4 'a' 'b')
  IO.println (test5 'a' 'b')
  IO.println (test6 'a' 'b')
