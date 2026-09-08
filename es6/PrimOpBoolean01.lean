prelude
import Init.System.IO
import Init.Data.Bool

def test1 (a b : Bool) : Bool := a && b
def test2 (a b : Bool) : Bool := a || b
def test3 (a b : Bool) : Bool := a == b
def test4 (a b : Bool) : Bool := a != b
def test5 (a b : Bool) : Bool := decide (a < b)
def test6 (a b : Bool) : Bool := decide (a > b)
def test7 (a b : Bool) : Bool := decide (a <= b)
def test8 (a b : Bool) : Bool := decide (a >= b)
def test9 (a : Bool) : Bool := !a

def main : IO Unit := do
  IO.println (test1 true false)
  IO.println (test2 true false)
  IO.println (test3 true true)
  IO.println (test4 true true)
  IO.println (test5 false true)
  IO.println (test6 true false)
  IO.println (test7 true true)
  IO.println (test8 true true)
  IO.println (test9 true)
