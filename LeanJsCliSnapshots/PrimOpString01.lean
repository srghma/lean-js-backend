prelude
import Init.System.IO
import Init.Data.String.Basic

def test1 (a b : String) : Bool := a == b
def test2 (a b : String) : Bool := a != b
def test3 (a b : String) : Bool := decide (a < b)
def test4 (a b : String) : Bool := decide (a > b)
def test5 (a b : String) : Bool := decide (a <= b)
def test6 (a b : String) : Bool := decide (a >= b)
def test7 (a b : String) : String := a ++ b

def main : IO Unit := do
  IO.println (test1 "a" "a")
  IO.println (test2 "a" "a")
  IO.println (test3 "a" "b")
  IO.println (test4 "a" "b")
  IO.println (test5 "a" "a")
  IO.println (test6 "a" "a")
  IO.println (test7 "a" "b")
