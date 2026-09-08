prelude
import Init.System.IO
import Init.Data.String
import Init.Data.Bool

def test1 (a b : String) : Bool := a == b
def test2 (a b : String) : Bool := a != b
def test3 (a b : String) : Bool := decide (a < b)
def test4 (a b : String) : Bool := decide (a > b)
def test5 (a b : String) : Bool := decide (a <= b)
def test6 (a b : String) : Bool := decide (a >= b)
def test7 (a b : String) : String := a ++ b


def main : IO Unit := do
  IO.println (test1 "foo" "bar")
  IO.println (test2 "foo" "bar")
  IO.println (test3 "foo" "bar")
  IO.println (test4 "foo" "bar")
  IO.println (test5 "foo" "bar")
  IO.println (test6 "foo" "bar")
  IO.println (test7 "foo" "bar")
