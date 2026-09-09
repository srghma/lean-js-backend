prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.String.Basic
import Init.Data.Bool

structure R where
  foo : Int
  bar : String
  baz : Bool
deriving BEq, Repr

def test1 : Int → Int → Bool := fun a b => a != b
def test2 (a b : Int) : Bool := a != b
def test3 (a : Int) : Bool := 12 != a
def test4 (a : Int) : Bool := a != 12
def test5 : Int → Bool := fun a => 12 != a
def test6 (r : R) : Bool := { foo := 42, bar := "hello", baz := false : R } != r

def main : IO Unit := do
  IO.println (test1 1 2)
  IO.println (test1 1 1)
  IO.println (test2 1 2)
  IO.println (test3 12)
  IO.println (test3 13)
  IO.println (test4 12)
  IO.println (test5 12)
  IO.println (test5 13)
  IO.println (test6 { foo := 42, bar := "hello", baz := false })
  IO.println (test6 { foo := 43, bar := "hello", baz := false })
