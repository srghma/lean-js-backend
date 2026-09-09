prelude
import Init.System.IO
import Init.Data.String.Basic

def test1 (a : String) : String := "a" ++ "b" ++ a ++ "c" ++ "d"
def test2 (a : String) : String := "a" ++ (("b" ++ a) ++ "c") ++ "d"
def test3 (a : String) : String := "a" ++ ("b" ++ (a ++ "c")) ++ "d"

def main : IO Unit := do
  IO.println (test1 "X")
  IO.println (test2 "X")
  IO.println (test3 "X")
