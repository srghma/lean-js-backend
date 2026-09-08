prelude
import Init.System.IO
import Init.Data.String

def test1 (x : String) : String :=
  "a" ++ ((((("b" ++ x) ++ x) ++ x) ++ x) ++ "c") ++ "d"

def test2 (x : String) : String :=
  "a" ++ ("b" ++ (x ++ (x ++ (x ++ (x ++ "c"))))) ++ "d"

def test3 (x : String) : String :=
  "a" ++ ("b" ++ (x ++ (x ++ (x ++ (x ++ "c"))))) ++ "d" ++
    ((((("e" ++ x) ++ x) ++ x) ++ x) ++ "f") ++ "g"

def main : IO Unit := do
  IO.println (test1 "xy")
  IO.println (test2 "xy")
  IO.println (test3 "xy")
