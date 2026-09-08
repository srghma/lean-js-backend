prelude
import Init.System.IO
import Init.Data.Bool
import Init.Data.Int.Basic

def test1 (a b c : Bool) : Int :=
  if a then
    if b then
      1
    else if c then
      2
    else
      3
  else if c then
    2
  else
    3

def main : IO Unit := do
  IO.println (test1 true true true)
  IO.println (test1 true false true)
  IO.println (test1 true false false)
  IO.println (test1 false true true)
  IO.println (test1 false true false)
