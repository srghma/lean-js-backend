prelude
import Init.System.IO
import Init.Data.Float

def test1 (x : Float) : String :=
  if x == 1.0 then "1"
  else if x == 2.0 then "2"
  else if x == 3.0 then "3"
  else "catch"

def main : IO Unit := do
  IO.println (test1 3.0)
  IO.println (test1 4.0)
