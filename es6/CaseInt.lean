prelude
import Init.System.IO
import Init.Data.Int.Basic

def test1 : Int → String
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | _ => "catch"

def main : IO Unit := do
  IO.println (test1 2)
  IO.println (test1 9)
