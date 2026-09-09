prelude
import Init.System.IO

def test1 : Bool → Bool → Bool → Int
  | _, false, true => 1
  | false, true, _ => 2
  | _, _, false => 3
  | _, _, true => 4

def main : IO Unit := do
  IO.println (test1 true false true)
  IO.println (test1 false true false)
