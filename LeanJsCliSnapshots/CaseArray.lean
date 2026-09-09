prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.String

def test1 : Array Nat → String
  | #[] => "0"
  | #[1] => "1"
  | #[_] => "any1"
  | #[_, 2] => "2"
  | #[_, _, _] => "3"
  | _ => "catch"

def main : IO Unit := do
  IO.println (test1 #[])
  IO.println (test1 #[1])
  IO.println (test1 #[1, 2])
