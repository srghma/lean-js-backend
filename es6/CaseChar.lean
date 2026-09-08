prelude
import Init.System.IO

def test1 : Char → String
  | 'a' => "1"
  | 'b' => "2"
  | 'c' => "3"
  | _ => "catch"

def main : IO Unit := do
  IO.println (test1 'a')
  IO.println (test1 'z')
