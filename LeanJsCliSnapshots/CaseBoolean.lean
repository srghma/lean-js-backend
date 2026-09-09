prelude
import Init.System.IO

def test1 : Bool → String
  | true => "1"
  | false => "2"

def main : IO Unit := do
  IO.println (test1 true)
  IO.println (test1 false)
