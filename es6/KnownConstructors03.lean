prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.String.Basic

def test (x : Int) : String :=
  let a := if x > 42 then some "Hello" else none
  match a with
  | some str => str ++ ", World!"
  | none => ""

def main : IO Unit := do
  IO.println (test 43)
  IO.println (test 42)
