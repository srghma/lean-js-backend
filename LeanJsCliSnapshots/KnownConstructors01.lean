prelude
import Init.System.IO
import Init.Data.Option.Basic
import Init.Data.String.Basic

def test1 : String :=
  (some "c").map (fun _ => "b") |>.getD "a"

def main : IO Unit := do
  IO.println test1
