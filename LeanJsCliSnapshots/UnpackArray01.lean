prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.String.Basic

def test (fn1 : String → String → String) (fn2 : Unit → String) : String :=
  let array := #[ "foo", "bar", "baz", fn2 () ]
  fn1 array[0]! array[2]!

def main : IO Unit := do
  IO.println (test (fun s1 s2 => s1 ++ s2) (fun _ => "qux"))
