prelude
import Init.System.IO
import Init.Data.Int.Basic

def test (a : Except Int Int) : Int :=
  match some a with
  | some (Except.error b) => b
  | some (Except.ok c) => c
  | none => 42

def main : IO Unit := do
  IO.println (test (Except.error 1))
  IO.println (test (Except.ok 2))
