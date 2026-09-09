prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.Int.Basic

def test1 (arr : Array Int) : Option Int :=
  match arr[0]?, arr[1]? with
  | some x, some y => some (x + y)
  | _, _ => none

def test2 (arr : Array Int) : Option Int :=
  match arr[0]? with
  | some x =>
    match arr[1]? with
    | some y => some (x + y)
    | none => none
  | none => none

def main : IO Unit := do
  IO.println (repr (test1 #[1, 2]))
  IO.println (repr (test2 #[1, 2]))
  IO.println (repr (test1 #[1]))
