prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.String

def test1 (x : Int) : String :=
  match x with
  | 1 => "111"
  | 2 => "2"
  | n => "any: " ++ toString n ++ toString n ++ toString n

structure Product3 where
  a : Int
  b : Int
  c : Int

def test2 (x : Product3) : String :=
  match x with
  | ⟨1, a, b⟩ => toString a ++ toString b ++ "1"
  | ⟨a, 1, b⟩ => toString a ++ toString b ++ "1"
  | ⟨a, b, 1⟩ => toString a ++ toString b ++ "1"
  | ⟨a, b, c⟩ => toString a ++ toString a ++ toString b ++ toString b ++ toString c ++ toString c

def main : IO Unit := do
  IO.println (test1 1)
  IO.println (test1 9)
  IO.println (test2 ⟨1, 2, 3⟩)
  IO.println (test2 ⟨4, 5, 6⟩)
