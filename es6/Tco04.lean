prelude
import Init.System.IO

def test1 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => test1 (n + 1)

def main : IO Unit := do
  IO.println (test1 9)
