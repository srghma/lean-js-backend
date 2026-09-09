prelude
import Init.System.IO

def test1 : Nat := 'a'.toNat

def main : IO Unit := do
  IO.println test1
