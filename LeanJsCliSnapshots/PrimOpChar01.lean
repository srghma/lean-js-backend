prelude
import Init.System.IO

def test1 (c : Char) : Nat := c.toNat

def main : IO Unit := do
  IO.println (test1 'a')
