prelude
import Init.System.IO
import Init.Data.Nat.ToString

def test1 (x : Nat) : IO Unit := do
  IO.println (toString x)


def main : IO Unit := do
  test1 42
