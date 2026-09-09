prelude
import Init.System.IO
import Init.Data.Array.Basic

def test1 (a : Array α) : Nat := a.size


def main : IO Unit := do
  IO.println (test1 #[1, 2, 3])
