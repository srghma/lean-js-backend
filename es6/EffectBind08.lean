prelude
import Init.System.IO
import Init.Data.Int.Basic

def test : IO Int := do
  let a ← (pure 12 : IO Int)
  pure (a + 1)

def main : IO Unit := do
  IO.println (← test)
