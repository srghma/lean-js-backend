prelude
import Init.System.IO
import Init.Data.Array.Basic

def test1 : Array Int := Id.run do
  let mut arr := #[]
  pure arr

def main : IO Unit := do
  IO.println (repr test1)
