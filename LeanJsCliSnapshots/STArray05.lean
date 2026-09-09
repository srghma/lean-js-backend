prelude
import Init.System.IO
import Init.Data.Array.Basic

def test (x : Bool) : Array Int := Id.run do
  let mut arr := #[]
  if x then
    arr := arr.push 1
  else
    arr := #[2] ++ arr
  pure arr

def main : IO Unit := do
  IO.println (repr (test true))
  IO.println (repr (test false))
