prelude
import Init.System.IO
import Init.Data.UInt

def test1 (a b : UInt32) : UInt32 := (a >>> b) >>> b
def test2 (a b : UInt32) : UInt32 := a >>> (b >>> b)

def main : IO Unit := do
  IO.println (test1 16 1)
  IO.println (test2 16 1)
