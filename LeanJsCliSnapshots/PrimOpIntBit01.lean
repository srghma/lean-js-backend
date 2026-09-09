prelude
import Init.System.IO
import Init.Data.UInt

def test1 (a b : UInt32) : UInt32 := a &&& b
def test2 (a b : UInt32) : UInt32 := a ||| b
def test3 (a b : UInt32) : UInt32 := a <<< b
def test4 (a b : UInt32) : UInt32 := a >>> b
def test5 (a b : UInt32) : UInt32 := a ^^^ b
def test6 (a b : UInt32) : UInt32 := a >>> b
def test7 (a : UInt32) : UInt32 := ~~~a

def main : IO Unit := do
  IO.println (test1 3 1)
  IO.println (test2 3 4)
  IO.println (test3 1 2)
  IO.println (test4 8 2)
  IO.println (test5 3 1)
  IO.println (test6 8 2)
  IO.println (test7 0)
