prelude
import Init.System.IO
import Init.Data.Int.Basic

def test1 : Int := 2000000000 + 2000000000
def test2 : Int := -2000000000 - 2000000000
def test3 : Int := 2000000000 * 2000000000
def test4 (a : Int) : Int := 2000000000 + a + 2000000000

def main : IO Unit := do
  IO.println test1
  IO.println test2
  IO.println test3
  IO.println (test4 1)
