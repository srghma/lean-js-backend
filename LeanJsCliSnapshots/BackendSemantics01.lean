prelude
import Init.System.IO
import Init.Data.Int.Basic

def test1 : Int := 2147483646
def test2 : Int := -2147483647
def test3 : Char := Char.ofNat 0xFFFF
def test4 : Char := Char.ofNat 0

def main : IO Unit := do
  IO.println test1
  IO.println test2
  IO.println (repr test3)
  IO.println (repr test4)
