prelude
import Init.System.IO
import Init.Data.Nat.ToString
import Init.Data.Int.ToString
import Init.Data.Bool
import Init.Data.String
import Init.Data.Char.Basic

def test1 : String := toString 42
def test2 : String := toString (42 : Int)
def test3 : String := toString true
def test4 : String := toString "wat"
def test5 : String := toString 'w'


def main : IO Unit := do
  IO.println test1
  IO.println test2
  IO.println test3
  IO.println test4
  IO.println test5
