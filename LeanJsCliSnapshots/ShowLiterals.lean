prelude
import Init.System.IO
import Init.Data.String.Basic
import Init.Data.Int.Basic
import Init.Data.Float
import Init.Data.Bool
import Init.Data.Char.Basic
import Init.Data.Array.Basic

structure MyRec where
  foo : String
  bar : Bool
deriving Repr

def test1 := toString 42
def test2 := toString 42.0
def test3 := toString true
def test4 := toString "wat"
def test5 := toString 'w'
def test6 := repr ({ foo := "1", bar := true } : MyRec)
def test7 := repr #[1, 2, 3, 4]

def main : IO Unit := do
  IO.println test1
  IO.println test2
  IO.println test3
  IO.println test4
  IO.println test5
  IO.println (toString test6)
  IO.println (toString test7)
