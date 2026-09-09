prelude
import Init.System.IO
import Init.Data.Char.Basic
import Init.Data.List.Basic

def charValues (op : Char → Char → Bool) : List Bool :=
  [ op 'a' 'a'
  , op 'a' 'b'
  , op 'b' 'a'
  ]

def test1 := charValues (· == ·)
def test2 := charValues (· != ·)
def test3 := charValues (· < ·)
def test4 := charValues (· > ·)


def main : IO Unit := do
  IO.println (repr test1)
  IO.println (repr test2)
  IO.println (repr test3)
  IO.println (repr test4)
