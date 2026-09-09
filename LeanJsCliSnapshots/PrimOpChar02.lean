prelude
import Init.System.IO
import Init.Data.Char.Basic
import Init.Data.Array.Basic

def charValues (op : Char → Char → Bool) : Array Bool :=
  #[ op 'a' 'a', op 'a' 'b', op 'b' 'a' ]

def test1 := charValues (fun a b => a == b)
def test2 := charValues (fun a b => a != b)
def test3 := charValues (fun a b => decide (a < b))
def test4 := charValues (fun a b => decide (a > b))
def test5 := charValues (fun a b => decide (a <= b))
def test6 := charValues (fun a b => decide (a >= b))

def main : IO Unit := do
  IO.println (repr test1)
  IO.println (repr test2)
  IO.println (repr test3)
  IO.println (repr test4)
  IO.println (repr test5)
  IO.println (repr test6)
