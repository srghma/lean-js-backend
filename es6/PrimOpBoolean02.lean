prelude
import Init.System.IO
import Init.Data.Bool
import Init.Data.Array.Basic

def boolValues (op : Bool → Bool → Bool) : Array Bool :=
  #[ op true true, op true false, op false true, op false false ]

def test1 := boolValues (fun a b => a && b)
def test2 := boolValues (fun a b => a || b)
def test3 := boolValues (fun a b => a == b)
def test4 := boolValues (fun a b => a != b)
def test5 := boolValues (fun a b => decide (a < b))
def test6 := boolValues (fun a b => decide (a > b))
def test7 := boolValues (fun a b => decide (a <= b))
def test8 := boolValues (fun a b => decide (a >= b))
def test9 := #[ !true, !false ]

def main : IO Unit := do
  IO.println (repr test1)
  IO.println (repr test2)
  IO.println (repr test3)
  IO.println (repr test4)
  IO.println (repr test5)
  IO.println (repr test6)
  IO.println (repr test7)
  IO.println (repr test8)
  IO.println (repr test9)
