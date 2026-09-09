prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.Int.DivMod
import Init.Data.Bool
import Init.Data.List.Basic

def intValues (op : Int → Int → α) : List α :=
  [ op 1 1
  , op 1 2
  , op 2 1
  , op 1 (-2)
  , op (-1) 2
  , op (-1) (-1)
  ]

def test1 := intValues (· + ·)
def test2 := intValues (· - ·)
def test3 := intValues (· == ·)
def test4 := intValues (· != ·)
def test5 := intValues (fun a b => decide (decide (a < b)))
def test9 := intValues (· * ·)
def test10 := intValues (· / ·)
def test11 := [ -1, -(-1) ]


def main : IO Unit := do
  IO.println (repr test1)
  IO.println (repr test2)
  IO.println (repr test3)
  IO.println (repr test4)
  IO.println (repr test5)
  IO.println (repr test9)
  IO.println (repr test10)
  IO.println (repr test11)
