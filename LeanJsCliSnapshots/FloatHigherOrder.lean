import Init.Data.Bool
import Init.Data.Float
import Init.Data.OfScientific
import Init.Data.List.Basic

def numValues (op : Float → Float → α) : List α :=
  [ op 1.5 1.0
  , op 1.5 2.0
  , op 2.5 1.0
  , op 1.5 (-2.0)
  , op (-1.5) 2.0
  , op (-1.5) (-1.0)
  ]

def test1 := numValues (· + ·)
def test2 := numValues (· - ·)
def test3 := numValues (fun a b => Float.beq a b)
def test4 := numValues (fun a b => !Float.beq a b)
def test5 := numValues (fun a b => decide (decide (a < b)))
def test6 := numValues (fun a b => decide (a ≤ b))
def test9 := numValues (· * ·)
def test10 := numValues (· / ·)
def test11 := [ -1.5, -(-1.5) ]
