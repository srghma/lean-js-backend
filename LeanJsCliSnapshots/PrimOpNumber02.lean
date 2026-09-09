import Init.Data.Float
import Init.Data.Array.Basic

def nan : Float := 0.0 / 0.0

def numValues {α : Type} (op : Float → Float → α) : Array α :=
  #[ op 1.5 1.0, op 1.5 2.0, op 2.5 1.0, op 1.5 (-2.0), op (-1.5) 2.0, op (-1.5) (-1.0), op 1.0 nan ]

def test1 := numValues (fun a b => a + b)
def test2 := numValues (fun a b => a - b)
def test3 := numValues (fun a b => a == b)
def test4 := numValues (fun a b => a != b)
def test5 := numValues (fun a b => decide (a < b))
def test6 := numValues (fun a b => decide (a > b))
def test7 := numValues (fun a b => decide (a <= b))
def test8 := numValues (fun a b => decide (a >= b))
def test9 := numValues (fun a b => a * b)
def test10 := numValues (fun a b => a / b)
def test11 := #[ -1.5, -(-1.5) ]
