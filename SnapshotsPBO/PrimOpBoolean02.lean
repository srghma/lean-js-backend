-- @js_export: boolValues, test1, test2, test3, test4, test5, test6, test7, test8, test9
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
