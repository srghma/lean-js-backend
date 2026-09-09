def intValues {α : Type} (op : Int → Int → α) : Array α :=
  #[ op 1 1, op 1 2, op 2 1, op 1 (-2), op (-1) 2, op (-1) (-1) ]

def test1 := intValues (fun a b => a + b)
def test2 := intValues (fun a b => a - b)
def test3 := intValues (fun a b => a == b)
def test4 := intValues (fun a b => a != b)
def test5 := intValues (fun a b => decide (a < b))
def test6 := intValues (fun a b => decide (a > b))
def test7 := intValues (fun a b => decide (a <= b))
def test8 := intValues (fun a b => decide (a >= b))
def test9 := intValues (fun a b => a * b)
def test10 := intValues (fun a b => a / b)
def test11 := #[ -1, -(-1) ]
