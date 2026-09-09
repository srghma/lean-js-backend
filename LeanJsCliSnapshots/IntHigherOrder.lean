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
