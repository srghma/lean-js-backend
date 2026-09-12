def test1 (a b : Int) : Int := a + b
def test2 (a b : Int) : Int := a - b
def test3 (a b : Int) : Bool := a == b
def test4 (a b : Int) : Bool := a != b
def test5 (a b : Int) : Bool := decide (a < b)
def test6 (a b : Int) : Bool := decide (a > b)
def test7 (a b : Int) : Bool := decide (a <= b)
def test8 (a b : Int) : Bool := decide (a >= b)
def test9 (a b : Int) : Int := a * b
def test10 (a b : Int) : Int := a / b
def test11 (a : Int) : Int := -a
