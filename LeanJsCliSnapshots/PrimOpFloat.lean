import Init.Data.Float

def test1 (a b : Float) : Float := a + b
def test2 (a b : Float) : Float := a - b
def test3 (a b : Float) : Float := a * b
def test4 (a b : Float) : Float := a / b
def test5 (a : Float) : Float := -a
def test6 (a b : Float) : Bool := decide (a < b)
def test7 (a b : Float) : Bool := decide (a <= b)
