-- @js_export: test1, test2, test3, test4, test5, test6, test7
def test1 (a b : String) : Bool := a == b
def test2 (a b : String) : Bool := a != b
def test3 (a b : String) : Bool := decide (a < b)
def test4 (a b : String) : Bool := decide (a > b)
def test5 (a b : String) : Bool := decide (a <= b)
def test6 (a b : String) : Bool := decide (a >= b)
def test7 (a b : String) : String := a ++ b
