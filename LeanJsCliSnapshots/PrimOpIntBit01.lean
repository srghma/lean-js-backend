import Init.Data.UInt

def test1 (a b : UInt32) : UInt32 := a &&& b
def test2 (a b : UInt32) : UInt32 := a ||| b
def test3 (a b : UInt32) : UInt32 := a <<< b
def test4 (a b : UInt32) : UInt32 := a >>> b
def test5 (a b : UInt32) : UInt32 := a ^^^ b
def test6 (a b : UInt32) : UInt32 := a >>> b
def test7 (a : UInt32) : UInt32 := ~~~a
