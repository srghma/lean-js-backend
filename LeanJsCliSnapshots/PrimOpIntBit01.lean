-- @js_export: test1, test2, test3, test4, test5, test6, test7
def test1 (a b : UInt32) : UInt32 := a &&& b
def test2 (a b : UInt32) : UInt32 := a ||| b
def test3 (a b : UInt32) : UInt32 := a <<< b
def test4 (a b : UInt32) : UInt32 := a >>> b
def test5 (a b : UInt32) : UInt32 := a ^^^ b
def test6 (a b : UInt32) : UInt32 := a >>> b
def test7 (a : UInt32) : UInt32 := ~~~a
