-- @js_export: test1, test2, test3, test4, test5
def test1 (a : Float) : Float := a + (a + (a + a))
def test2 (a : Float) : Float := ((a + a) + a) + a
def test3 (a : Float) : Float := a + (a + (a - a))
def test4 (a : Float) : Float := ((a - a) + a) + a
def test5 (a : Float) : Float := (a - a) + (a + a)
