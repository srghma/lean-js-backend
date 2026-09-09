def test1 : IO Int := pure 1
def test2 (a : Int) : IO Int := pure (a + 1)
