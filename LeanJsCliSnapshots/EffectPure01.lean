import Init.System.IO
import Init.Data.Int.Basic

def test1 : IO Int := pure 1
def test2 (a : Int) : IO Int := pure (a + 1)
