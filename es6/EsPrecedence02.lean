prelude
import Init.System.IO
import Init.Data.Float

def test1 (a : Float) : Float := a + (a + (a + a))
def test2 (a : Float) : Float := ((a + a) + a) + a
def test3 (a : Float) : Float := a + (a + (a - a))
def test4 (a : Float) : Float := ((a - a) + a) + a
def test5 (a : Float) : Float := (a - a) + (a + a)

def main : IO Unit := do
  IO.println (toString (test1 1.0))
  IO.println (toString (test2 1.0))
  IO.println (toString (test3 1.0))
  IO.println (toString (test4 1.0))
  IO.println (toString (test5 1.0))
