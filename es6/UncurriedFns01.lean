prelude
import Init.System.IO
import Init.Data.Int.Basic

def test1 (f : Int → Int → Int → Int) (g : Int → Int) : Int := f (g 1) 2 3
def test2 (f : Int → Int → Int → Int) (g : Int → Int) (i : Int) : Int := f (g 1) 2 i
def test3 (f : Int → Int → Int → Int) (g : Int → Int) (i j : Int) : Int := f (g 1) i j
def test4 (f : Int → Int → Int → Int) (i j k : Int) : Int := f i j k

def main : IO Unit := do
  let f := fun i j k => i + j + k
  let g := fun i => i + 10
  IO.println (test1 f g)
  IO.println (test2 f g 3)
  IO.println (test3 f g 2 3)
  IO.println (test4 f 1 2 3)
