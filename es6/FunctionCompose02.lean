prelude
import Init.System.IO

def test1 (f g : Int → Int) : Int → Int := f ∘ g
def test2 (f g : Int → Int) : Int → Int := g ∘ (f ∘ g)
def test3 (f g : Int → Int) : Int → Int := (f ∘ g) ∘ (f ∘ g)
def test4 (f g : Int → Int) : Int → Int := ((g ∘ f) ∘ g) ∘ (f ∘ g)

def main : IO Unit := do
  let f := fun x => x + 1
  let g := fun x => x * 2
  IO.println (test1 f g 10)
  IO.println (test2 f g 10)
  IO.println (test3 f g 10)
  IO.println (test4 f g 10)
