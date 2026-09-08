prelude
import Init.System.IO
import Init.Data.Int.Basic

def fc2_1 (f g : Int → Int) : Int → Int := f ∘ g
def fc2_2 (f g : Int → Int) : Int → Int := g ∘ (f ∘ g)
def fc2_3 (f g : Int → Int) : Int → Int := (f ∘ g) ∘ (f ∘ g)
def fc2_4 (f g : Int → Int) : Int → Int := ((g ∘ f) ∘ g) ∘ (f ∘ g)

def fc3_1 (f g : Unit → Int → Int) : Int → Int := f () ∘ g ()
def fc3_2 (f g : Unit → Int → Int) : Int → Int := g () ∘ (f () ∘ g ())
def fc3_3 (f g : Unit → Int → Int) : Int → Int := (f () ∘ g ()) ∘ (f () ∘ g ())
def fc3_4 (f g : Unit → Int → Int) : Int → Int := ((g () ∘ f ()) ∘ g ()) ∘ (f () ∘ g ())

def inc : Int → Int := fun x => x + 1
def double : Int → Int := fun x => x * 2
def add3 : Unit → Int → Int := fun _ x => x + 3
def mul4 : Unit → Int → Int := fun _ x => x * 4

def main : IO Unit := do
  IO.println (fc2_1 inc double 5)
  IO.println (fc2_2 inc double 5)
  IO.println (fc2_3 inc double 5)
  IO.println (fc2_4 inc double 5)
  IO.println (fc3_1 add3 mul4 2)
  IO.println (fc3_2 add3 mul4 2)
  IO.println (fc3_3 add3 mul4 2)
  IO.println (fc3_4 add3 mul4 2)
