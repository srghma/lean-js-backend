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
