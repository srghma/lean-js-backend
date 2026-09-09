def test1 (f g : Unit → Int → Int) : Int → Int := f () ∘ g ()
def test2 (f g : Unit → Int → Int) : Int → Int := g () ∘ (f () ∘ g ())
def test3 (f g : Unit → Int → Int) : Int → Int := (f () ∘ g ()) ∘ (f () ∘ g ())
def test4 (f g : Unit → Int → Int) : Int → Int := ((g () ∘ f ()) ∘ g ()) ∘ (f () ∘ g ())
