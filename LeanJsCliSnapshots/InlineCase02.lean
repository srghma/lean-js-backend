def maybe {α β : Type} (d : β) (f : α → β) : Option α → β
  | some a => f a
  | none => d

def maybe' {α β : Type} (d : Unit → β) (f : α → β) : Option α → β
  | some a => f a
  | none => d ()

-- Terms are purposefully eta-expanded.

def test1 (f : Unit → Int) (z : Option Int) : Int := maybe (f ()) (fun x => x + 1) z

def test2 {α β : Type} (f : Unit → β) (g : Int → α → β) (z : Option α) : β := maybe (f ()) (g 1) z

def test3 (f : Unit → Int) (z : Option Int) : Int := maybe' f (fun x => x + 1) z

def test4 {α β : Type} (f : Unit → β) (g : Int → α → β) (z : Option α) : β := maybe' f (g 1) z

def test5 {α : Type} (a : Int) (g : Int → α → Int) (z : Option α) : Int := maybe' (fun _ => a + 1) (g 1) z
