import Init.Data.Int.Basic
import Init.Data.String.Basic

def flip' {α β γ : Type} (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

def const' {α β : Type} (a : α) : β → α :=
  fun _ => a

def test1 (f : Int → Unit → Unit) (g : String → Unit → Unit) (a : Unit) : Unit := f 1 (g "foo" a)
def test2 (f : Int → Unit → Unit) (g : String → Unit → Unit) (a : Unit) : Unit := f 1 (g "foo" a)
def test3 (f : Int → Int → Unit) (g : Int → Int → Int) : Unit → Unit := fun _ => flip' f 3 (flip' g 2 1)
def test4 {α β γ : Type} (f : α → β → γ) : β → α → γ := flip' f
def test5 {α β : Type} (a : α) : β → α := const' a
def test6 : Int → Int := fun x => x
