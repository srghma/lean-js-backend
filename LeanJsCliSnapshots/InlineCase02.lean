prelude
import Init.System.IO
import Init.Data.Int.Basic

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

def main : IO Unit := do
  IO.println (test1 (fun _ => 0) (some 41))
  IO.println (test1 (fun _ => 0) none)
  IO.println (test2 (fun _ => 10) (fun x _ => x + 100) (some 42))
  IO.println (@test2 Int Int (fun _ => 10) (fun x _ => x + 100) none)
  IO.println (test3 (fun _ => 0) (some 41))
  IO.println (test3 (fun _ => 0) none)
  IO.println (test4 (fun _ => 10) (fun x _ => x + 100) (some 42))
  IO.println (@test4 Int Int (fun _ => 10) (fun x _ => x + 100) none)
  IO.println (test5 10 (fun x _ => x + 100) (some ()))
