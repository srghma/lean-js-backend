import Init.System.IO
import Init.Data.Int.Basic

def test1 : IO (IO.Ref Int) := IO.mkRef 42

def test2 {α : Type} (g : Int → α) : IO (IO.Ref α) := IO.mkRef (g 42)

def test3 {α : Type} (r : IO.Ref α) : IO α := r.get

def test4 {α β : Type} (g : α → IO.Ref β) (r : α) : IO β := (g r).get

def test5 (r : IO.Ref Int) : IO Unit := r.set 42

def test6 {α : Type} (g : Int → α) (r : IO.Ref α) : IO Unit := r.set (g 42)

def test7 {α : Type} (g : α → α) (r : IO.Ref α) : IO α := r.modifyGet fun a => let a' := g a; (a', a')

def test8 {α : Type} (g : ∀ {β}, β → β) (r : IO.Ref α) : IO α := r.modifyGet fun a => let a' := g a; (a', a')

def test9 (g : Int → Int) : IO Int := do
  let ref ← IO.mkRef (g 42)
  let prev ← ref.get
  ref.set (prev + 1)
  ref.modify (fun x => x + 1)
  ref.get
