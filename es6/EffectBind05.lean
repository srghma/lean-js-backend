prelude
import Init.System.IO

def MyId (α : Type) := Unit → α

instance : Monad MyId where
  pure a := fun _ => a
  bind x k := k (x ())

def test1 (k : Unit → IO Unit) : IO Unit := do
  let _ ← pure ()
  k ()

def test2 {α : Type} (k : Unit → MyId α) : MyId α := do
  let _ ← pure ()
  k ()

def main : IO Unit := do
  test1 (fun _ => IO.println "test1")
  IO.println (test2 (fun _ => fun _ => "test2") ())
