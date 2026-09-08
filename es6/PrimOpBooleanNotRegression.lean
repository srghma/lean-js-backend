prelude
import Init.System.IO

def test {α : Type} (comp : α → α → Ordering) (a b : α) : Bool :=
  comp a b != Ordering.eq

def main : IO Unit := do
  IO.println (test (fun (i j : Int) => compare i j) 1 2)
  IO.println (test (fun (i j : Int) => compare i j) 1 1)
