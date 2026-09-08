prelude
import Init.System.IO
import Init.Data.Array.Basic

def test1 {α : Type} (a : Array α) : Int := (a.size : Int)

def test2 {α : Type} [Inhabited α] (a : Array α) : α := a[2]!

def test3 {α : Type} (a : Array α) : Int := (a.size : Int)

def test4 {α : Type} [Inhabited α] (a : Array α) : α := a[2]!

def main : IO Unit := do
  let a := #[1, 2, 3, 4]
  IO.println (test1 a)
  IO.println a[2]!
  IO.println (test3 a)
  IO.println a[2]!
