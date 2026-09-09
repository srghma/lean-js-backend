prelude
import Init.System.IO
import Init.Core
import Init.Data.String

def f (_ : String) : String := "a"
def g (_ : String) : String := "b"

def test1 := f ∘ g
def test2 := g ∘ (f ∘ g)
def test3 := (f ∘ g) ∘ (f ∘ g)
def test4 := ((g ∘ f) ∘ g) ∘ (f ∘ g)


def main : IO Unit := do
  IO.println (test1 "x")
  IO.println (test2 "x")
  IO.println (test3 "x")
  IO.println (test4 "x")
