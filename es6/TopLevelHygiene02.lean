prelude
import Init.System.IO

def wat : Int := 42

def test1 {α β : Type} (wat : α → β) (a : α) : β := wat a

def test2 {α β : Type} (f : α → β) (a : α) : β := test1 f a

def main : IO Unit := do
  IO.println wat
  IO.println (test2 (fun i => i + 1) 42)
