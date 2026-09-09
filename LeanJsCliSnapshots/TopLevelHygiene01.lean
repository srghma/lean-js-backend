prelude
import Init.System.IO

def test1 {α β : Type} (wat : α → β) (a : α) : β := wat a

def main : IO Unit := do
  IO.println (test1 (fun i => i + 1) 42)
