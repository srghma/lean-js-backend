prelude
import Init.System.IO
import Init.Data.Array.Basic

def test1 {α β : Type} (f : α → β) (as : Array α) : IO Unit := do
  let ref ← IO.mkRef #[]
  for a in as do
    let bs ← ref.get
    ref.set (bs.push (f a))

def main : IO Unit := do
  test1 (fun i => i + 1) #[1, 2, 3]
  IO.println "ok"
