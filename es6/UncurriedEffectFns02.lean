prelude
import Init.System.IO
import Init.Data.Int.Basic

def test1 : IO Unit := IO.println 12

def test2 (random : Unit → IO Int) : IO Unit := do
  let log := fun (n : Int) => IO.println n
  let n ← random ()
  log n

def main : IO Unit := do
  test1
  test2 (fun _ => pure 42)
