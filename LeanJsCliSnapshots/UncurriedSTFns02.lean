import Init.System.IO
import Init.Data.Int.Basic

def test1 : Int := 12

def test2 (random : Unit → IO Int) : IO Unit := do
  let f := fun (n : Int) => n
  let n ← random ()
