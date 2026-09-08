prelude
import Init.System.IO
import Init.Data.Int.Basic

def test (random : Unit → IO Int) (value : Unit → Int) : IO Int := do
  let x ← random ()
  let n ← do
    let a := 
      let b := 
        let c := value ()
        c + c
      b + b
    let x ← random ()
    let y ← random ()
    pure (x + y + a + a)
  let m ← random ()
  pure (x + n - m)

def main : IO Unit := do
  let ref ← IO.mkRef 0
  let random := fun _ => do
    let val ← ref.get
    ref.set (val + 1)
    pure (val + 1)
  IO.println (← test random (fun _ => 10))
