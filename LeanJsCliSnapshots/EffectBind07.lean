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
