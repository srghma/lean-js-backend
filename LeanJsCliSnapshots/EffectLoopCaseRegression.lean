import Init.System.IO
import Init.Data.List.Basic
import Init.Data.Option.Basic

def test (eff : Unit → IO (Option (List String))) : IO Unit := do
  let res ← eff ()
  match res with
  | none => pure ()
