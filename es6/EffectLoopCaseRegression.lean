prelude
import Init.System.IO
import Init.Data.List.Basic
import Init.Data.Option.Basic

def test (eff : Unit → IO (Option (List String))) : IO Unit := do
  let res ← eff ()
  match res with
  | none => pure ()
  | some as => as.forM IO.println

def main : IO Unit := do
  test (fun _ => pure (some ["a", "b", "c"]))
  test (fun _ => pure none)
