prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.Int.Basic

def test1 (k : Int → Array Int) : IO Unit :=
  Array.forM (fun a => do
    IO.println (repr a)
    IO.println (repr a)) (k 42)

def test2 (k : Int → Array Int) : IO Unit := do
  Array.forM (fun a => IO.println (repr a)) (k 42)
  Array.forM (fun a => IO.println (repr a)) (k 42)
  Array.forM (fun _ => IO.println "wat") (k 42)

def test3 (arr : Array Int) : IO Unit :=
  Array.forM (fun a =>
    if a < 10 then
      IO.println (repr a)
    else
      pure ()) arr

def test4 (arr : Array Int) : IO Unit :=
  Array.forM (fun a =>
    if a < 10 then
      IO.println (repr a)
    else
      IO.println "wat") arr

def main : IO Unit := do
  test1 (fun x => #[x, x + 1])
  test2 (fun x => #[x])
  test3 #[5, 15]
  test4 #[5, 15]
