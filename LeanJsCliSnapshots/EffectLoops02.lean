prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.ToString.Basic

partial def forE (lo hi : Int) (f : Int → IO Unit) : IO Unit := do
  let rec loop (i : Int) : IO Unit := do
    if i < hi then
      f i
      loop (i + 1)
    else
      pure ()
  loop lo

def test1 (lo hi : Int) : IO Unit :=
  forE (lo + 1) (hi + 1) fun a => do
    IO.println (toString a)
    IO.println (toString a)

def test2 (lo hi : Int) : IO Unit := do
  forE (lo + 1) (hi + 1) fun a => IO.println (toString a)
  forE (lo + 1) (hi + 1) fun a => IO.println (toString a)
  forE (lo + 1) (hi + 1) fun _ => IO.println "wat"

def test3 (lo hi : Int) : IO Unit :=
  forE lo hi fun a =>
    if a < 10 then
      IO.println (toString a)
    else
      pure ()

def test4 (lo hi : Int) : IO Unit :=
  forE lo hi fun a =>
    if a < 10 then
      IO.println (toString a)
    else
      IO.println "wat"

def main : IO Unit := do
  test1 0 2
  test2 0 1
  test3 5 15
  test4 5 15
