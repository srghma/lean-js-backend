prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.List.Basic

def guardList {M : Type} (empty : M) (b : Bool) (m : M) : M :=
  if b then m else empty

def test1 (b : Bool) : List Int :=
  guardList [] b [1, 2, 3]

def test2 (f : List Int → List Int) (b : Bool) : List Int :=
  guardList [] b (f [1, 2, 3])

def main : IO Unit := do
  IO.println (repr (test1 true))
  IO.println (repr (test1 false))
  IO.println (repr (test2 (fun xs => xs ++ [4]) true))
  IO.println (repr (test2 (fun xs => xs ++ [4]) false))
