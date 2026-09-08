prelude
import Init.System.IO
import Init.Data.String.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic

def poke (k : String) (v : Int) (m : List (String × Int)) : List (String × Int) :=
  (k, v) :: m.filter (fun p => p.1 != k)

def deleteKey (k : String) (m : List (String × Int)) : List (String × Int) :=
  m.filter (fun p => p.1 != k)

def test1 : List (String × Int) := []

def test3 : List (String × Int) := 
  let m := []
  let m := poke "a" 1 m
  let m := poke "b" 2 m
  let m := poke "c" 3 m
  m

def test5 : List (String × Int) := 
  let m := []
  let m := poke "a" 1 m
  let m := poke "b" 2 m
  let m := deleteKey "a" m
  let m := deleteKey "b" m
  m

def main : IO Unit := do
  IO.println (repr test1)
  -- We sort to have stable output for comparison if needed, 
  -- but here the order of operations determines the order in List.
  IO.println (repr test3)
  IO.println (repr test5)
