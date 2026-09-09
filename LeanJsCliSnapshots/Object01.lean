prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.String.Basic

def test1 (a : List (String × Int)) : Int := 
  a.find? (fun p => p.1 == "foo") |>.map (fun p => p.2) |>.getD 0

def test2 (a : List (String × Int)) : Int := 
  a.find? (fun p => p.1 == "foo.bar") |>.map (fun p => p.2) |>.getD 0

def test3 (a : List (String × Int)) (b : String) : Int := 
  a.find? (fun p => p.1 == b) |>.map (fun p => p.2) |>.getD 0

def test4 (a : List (String × Int)) : Array String := 
  a.map (fun p => p.1) |>.toArray

def test5 (a : List (String × Int)) : Bool := 
  a.any (fun p => p.1 == "wat")

def main : IO Unit := do
  let obj := [("foo", 1), ("foo.bar", 2), ("wat", 3)]
  IO.println (test1 obj)
  IO.println (test2 obj)
  IO.println (test3 obj "wat")
  IO.println (repr (test4 obj))
  IO.println (test5 obj)
