structure ABC where
  a : Int
  b : Int
  c : Int

def test1 (x : ABC) : String :=
  match x with
  | { a := 1, .. } => "0"
  | { b := 1, .. } => "1"
  | { c := 1, .. } => "2"
  | { a := 2, b := 2, .. } => "3"
  | _ => "catch"

structure InnerBC where
  b : Int
  c : Int

structure InnerEF where
  e : Int
  f : Int

structure Outer where
  a : InnerBC
  d : InnerEF

def test2 (x : Outer) : Int :=
  match x with
  | { a := { b := 1, c := 2 }, d := { e := 1, f := 2 } } => 1
  | { a := { b := _, c := 2 }, d := { e := 1, f := 2 } } => 2
  | { a := { b := 1, c := 2 }, d := _ } => 3
  | _ => 4


def main : IO Unit := do
  IO.println (test1 { a := 1, b := 2, c := 3 })
  IO.println (test2 { a := { b := 1, c := 2 }, d := { e := 1, f := 2 } })
  IO.println (test2 { a := { b := 5, c := 2 }, d := { e := 1, f := 2 } })
  IO.println (test2 { a := { b := 1, c := 2 }, d := { e := 9, f := 9 } })
  IO.println (test2 { a := { b := 9, c := 9 }, d := { e := 9, f := 9 } })
