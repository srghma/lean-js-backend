prelude
import Init.System.IO
import Init.Data.Int.Basic

structure RecBaz where
  baz : Int
deriving Repr

structure RecFooBaz where
  foo : Int
  bar : RecBaz
deriving Repr

structure RecFooBar where
  foo : Int
  bar : Int
deriving Repr

def view_foo (a : RecFooBaz) : Int := a.foo
def over_bar (f : Int → Int) (a : RecFooBar) : RecFooBar := { a with bar := f a.bar }
def over_bar_baz (f : Int → Int) (a : RecFooBaz) : RecFooBaz := { a with bar := { a.bar with baz := f a.bar.baz } }

def test1 := view_foo
def test2 (a : RecFooBaz) := a.foo

def test3 := over_bar (fun i => i + 1)
def test4 (a : RecFooBar) := { a with bar := a.bar + 1 }

def test5 := over_bar_baz (fun i => i + 1)
def test6 (a : RecFooBaz) := { a with bar := { a.bar with baz := a.bar.baz + 1 } }

def test7 (a : RecFooBar) :=
  let a' := { a with foo := a.foo + 1 }
  { a' with bar := a'.bar + 42 }

def test8 (a : RecFooBar) :=
  let a' := { a with foo := a.foo + 1 }
  { a' with bar := a'.bar + 42 }

def main : IO Unit := do
  let r : RecFooBaz := { foo := 1, bar := { baz := 10 } }
  IO.println (test1 r)
  IO.println (test2 r)
  let r2 : RecFooBar := { foo := 1, bar := 10 }
  IO.println (repr (test3 r2))
  IO.println (repr (test4 r2))
  IO.println (repr (test5 r))
  IO.println (repr (test6 r))
  IO.println (repr (test7 r2))
  IO.println (repr (test8 r2))
