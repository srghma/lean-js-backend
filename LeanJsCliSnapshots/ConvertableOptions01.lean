prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.String

structure All where
  foo : Int := 42
  baz : Option Bool := none
  bar : String

def flubImpl (_ : All) : String := "???"

def test1 : String := flubImpl { bar := "Hello" }
def test2 : String := flubImpl { foo := 99, bar := "Hello" }
def test3 : String := flubImpl { foo := 99, bar := "Hello", baz := some true }
-- In test4, bar was Int 42 and baz was Bool true in PureScript, but they were converted to String and Option Bool.
def test4 : String := flubImpl { foo := 99, bar := toString 42, baz := some true }

def main : IO Unit := do
  IO.println test1
  IO.println test2
  IO.println test3
  IO.println test4
