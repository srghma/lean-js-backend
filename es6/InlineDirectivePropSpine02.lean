prelude
import Init.System.IO

def testImpl (u : Unit) : Unit := u

def test1 : Unit := testImpl ()
def test2 : Unit := testImpl ()

def main : IO Unit := do
  IO.println (repr test1)
  IO.println (repr test2)
