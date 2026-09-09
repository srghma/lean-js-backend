prelude
import Init.System.IO

def when' (bool : Bool) (k : Unit → IO Unit) : IO Unit :=
  if bool then k () else pure ()

def test1 (bool : Bool) : IO Unit := do
  when' bool (fun _ => IO.println "1")
  when' bool (fun _ => IO.println "2")
  when' bool (fun _ => IO.println "3")

def main : IO Unit := do
  test1 true
  test1 false
