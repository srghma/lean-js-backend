import Init.System.IO
import Init.Data.Int.Basic

def test1 (random : Unit → IO Int) : IO Unit := do
  let n ← random ()
  if n > 100 then
    IO.println "Too hot"
  else if n < 20 then
    IO.println "Too cold"
  else
    IO.println "Just right"

def test2 (random : Unit → IO Int) : IO Unit := do
  let n ← random ()
  if n > 100 then
    IO.println "Too hot"
  else if n < 20 then
    IO.println "Too cold"
  else
