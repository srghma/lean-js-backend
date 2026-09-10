def test1 (random : IO Int) : IO Unit := do
  let n ← random
  if n > 100 then
    IO.println "Too hot"
  else if n < 20 then
    IO.println "Too cold"
  else
    IO.println "Just right"

def test2 (random : IO Int) : IO Unit := do
  let n ← random
  if n > 100 then
    IO.println "Too hot"
  else if n < 20 then
    IO.println "Too cold"
  else
    IO.println "Just right"
  IO.println "Done"
