import Init.System.IO

def test1 : IO Unit := do
  IO.println "1"
  let value ← IO.println "2"
  IO.println "3"
  pure value
