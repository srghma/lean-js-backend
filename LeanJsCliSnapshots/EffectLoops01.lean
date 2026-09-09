def test1 (k : Int → Array Int) : IO Unit :=
  Array.forM (fun a => do
    IO.println (repr a)
    IO.println (repr a)) (k 42)

def test2 (k : Int → Array Int) : IO Unit := do
  Array.forM (fun a => IO.println (repr a)) (k 42)
  Array.forM (fun a => IO.println (repr a)) (k 42)
  Array.forM (fun _ => IO.println "wat") (k 42)

def test3 (arr : Array Int) : IO Unit :=
  Array.forM (fun a =>
    if a < 10 then
      IO.println (repr a)
    else
      pure ()) arr

def test4 (arr : Array Int) : IO Unit :=
  Array.forM (fun a =>
    if a < 10 then
      IO.println (repr a)
    else
