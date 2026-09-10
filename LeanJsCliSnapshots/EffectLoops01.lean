def test1 (k : Int → Array Int) : IO Unit :=
  flip Array.forM (k 42) fun a => do
    IO.println a
    IO.println (repr a)

def test2 (k : Int → Array Int) : IO Unit := do -- TODO maybe it should join same for loops?
  flip Array.forM (k 42) fun a => IO.println (repr a)
  flip Array.forM (k 42) fun a => IO.println (repr a)
  flip Array.forM (k 42) fun _ => IO.println "wat"

def test3 (arr : Array Int) : IO Unit :=
  flip Array.forM arr fun a =>
    if a < 10 then
      IO.println (repr a)
    else
      pure ()

def test4 (arr : Array Int) : IO Unit :=
  flip Array.forM arr fun a =>
    if a < 10 then
      IO.println (repr a)
    else
      IO.println "wat"
