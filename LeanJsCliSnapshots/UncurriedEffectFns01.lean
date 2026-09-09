def test1 (f : Int → Int → Int → IO Unit) (g : Int → Int) : IO Unit := f (g 1) 2 3
def test2 (f : Int → Int → Int → IO Unit) (g : Int → Int) (i : Int) : IO Unit := f (g 1) 2 i
def test3 (f : Int → Int → Int → IO Unit) (g : Int → Int) (i j : Int) : IO Unit := f (g 1) i j
def test4 (f : Int → Int → Int → IO Unit) (i j k : Int) : IO Unit := f i j k

def test5 (f : Int → Int → Int → IO Unit) (g : Int → Int) : IO Unit := do
  f (g 1) 2 3
  f (g 1) 2 3

def test6 (f : Int → Int → Int → IO Unit) (g : Int → Int) : IO Unit := do
  f (g 1) 2 3
  f (g 1) 2 3
  f (g 1) 2 3
