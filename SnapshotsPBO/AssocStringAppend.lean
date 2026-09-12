-- @js_export: test1, test2, test3
def test1 (x : String) : String :=
  "a" ++ ((((("b" ++ x) ++ x) ++ x) ++ x) ++ "c") ++ "d"

def test2 (x : String) : String :=
  "a" ++ ("b" ++ (x ++ (x ++ (x ++ (x ++ "c"))))) ++ "d"

def test3 (x : String) : String :=
  "a" ++ ("b" ++ (x ++ (x ++ (x ++ (x ++ "c"))))) ++ "d" ++
    ((((("e" ++ x) ++ x) ++ x) ++ x) ++ "f") ++ "g"
