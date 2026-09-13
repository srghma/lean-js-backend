def test1 (a : List (String × Int)) : Int :=
  a.find? (fun p => p.1 == "foo") |>.map (fun p => p.2) |>.getD 0

def test2 (a : List (String × Int)) : Int :=
  a.find? (fun p => p.1 == "foo.bar") |>.map (fun p => p.2) |>.getD 0

def test3 (a : List (String × Int)) (b : String) : Int :=
  a.find? (fun p => p.1 == b) |>.map (fun p => p.2) |>.getD 0

def test4 (a : List (String × Int)) : Array String :=
  a.map (fun p => p.1) |>.toArray

def test5 (a : List (String × Int)) : Bool :=
  a.any (fun p => p.1 == "wat")
