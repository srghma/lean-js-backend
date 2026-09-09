def guardList {M : Type} (empty : M) (b : Bool) (m : M) : M :=
  if b then m else empty

def test1 (b : Bool) : List Int :=
  guardList [] b [1, 2, 3]

def test2 (f : List Int → List Int) (b : Bool) : List Int :=
  guardList [] b (f [1, 2, 3])
