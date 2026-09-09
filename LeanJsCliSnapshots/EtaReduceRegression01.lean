def foldString : Option String → String
  | some a => a
  | none   => ""

def test : Option String → String := foldString
