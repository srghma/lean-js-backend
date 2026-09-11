-- @js_export: test1, test2, test3
def test1 (a : String) : String := "a" ++ "b" ++ a ++ "c" ++ "d"
def test2 (a : String) : String := "a" ++ (("b" ++ a) ++ "c") ++ "d"
def test3 (a : String) : String := "a" ++ ("b" ++ (a ++ "c")) ++ "d"
