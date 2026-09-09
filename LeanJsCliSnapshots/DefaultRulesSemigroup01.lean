import Init.Data.Int.Basic
import Init.Data.String.Basic

def test1 (f g : Int → String) : Int → String := fun x => f x ++ g x
def test2 (f g : Int → String) : Int → String := fun x => f x ++ g x ++ f x ++ g x
