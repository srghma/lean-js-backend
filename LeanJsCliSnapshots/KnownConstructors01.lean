import Init.Data.Option.Basic
import Init.Data.String.Basic

def test1 : String :=
  (some "c").map (fun _ => "b") |>.getD "a"
