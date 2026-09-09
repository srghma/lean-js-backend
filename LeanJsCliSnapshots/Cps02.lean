import Init.Data.Int.Basic

def CPS (α : Type) (ρ : Type) := (α → ρ) → ρ

@[inline] def pureCPS {α ρ : Type} (a : α) : CPS α ρ := fun k => k a
@[inline] def bindCPS {α β ρ : Type} (ma : CPS α ρ) (f : α → CPS β ρ) : CPS β ρ := fun k => ma (fun a => f a k)

def test1 (x : Int) : Int :=
  let ma : CPS Int Int := pureCPS (x + 1)
  let mb : CPS Int Int := bindCPS ma (fun y => pureCPS (y * 2))
  mb (fun x => x)

def test2 (x : Int) : Int :=
  let ma : CPS Int Int := pureCPS (x + 1)
  let mb : CPS Int Int := bindCPS ma (fun y => if y < 10 then pureCPS y else pureCPS (y * 2))
  mb (fun x => x)
