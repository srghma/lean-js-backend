-- Fusion02 is Unfold-based (Pull / Forward)
-- → In Lean std, this corresponds to for x in arr or Array.filterMap.

-- 1. Church-encoded Step
def Step (α : Type) (s : Type) : Type 1 :=
  {r : Type} → (Unit → r) → (s → α → r) → r

-- 2. Existential Unfold Stream
structure Unfold (α : Type) where
  State : Type
  seed  : State
  step  : State → Step α State

-- 3. Stream combinators (notice `{r}` added to `step`)
@[inline]
def mapU (f : α → β) (u : Unfold α) : Unfold β where
  State := u.State
  seed  := u.seed
  step s {_r} nothing just :=
    u.step s nothing (fun s' a => just s' (f a))

@[inline]
unsafe def filterMapU (f : α → Option β) (u : Unfold α) : Unfold β where
  State := u.State
  seed  := u.seed
  step s2 {r} nothing just :=
    let rec loop s3 :=
      u.step s3 nothing (fun s4 a =>
        match f a with
        | none   => loop s4
        | some b => just s4 b)
    loop s2

@[inline]
unsafe def filterU (p : α → Bool) (u : Unfold α) : Unfold α :=
  filterMapU (fun a => if p a then some a else none) u

-- 4. Conversions (notice `{r}` added to `step`)
@[inline]
def fromArray (arr : Array α) : Unfold α where
  State := Nat
  seed  := 0
  step ix {r} nothing just :=
    if h : ix < arr.size then
      just (ix + 1) arr[ix]
    else
      nothing ()

@[inline]
unsafe def toArray (u : Unfold α) : Array α :=
  let rec loop (s : u.State) (acc : List α) : Array α :=
    u.step s
      (fun _ => acc.reverse.toArray)
      (fun s' a => loop s' (a :: acc))
  loop u.seed []

-- @[inline] export overArray
@[inline]
unsafe def overArray (f : Unfold α → Unfold β) (arr : Array α) : Array β :=
  toArray (f (fromArray arr))

-- 5. Helper for dropPrefix1
@[inline]
def dropPrefix1 (s : String) : Option String :=
  if s.startsWith "1" then some (s.drop 1).toString else none

-- 6. The fused pipeline
unsafe def test (arr : Array Int) : Array String :=
  flip overArray arr fun u =>
    u
      |> mapU (· + 1)
      |> mapU toString
      |> filterMapU dropPrefix1
      |> mapU ("2" ++ ·)
      |> filterU (· != "wat")
      |> mapU (· ++ "1")
