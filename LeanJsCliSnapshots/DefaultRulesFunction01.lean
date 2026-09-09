def F := ∀ {α β γ : Type}, α → β → γ

def flip' {α β γ : Type} (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

def const' {α β : Type} (a : α) : β → α :=
  fun _ => a

-- test1: annotate that (g "foo" a) produces Unit
def test1 (f : F) (g : F) (a : Unit) : Unit :=
  f 1 <| (g "foo" a : Unit)

-- test2: annotate intermediate pipeline step
def test2 (f : F) (g : F) (a : Unit) : Unit :=
  (a |> g "foo" : Unit) |> f 1

-- test3: annotate intermediate flip result (say, Int)
def test3 (f : F) (g : F) : Unit → Unit :=
  fun _ => flip' f 3 $ (flip' g 2 1 : Int)

-- test4: works as-is
def test4 (f : F) : F :=
  fun b a => flip' f a b

-- test5: works as-is
def test5 {α β : Type} (a : α) : β → α :=
  const' a

-- test6: works as-is (and remains fully polymorphic!)
def test6 {α : Type} : α → α :=
  flip' const' 42
