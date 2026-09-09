inductive ExprF (α : Type) where
  | Lit : Int → ExprF α
  | Add : α → α → ExprF α

def mapExprF {α β : Type} (f : α → β) : ExprF α → ExprF β
  | ExprF.Lit n => ExprF.Lit n
  | ExprF.Add a b => ExprF.Add (f a) (f b)

structure FixExpr where
  unFix : ExprF FixExpr

def lit (n : Int) : FixExpr := ⟨ExprF.Lit n⟩
def add (a b : FixExpr) : FixExpr := ⟨ExprF.Add a b⟩

partial def cata {α : Type} [Inhabited α] (f : ExprF α → α) (fix : FixExpr) : α :=
  f (mapExprF (cata f) fix.unFix)

def evalF : ExprF Int → Int
  | ExprF.Lit n => n
  | ExprF.Add a b => a + b
