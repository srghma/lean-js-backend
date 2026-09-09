inductive Fun where
  | Abs : String → Fun → Fun
  | App : Fun → Fun → Fun

def traverseFun1 {f : Type → Type} [Applicative f] (k : Fun → f Fun) : Fun → f Fun
  | Fun.Abs id a => Fun.Abs id <$> k a
  | Fun.App a b => Fun.App <$> k a <*> k b

partial def rewriteBottomUpM {m : Type → Type} [Monad m] (k : Fun → m Fun) : Fun → m Fun := fun a => do
  let a' ← traverseFun1 (rewriteBottomUpM k) a
  k a'

def rewriteBottomUp (k : Fun → Fun) : Fun → Fun := fun a =>
  Id.run (rewriteBottomUpM (m := Id) (fun f => pure (k f)) a)
