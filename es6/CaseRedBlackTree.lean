inductive Color where
  | Red
  | Black

inductive RedBlackTree (α : Type) where
  | Leaf
  | Node (color : Color) (l : RedBlackTree α) (val : α) (r : RedBlackTree α)

structure Result where
  i : Nat
  a : RedBlackTree Nat
  x : Nat
  b : RedBlackTree Nat
  y : Nat
  c : RedBlackTree Nat
  z : Nat
  d : RedBlackTree Nat

def leaf : RedBlackTree Nat := .Leaf

def node (color : Color) (l : RedBlackTree Nat) (val : Nat) (r : RedBlackTree Nat) : RedBlackTree Nat :=
  .Node color l val r

def renderTree : RedBlackTree Nat → String
  | .Leaf => "."
  | .Node .Red l v r => s!"(R {renderTree l} {v} {renderTree r})"
  | .Node .Black l v r => s!"(B {renderTree l} {v} {renderTree r})"

def renderResult : Result → String
  | { i, a, x, b, y, c, z, d } =>
    s!"{i}|{renderTree a}|{x}|{renderTree b}|{y}|{renderTree c}|{z}|{renderTree d}"

def renderOptionResult : Option Result → String
  | none => "none"
  | some r => renderResult r

def test1 (t : RedBlackTree Nat) : Option Result :=
  match t with
  | .Node .Black (.Node .Red (.Node .Red a x b) y c) z d => some { i := 1, a, x, b, y, c, z, d }
  | .Node .Black (.Node .Red a x (.Node .Red b y c)) z d => some { i := 2, a, x, b, y, c, z, d }
  | .Node .Black a x (.Node .Red (.Node .Red b y c) z d) => some { i := 3, a, x, b, y, c, z, d }
  | .Node .Black a x (.Node .Red b y (.Node .Red c z d)) => some { i := 4, a, x, b, y, c, z, d }
  | _ => none

def main : IO Unit := do
  let t1 := node .Black (node .Red (node .Red leaf 1 leaf) 2 leaf) 3 leaf
  let t2 := node .Black (node .Red leaf 1 (node .Red leaf 2 leaf)) 3 leaf
  let t3 := node .Black leaf 1 (node .Red (node .Red leaf 2 leaf) 3 leaf)
  let t4 := node .Black leaf 1 (node .Red leaf 2 (node .Red leaf 3 leaf))
  let t5 := node .Red leaf 1 leaf
  IO.println (renderOptionResult (test1 t1))
  IO.println (renderOptionResult (test1 t2))
  IO.println (renderOptionResult (test1 t3))
  IO.println (renderOptionResult (test1 t4))
  IO.println (renderOptionResult (test1 t5))
