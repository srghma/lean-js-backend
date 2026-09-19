/-
# Seven proof-carrying variants of each of the seven shapes

`ExamplesProofFields/Shapes.lean` gives one specimen per shape.  This file gives **seven
per shape**, forty-nine declarations in all, so that the rule can be read off rather than
taken on trust.  In every group the variants are, in order:

1. the baseline, with no proof field at all;
2. one proof field;
3. a proof field in every constructor;
4. a proof field that mentions a *parameter* of the declaration;
5. a data field whose type depends on an earlier field (an index, a `Vector`, …);
6. two or more proof fields in one constructor;
7. the **collapse**: the same declaration with one more field turned into a proof, which
   is the one case where the shape changes.

`scripts/dump-shape.lean` computes the shape of every inductive in this module from the
environment — counting the fields that survive erasure — and
`ExamplesProofFields/Variants-Shapes.txt` is its output.  That file, not this comment, is
the evidence for the shape named in each group heading.
-/

namespace ExamplesProofFields.Variants

/-! ## Group E — `enum`: a sum of ≥ 3 constructors with no surviving field -/

namespace Enum

inductive V1 where
  | a | b | c

inductive V2 (n : Nat) where
  | a | b (h : 0 < n) | c

inductive V3 (n : Nat) where
  | a (h : n = n) | b (h : 0 < n) | c (h : n ≤ n)

inductive V4 (cap : Nat) where
  | a | b (h : cap < 10) | c | d

inductive V5 (xs : List Nat) where
  | a | b (h : xs ≠ []) | c

inductive V6 (n : Nat) where
  | a | b (h1 : 0 < n) (h2 : n ≠ 1) | c

/-- The collapse: two constructors, so a `Ty.bool` rather than an enum. -/
inductive V7 (n : Nat) where
  | yes (h : 0 < n) | no (h : n = 0)

end Enum

/-! ## Group R — `record`: one constructor, ≥ 2 surviving fields -/

namespace Record

structure V1 where
  x : Nat
  y : Nat

structure V2 where
  x : Nat
  y : Nat
  h : x ≤ y

structure V3 (cap : Nat) where
  x : Nat
  y : Nat
  hx : x ≤ cap
  hy : y ≤ cap

structure V4 where
  flag : Bool
  n : Nat
  h : flag = true

/-- An index and a value that depends on it; `Vector Nat n` is itself an array and a
    proof, so it erases to an array. -/
structure V5 where
  n : Nat
  v : Vector Nat n

structure V6 where
  a : Nat
  b : Nat
  c : Nat
  h1 : a ≤ b
  h2 : b ≤ c

/-- The collapse: one surviving field, so a newtype — its `Ty` is `Nat`'s. -/
structure V7 (cap : Nat) where
  v : Nat
  h : v ≤ cap

end Record

/-! ## Group U — `taggedUnion`: ≥ 2 constructors, at least one with a surviving field -/

namespace Union

inductive V1 where
  | none
  | some (v : Nat)

inductive V2 (cap : Nat) where
  | missing (h : 0 < cap)
  | value (v : Nat) (h : v ≤ cap)

inductive V3 where
  | a (x : Nat)
  | b (y : Bool)

inductive V4 (cap : Nat) where
  | a (x : Nat) (h : x ≤ cap)
  | b (y : Bool) (h : cap ≠ 0)
  | c

inductive V5 where
  | empty
  | mk (n : Nat) (v : Vector Nat n)

inductive V6 (n : Nat) where
  | a (x : Nat) (h1 : x < n) (h2 : 0 < x)
  | b (h : n = 0)

/-- The collapse: no constructor keeps a field, and there are three of them, so an
    `enum`. -/
inductive V7 (n : Nat) where
  | a (h : 0 < n)
  | b (h : n = 0)
  | c

end Union

/-! ## Group T — `recTaggedUnion`: a recursive sum -/

namespace RecUnion

inductive V1 where
  | leaf
  | node (n : Nat) (l r : V1)

inductive V2 where
  | leaf
  | node (n : Nat) (h : 0 < n) (l r : V2)

inductive V3 (cap : Nat) where
  | leaf (h : 0 < cap)
  | node (n : Nat) (h : n < cap) (l r : V3 cap)

inductive V4 where
  | leaf
  | node (n : Nat) (h : 0 < n) (kids : List V4)

inductive V5 where
  | leaf
  | node (k : Nat) (kids : Array V5)

inductive V6 (cap : Nat) where
  | leaf
  | tip (n : Nat) (h1 : n < cap) (h2 : 0 < n)
  | node (l r : V6 cap)

/-- There is no collapse out of this group, and the reason is worth recording: a proof
    field can never *hold* a recursive occurrence.  Writing `node (n : Nat) (h : Nonempty V7)`
    is rejected by the kernel — "mutually inductive types must live in the same universe" —
    so a recursive sum stays a recursive sum however many proofs are added to it.  The
    nearest thing to a collapse is this: every data field except the recursive ones is a
    proof, so the payload is `[[], [self 0, self 0]]` rather than `[[], [nat, self 0, self 0]]`. -/
inductive V7 (cap : Nat) where
  | leaf
  | node (h : 0 < cap) (l r : V7 cap)

end RecUnion

/-! ## Group O — `recObject`: a recursive single-constructor type with ≥ 2 fields -/

namespace RecObject

structure V1 where
  n : Nat
  kids : Array V1

structure V2 where
  n : Nat
  h : 0 < n
  kids : Array V2

structure V3 where
  n : Nat
  kids : List V3

structure V4 where
  n : Nat
  flag : Bool
  h : flag = true
  kids : Array V4

structure V5 (cap : Nat) where
  n : Nat
  kids : Array (V5 cap)
  h : n ≤ cap

structure V6 where
  n : Nat
  next : Option V6

/-- The collapse: one surviving field, so a recursive *newtype* — a `recAlias`. -/
structure V7 (cap : Nat) where
  kids : Array (V7 cap)
  h : 0 < cap

end RecObject

/-! ## Group A — `recAlias`: a recursive newtype -/

namespace RecAlias

structure V1 where
  kids : Array V1

structure V2 (cap : Nat) where
  kids : Array (V2 cap)
  h : 0 < cap

structure V3 where
  kids : List V3

structure V4 where
  next : Option V4

structure V5 (cap : Nat) where
  kids : List (V5 cap)
  h1 : 0 < cap
  h2 : cap ≠ 1

structure V6 (n : Nat) where
  kids : Array (V6 n)
  h : n = n

/-- The collapse: a second surviving field, so a `recObject` again. -/
structure V7 where
  n : Nat
  kids : Array V7

end RecAlias

/-! ## Group M — `mutualRecursiveFamily`: a genuinely mutual block -/

namespace Family

mutual
inductive N1 where | node (label : Nat) (kids : F1)
inductive F1 where | nil | cons (hd : N1) (tl : F1)
end

mutual
inductive N2 where | node (label : Nat) (h : 0 < label) (kids : F2)
inductive F2 where | nil | cons (hd : N2) (tl : F2)
end

mutual
inductive N3 (cap : Nat) where | node (label : Nat) (kids : F3 cap)
inductive F3 (cap : Nat) where | nil (h : 0 < cap) | cons (hd : N3 cap) (tl : F3 cap)
end

mutual
inductive N4 (cap : Nat) where | node (label : Nat) (h : label < cap) (kids : F4 cap)
inductive F4 (cap : Nat) where | nil (h : 0 < cap) | cons (hd : N4 cap) (tl : F4 cap)
end

mutual
inductive N5 where | node (label : Nat) (kids : F5)
inductive F5 where | nil | cons (hd : N5) (tl : F5) | tagged (t : T5) (tl : F5)
inductive T5 where | one (n : Nat) | two (kids : F5)
end

mutual
inductive N6 where | node (label : Nat) (h : 0 < label) (kids : Array F6)
inductive F6 where | nil | cons (hd : N6) (tl : F6)
end

/-! The collapse: `F7`'s constructors keep no field, so `F7` is an `enum` that mentions no
other member, and `N7` — whose only surviving field is an `F7` — is a newtype for it.  A
block like this is not a recursive family at all; it is two independent declarations that
happen to be written together. -/

mutual
inductive N7 (cap : Nat) where | node (kids : F7 cap) (h : 0 < cap)
inductive F7 (cap : Nat) where | a (h : 0 < cap) | b (h : cap = 0) | c
end

end Family

end ExamplesProofFields.Variants
