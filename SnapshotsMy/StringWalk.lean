/-!
Walking a string one position at a time. A Lean string position is a byte offset into
the UTF-8 encoding of the string, so every primitive that takes one is written in
terms of `_utf8(s)`, the encoding the runtime remembers for the last two strings. The
loops below asked for that view at every step; `LakeJs/LoopHoist.lean` now takes it
once, in front of the loop, since a string is immutable and the loop never assigns it.
-/

/-- Counting the occurrences of a character: the standard byte-position walk. -/
partial def test1 (s : String) (c : Char) : Nat :=
  let rec go (p : String.Pos.Raw) (n : Nat) : Nat :=
    if String.Pos.Raw.atEnd s p then n
    else go (String.Pos.Raw.next s p) (if String.Pos.Raw.get s p == c then n + 1 else n)
  go 0 0

/-- The same walk, answering with the position of the first occurrence. -/
partial def test2 (s : String) (c : Char) : String.Pos.Raw :=
  let rec go (p : String.Pos.Raw) : String.Pos.Raw :=
    if String.Pos.Raw.atEnd s p then p
    else if String.Pos.Raw.get s p == c then p
    else go (String.Pos.Raw.next s p)
  go 0

/-- `String.length` counts the characters of the string, so asking for it at every
    step of a loop is quadratic; the string is invariant, so it is asked once. -/
partial def test4 (s : String) : Nat :=
  let rec go (i : Nat) (acc : Nat) : Nat :=
    if i < s.length then go (i + 1) (acc + i) else acc
  go 0 0

/-- The loop assigns the string it measures, so its encoding is not the same at every
    step and nothing is hoisted. -/
def test3 (s : String) (n : Nat) : Nat := Id.run do
  let mut s := s
  let mut acc := 0
  for _ in [0:n] do
    acc := acc + s.utf8ByteSize
    s := s.push 'x'
  return acc
