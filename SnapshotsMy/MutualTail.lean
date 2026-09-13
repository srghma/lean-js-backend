/-!
Mutually tail-recursive functions: each of these calls the next in tail position, so
none of them may grow the JavaScript stack. The group is compiled into a single
function with a dispatch loop (`_mut$…`), and each member keeps a declaration of its
own that enters it with the member's tag.

`test1`/`test2` are a two-member group of one argument each; `test3`/`test4`/`test5`
are a three-member group of *different* arities, so the merged function takes as many
arguments as the widest member.
-/

mutual

partial def test1 : Nat → Bool
  | 0 => true
  | n + 1 => test2 n

partial def test2 : Nat → Bool
  | 0 => false
  | n + 1 => test1 n

end

mutual

partial def test3 (n acc : Nat) : Nat :=
  if n == 0 then acc else test4 (n - 1) (acc + 1) 2

partial def test4 (n acc k : Nat) : Nat :=
  if n == 0 then acc else test5 (n - 1) (acc + k)

partial def test5 (n acc : Nat) : Nat :=
  if n == 0 then acc else test3 (n - 1) (acc + 3)

end
