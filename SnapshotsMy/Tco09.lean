-- Four well-founded recursions whose measures are *not* one argument going down.
--
-- * `diagonal`   — lexicographic `(m + n, m)`: the first component is a sum of two
--                  arguments, so no single parameter decreases.
-- * `hyper`      — lexicographic `(n, b)` with a *nested* recursive call in the second
--                  argument of the outer call.
-- * `ackRev`     — Ackermann with the arguments swapped, so the lexicographic order
--                  `(m, n)` mentions the *second* parameter first.
-- * `Mc91`       — McCarthy's 91 function: the measure `101 - n` is a subtraction that
--                  goes *up* in the argument, and the recursion is nested through a
--                  subtype carrying the proof that makes the measure decrease.
--
-- `Mc91` is written with `where`, so the recursion actually lives in the auxiliary
-- declaration `Mc91.M`, whose result type is a `Subtype`.
--
-- Note: the original request wrote `import Mathlib` at the top of this file.  This
-- package does not depend on Mathlib, and none of the four definitions needs it:
-- `omega`, `calc`, `Subtype` and `termination_by`/`decreasing_by` are all core Lean.
-- The file is therefore kept import-free so that it builds in this tree.

def diagonal : Nat → Nat → Nat
  | 0,     0     => 0
  | 0,     n + 1 => diagonal n 0 + 1
  | m + 1, n     => diagonal m (n + 1) + 1
termination_by m n => (m + n, m)
decreasing_by all_goals omega

def hyper : Nat → Nat → Nat → Nat
  | 0,     _, b     => b + 1
  | 1,     a, 0     => a
  | 2,     _, 0     => 0
  | _ + 3, _, 0     => 1
  | n + 1, a, b + 1 => hyper n a (hyper (n + 1) a b)
termination_by n _ b => (n, b)
decreasing_by all_goals omega

def ackRev : Nat → Nat → Nat
  | n,     0     => n + 1
  | 0,     m + 1 => ackRev 1 m
  | n + 1, m + 1 => ackRev (ackRev n (m + 1)) m
termination_by n m => (m, n)
decreasing_by all_goals omega

def Mc91 (n : Nat) : Nat :=
  (M n).val
where
  M (n : Nat) : { m : Nat // m ≥ n - 10 } :=
    if h : n > 100 then
      ⟨n - 10, by omega⟩
    else
      have : n + 11 - 10 ≤ M (n + 11) := (M (n + 11)).property
      have lem : n - 10 ≤ M (M (n + 11)) := calc
        _ ≤ (n + 11) - 10 - 10 := by omega
        _ ≤ (M (n + 11)) - 10 := by omega
        _ ≤ M (M (n + 11)) := (M (M (n + 11)).val).property

      ⟨M (M (n + 11)), lem⟩
  termination_by 101 - n
