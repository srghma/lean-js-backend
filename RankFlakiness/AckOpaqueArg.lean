-- `ack`, with the *unchanged* first argument of the inner recursive call written
-- `2 * (m + 1) - (m + 1)` instead of `m + 1`.  That is the same number, the function is
-- the same function, and Lean accepts the same lexicographic `termination_by`.

def ackOpaque : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ackOpaque m 1
  | m + 1, n + 1 => ackOpaque m (ackOpaque (2 * (m + 1) - (m + 1)) n)
termination_by m n => (m, n)
decreasing_by all_goals omega
