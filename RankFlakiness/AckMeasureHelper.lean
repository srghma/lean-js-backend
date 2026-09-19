-- `ack`, with the first component of the measure written through a definition that is
-- the identity.  The measure is the same measure.

def idNat (x : Nat) : Nat := x

def ackId : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ackId m 1
  | m + 1, n + 1 => ackId m (ackId (m + 1) n)
termination_by m n => (idNat m, n)
decreasing_by all_goals simp [idNat] <;> omega
