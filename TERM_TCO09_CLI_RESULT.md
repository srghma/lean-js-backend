# `SnapshotsMy/Tco09.lean`: yes, the backend emits its `Program.lean`

```
$ lake build SnapshotsMy.Tco09
$ lake env ./.lake/build/bin/lean-to-js-backend SnapshotsMy/Tco09.lean
SnapshotsMy/Tco09.lean -> SnapshotsMy/Tco09Program.lean (5 declarations, checked)
```

All five declarations of the module — `diagonal`, `hyper`, `ackRev`, `Mc91` and the
auxiliary `Mc91.M` the `where` clause creates — translate into terms of the one grammar
of `LakeJs/Expr.lean`, and the generated file elaborates (`checked`) and builds as the
module `SnapshotsMy.Tco09Program`.

Two remarks on the file as it was requested.

* `import Mathlib` was dropped: this package does not depend on Mathlib, and none of the
  four definitions needs it — `omega`, `calc`, `Subtype`, `termination_by` and
  `decreasing_by` are all core Lean.  The definitions are otherwise verbatim.
* `termination_by m n => (m + n, m)` is written exactly as in the request.

## What each function became

| function | measure | what the front end emitted |
| :-- | :-- | :-- |
| `diagonal` | `(m + n, m)` | two ranked `fix`es, ranked `m + n + 1` and `m + 1`, **each taking a copy of both parameters** |
| `hyper` | `(n, b)` | two ranked `fix`es, curried: the outer takes `n` and is ranked `n + 1`, the inner takes `a, b` and is ranked `b + 1` |
| `ackRev` | `(m, n)` | two ranked `fix`es, ranked `m + 1` and `n + 1`, each taking a copy of both parameters |
| `Mc91.M` | `101 - n` | one ranked `fix`, ranked `101 - n + 1`; the nested call `M (M (n + 11))` is two self calls of it |
| `Mc91` | — | not recursive: `@Mc91.M ⬝ n` |

## The two changes to the front end this needed

Before this run the command refused three of the five:

```
`ackRev`   was not translated: the termination measure does not partition the parameters
`diagonal` was not translated: the termination measure does not partition the parameters
`Mc91`     was not translated: function expected  lcErased val
`Mc91.M`   was not translated: function expected  lcErased val
```

### 1. A lexicographic measure that does not partition the parameters

The nest of ranked recursions used to be **curried**: component `i` of the measure owned
the parameters it was the last to mention, level `i` bound exactly those, and the levels
inside it bound the rest.  That is right for Ackermann (`(m, n)`: the outer level owns
`m`, the inner owns `n`) and for `hyper` (`(n, b)`), and it is still what the front end
does whenever it applies — every previously generated `…Program.lean` in the tree
regenerates byte for byte.

It cannot describe `diagonal`.  There the inner recursion — the call `diagonal m (n + 1)`
from `m + 1, n`, which keeps `m + n` fixed and decreases `m` — changes *both* parameters,
one of which the outer component mentions.  So there is no partition: the outer level
cannot own `m` (the inner recursion changes it) and cannot not own it (its rank is
computed from it).  `ackRev` fails for the same reason with the order reversed.

The front end now falls back to a second shape when the partition fails: **every level
takes a copy of every parameter**, and the body of a level is the level inside it applied
to the copies the level is running at.

```
fix (m@lvl0 n@lvl0) rank { (m@lvl0 + n@lvl0) + 1 } body {
  (fix (m@lvl1 n@lvl1) rank { m@lvl1 + 1 } body { … } exhausted { 0 }) ⬝ m@lvl0 ⬝ n@lvl0
} exhausted { 0 }
```

A self call of level `i` supplies all the parameters, and entering an outer level re-runs
its body, which re-enters the inner `fix` and so recomputes the inner rank from the new
arguments.  That is exactly what "lexicographic" means, and nothing about the grammar or
its metatheory changes: the only recursion is still `Term.fix`, which is `Nat.rec` on its
rank, so the term is terminating by construction.

Which level a self call belongs to is decided by a small linear normal form
(`LakeJs.FrontEnd.linOf?`, `levelDelta`): the outermost component the call does not
*provably* leave unchanged.  For `diagonal m (n + 1)` from `m + 1, n` the first component
goes from `(m + 1) + n` to `m + (n + 1)` — difference `0` — so the call is an inner one;
for `diagonal n 0` from `0, n + 1` the difference is not a constant, so it is an outer
one.

### 2. `Subtype`, which LCNF erases to `Subtype lcErased`

`Mc91` is written with a `where` clause whose auxiliary function returns
`{ m : Nat // m ≥ n - 10 }` — the proof is what makes the measure `101 - n` decrease at
the nested call.  The proof is erased before LCNF exists, and with it the `Nat`: LCNF
records the result type as `Subtype lcErased` and the body as
`@Subtype.mk _ ◾ x ◾` / `x # 0`.

The front end now treats a `Subtype` as transparent — building one is the identity on its
value and reading its first field is the identity — and, when the LCNF result type has
been erased that way, reads the result type off the **Lean** type of the declaration
instead.  So `Mc91.M` comes out as an ordinary `(fn nat nat)`.

## The emitted terms compute the same functions

`SnapshotsMy/Tco09Check.lean` runs the emitted terms — no fuel argument, the rank is part
of the term — against the Lean declarations they were translated from:

| theorem | what it checks |
| :-- | :-- |
| `ackRev_agrees` | `ackRev n m` for `n, m < 4` |
| `diagonal_agrees` | `diagonal m n` for `m, n < 8` |
| `hyper_agrees` | `hyper n a b` for `n < 4`, `a, b < 3` |
| `Mc91_agrees` | `Mc91 n` for `n < 130` |
| `Mc91_is_91` | the emitted `Mc91` answers `91` for every `n ≤ 100` |

These are finite checks discharged by `native_decide`; they say the rank the front end
chose is enough (the recursion is not cut short by an exhausted rank) and that the
translation preserves the function.  They are checks by evaluation, not a general
equivalence proof — the general theorem, for a hand-written term of the Ackermann shape,
is `ackTerm_eq` in `LakeJs/Examples/Ackermann.lean`.

## Regression

Every `…Program.lean` already in `SnapshotsMy/` and `SnapshotsPBOPure/` was regenerated
with the new front end and is unchanged, and `SnapshotsPBOPartial/` is still refused by
the totality gate (`partial def`, `IO`).
