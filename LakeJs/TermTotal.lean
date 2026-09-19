module

public import LakeJs.Fundamental

@[expose] public section

set_option autoImplicit false

/-!
# The headline theorem: the evaluator is total

`LakeJs.Reduce` defines

```lean
def Term.evalClosed {Sg : Sig} {τ : Ty} (t : Term Sg [] [] τ) (δ : GEnv Sg.decls) : τ.den
```

with no fuel argument and no `Option` in the result type, by structural recursion on the
term.  That it elaborates at all *is* the totality theorem: a closed term of the one
grammar denotes a value of its type, and the kernel computes it.

This file states that fact in the vocabulary the rest of the library uses, and then does
the first worked faithfulness proof with it: `Term.tco01`, the hand-written translation of
`SnapshotsPBOPure/Tco01.lean`, computes the Lean function it came from — at every
argument, not merely at the ones a `#eval` tries.

Why no fuel is needed, in one line per constructor family: the only constructs that
repeat work are `Term.fix`, which carries a measure and unrolls only while it descends, and
`Tail.join`, whose body is typed in the *outer* label context so that it cannot jump back
to itself.  Every other former is a finite combination of its subterms.  The four kinds of
recursive definition that Lean supports besides the structural and well-founded ones —
partial fixpoints, inductive/coinductive fixpoints, `partial`, and `unsafe` — have no
constructor to be written with.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {τ : Ty}

/-- **Totality.**  Every closed term has a value of its type, with no fuel and no failure
    case.  The witness is what the evaluator computes. -/
theorem Term.total (t : Term Sg [] [] τ) (δ : GEnv Sg.decls) :
    ∃ v : τ.den, t.evalClosed δ = v :=
  ⟨t.evalClosed δ, rfl⟩

/-- The value is unique: `Term.evalClosed` is a function, so a term has one answer. -/
theorem Term.evalClosed_det (t : Term Sg [] [] τ) (δ : GEnv Sg.decls) {v w : τ.den}
    (hv : t.evalClosed δ = v) (hw : t.evalClosed δ = w) : v = w := by
  rw [← hv, ← hw]

/-- Totality of a term of a module with no declarations, at the runner the examples
    use. -/
theorem Term.total_run (t : Term ⟨[], by decide⟩ [] [] τ) : ∃ v : τ.den, t.run = v :=
  ⟨t.run, rfl⟩

/-! ## A first faithfulness proof

`SnapshotsPBOPure/Tco01.lean` defines

```lean
def test (n : Nat) : Nat := match n with | 0 => n | n + 1 => test n
```

which is structurally recursive and answers `0` at every argument.  `Term.tco01` is its
translation, with the one-component measure `n` that the structural case produces.  Here is the proof
that the two agree — the pattern every example in `LakeJs.Examples` follows. -/

/-- The Lean function `Tco01.test` computes, as a function of an argument environment. -/
def tco01Fun (_as : Env [Ty.nat]) : Ty.nat.den := show Nat from 0

/-- The measure the structural case reads off the recursed-on argument: one component,
    the argument itself. -/
def tco01Measure (as : Env [Ty.nat]) : Lex.NatVec 1 := .cons (as.get .head) .nil

/-- **`Term.tco01` is `Tco01.test`.**  Applied to any argument, the translated term
    answers what the Lean function answers — by `Term.fix_implements_closed`, from the
    single fact that the one recursive call is at a smaller measure. -/
theorem tco01_implements (δ : GEnv Sg.decls) :
    (Term.tco01 (Sg := Sg) (Ρ := [])).Implements δ tco01Fun := by
  refine Term.fix_implements_closed _ _ _ δ tco01Fun tco01Measure ?_ ?_
  · intro as
    match as with
    | .cons n .nil => rfl
  · intro g as hg
    match as with
    | .cons n .nil =>
      cases (n : Nat) with
      | zero => rfl
      | succ k =>
        exact hg (.cons k .nil) ((Lex.NatVec.lt_one_iff _ _).mpr (Nat.lt_succ_self k))

/-- And the value at a concrete argument, computed by the kernel with no fuel. -/
example : Term.runNat1 Term.tco01 7 = 0 := rfl

end LakeJs.Expr

end
