module

public import LakeJs.DescentTactic
public import LakeJs.Examples.Descent

@[expose] public section

set_option autoImplicit false

/-!
# The verification condition, discharged by the tactic

`LakeJs.Examples.Descent` proves `Term.Descends` for the worked examples by hand, and for
four of them by `apply`ing the rules of `LakeJs.DescentVC` one at a time.  This file proves
the *same* conditions with `descent_auto`, the tactic of `LakeJs.DescentTactic`, which
assembles that derivation mechanically and closes the arithmetic it leaves.

That is the piece step 6 of `TERM_RANK_FLAKINESS_AND_ALTERNATIVES.md` §8 was missing: with
it, a **generated** program can carry its own verification condition, because the proof of
the condition no longer has to be written by a human who has read the term.

Each theorem below is the statement of the corresponding hand proof in
`LakeJs.Examples.Descent`, with the proof replaced by one line.  The shapes covered are the
ones the corpus has: a structural recursion on a number, a structural recursion over data
(whose measure is `Term.structSize` and whose obligation is about the size of a field), a
body that is a block of join points, a two-component lexicographic measure with a nested
self call (Ackermann), a merged mutual clique, and a well-founded recursion that is not
structural (`Nat.gcd`, whose obligation is `y % x < x`).
-/

namespace LakeJs.Expr.Examples

open LakeJs
open LakeJs.Ty
open LakeJs.Expr.Ops

variable {Sg : Sig}

/-- `sumTo`: structural on a number. -/
theorem sumToBody_descends_auto (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat]) (τ := Ty.nat)
      (Term.measure1 sumToMeasure) sumToBody δ .nil .nil := by
  simp only [sumToMeasure]
  descent_auto as

/-- `Nat.gcd`: well-founded, and not structural. -/
theorem gcdBody_descends_auto (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
      (Term.measure1 (♯0)) gcdBody δ .nil .nil := by
  descent_auto as

/-- Ackermann: two components, three self calls, one of them nested. -/
theorem ackBody_descends_auto (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
      (k := 2) (.cons (♯0) (.cons (♯1) .nil)) ackBody δ .nil .nil := by
  descent_auto as

/-- The merged `testEven` / `testOdd` clique: the call flips the member tag and descends on
    the shared measure. -/
theorem parityBody_descends_auto (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.bool)
      (Term.measure1 (♯1)) parityBody δ .nil .nil := by
  descent_auto as

/-- A body that is a block of join points. -/
theorem joinCountBody_descends_auto (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat]) (τ := Ty.nat) (k := 1)
      (Term.measure1 (♯0)) joinCountBody δ .nil .nil := by
  descent_auto as

/-- `sumList`: structural over data, so the measure is `Term.structSize` and the obligation
    is that the tail's runtime tree is smaller than the list's. -/
theorem sumListBody_descends_auto (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [natList]) (τ := Ty.nat)
      (Term.structMeasure (♯0)) sumListBody δ .nil .nil := by
  descent_auto as

/-! ## The tactic is not a rubber stamp

`LakeJs.Examples.Descent` proves `Term.Descends` **false** for the two recursions that
reach `stuck`: `Tco07.boom`, whose erased proof made a non-descending branch reachable, and
the recursion that calls itself at the same argument.  So the tactic had better fail on
them, and these two checks say that it does — if either ever succeeded, the tactic would be
proving something that is refuted a few hundred lines away. -/

/-- `descent_auto` fails on the erased `Tco07.boom`. -/
example : True := by
  fail_if_success
    (have : ∀ δ : GEnv Sg.decls,
        Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat]) (τ := Ty.nat)
          (k := 1) (Term.measure1 (♯0)) boomBody δ .nil .nil := by
      intro δ
      descent_auto as)
  trivial

/-- `descent_auto` fails on the recursion that calls itself at the same argument. -/
example : True := by
  fail_if_success
    (have : ∀ δ : GEnv Sg.decls,
        Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat]) (τ := Ty.nat)
          (k := 1) (.cons (♯0) .nil) spinBody δ .nil .nil := by
      intro δ
      descent_auto as)
  trivial

end LakeJs.Expr.Examples

end
