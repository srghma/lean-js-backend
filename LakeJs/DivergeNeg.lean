module

public import LakeJs.SN

@[expose] public section

/-!
# A closed term that never answers and contains **no block**

`LakeJs.Diverge` shows that a self-`Tail.label` — the loop — diverges.  This file shows
that the loop is **not** the only source of divergence: the type language admits a
recursive declaration whose `.self` occurs in the *domain* of a function type,

```
μX. { f : X → Nat, pad : Nat }
```

and at such a type the ordinary λ-calculus fragment of `Term` — `lam`, `ap`, `ctor`,
`proj` — already writes Curry's `Ω`.  The term below is closed, block-free, loop-free,
join-point-free, and it steps to itself in two steps.

The consequence for `TERMINATION_ASSESSMENT.md`: constraining the *term* language is not
enough for termination; the *type* language has to forbid a recursive occurrence in a
negative position as well.
-/

namespace LakeJs.Expr

open LakeJs

/-- `μX. { f : X → Nat, pad : Nat }`: a record with a field that takes the record
    itself.  The recursive occurrence stands in the **domain** of a function type — a
    negative occurrence, which `LakeJs.RTyWf` does not forbid. -/
def negRec : Ty := Ty.recObject ⟨.fn (.self 0) (.prim .nat), .prim .nat, []⟩

/-- The fields of its one constructor, with `.self` unfolded. -/
def negRecFields : Layout.FieldLayout := [Ty.fn negRec (.prim .nat), Ty.prim .nat]

theorem negRec_ctorFields : negRec.ctorFields? 0 = some negRecFields := rfl

theorem negRec_numCtors : negRec.numCtors? = some 1 := rfl

theorem negRec_fieldTy : negRec.fieldTy? 0 0 = some (Ty.fn negRec (.prim .nat)) := rfl

theorem negRec_ne_bool : negRec ≠ Ty.bool := fun h => Ty.noConfusion h

theorem negRecFields_get : negRecFields[0]? = some (Ty.fn negRec (.prim .nat)) := rfl

/-- `x ↦ x.f(x)`: read the function field of the argument and apply it to the argument
    itself.  This is the body of Curry's `Ω`, written with `proj` in place of the
    unfolding of a recursive type. -/
def selfApply {Sg : Sig} : Term Sg [negRec] (.prim .nat) :=
  .ap (.proj (.var .head) 0 0 negRec_numCtors negRec_fieldTy) (.var .head)

/-- `{ f := x ↦ x.f(x), pad := 0 }`: a value of the negative recursive type. -/
def omegaVal {Sg : Sig} : Term Sg [] negRec :=
  .ctor 0 negRecFields negRec_ctorFields
    (.cons (.lam selfApply) (.cons (.lit (.nat 0)) .nil))

/-- `Ω = ω.f(ω)`: a closed term of type `Nat` with no block in it. -/
def omegaTerm {Sg : Sig} : Term Sg [] (Ty.prim .nat) :=
  .ap (.proj omegaVal 0 0 negRec_numCtors negRec_fieldTy) omegaVal

/-- The intermediate term `Ω` passes through: `(x ↦ x.f(x))(ω)`. -/
def omegaRedex {Sg : Sig} : Term Sg [] (Ty.prim .nat) :=
  .ap (.lam selfApply) omegaVal

theorem omegaVal_value {Sg : Sig} : Value (omegaVal (Sg := Sg)) :=
  .ctor 0 negRecFields negRec_ctorFields negRec_ne_bool
    (.cons (.lam _) (.cons (.lit _) .nil))

theorem omega_step_redex {Sg : Sig} :
    Step (omegaTerm (Sg := Sg)) omegaRedex :=
  Step.apFun (Step.projCtor negRecFields_get)

theorem omega_redex_step {Sg : Sig} :
    Step (omegaRedex (Sg := Sg)) omegaTerm :=
  Step.beta omegaVal_value

/-- **`Ω` comes back to itself**, in two steps and without a block. -/
theorem omega_steps_self {Sg : Sig} : Steps (omegaTerm (Sg := Sg)) omegaTerm :=
  .tail (.tail .refl omega_step_redex) omega_redex_step

/-- A term that steps onto a cycle does not run out of steps. -/
theorem not_sn_of_cycle {Sg : Sig} {Γ : Ctx} {τ : Ty} {t u : Term Sg Γ τ}
    (h1 : Step t u) (h2 : Steps u t) : ¬ t.SN := by
  have key : ∀ {t : Term Sg Γ τ}, t.SN → ¬ ∃ u, Step t u ∧ Steps u t := by
    intro t hsn
    induction hsn with
    | intro t _ ih =>
        rintro ⟨u, hst, hback⟩
        rcases Steps.cases_head hback with rfl | ⟨w, hs1, hrest⟩
        · exact ih u hst ⟨u, hst, .refl⟩
        · exact ih u hst ⟨w, hs1, hrest.trans (Steps.single hst)⟩
  exact fun hsn => key hsn ⟨u, h1, h2⟩

/-- **The block-free fragment is not strongly normalising.** -/
theorem omega_not_sn {Sg : Sig} : ¬ (omegaTerm (Sg := Sg)).SN :=
  not_sn_of_cycle omega_step_redex (Steps.single omega_redex_step)

/-! ## Neither term on the cycle is an answer -/

/-- `Ω` is not an answer: it takes a step, and an answer does not. -/
theorem omega_not_value {Sg : Sig} : ¬ Value (omegaTerm (Sg := Sg)) :=
  fun hv => hv.not_step omega_step_redex

/-- Neither is the redex it passes through. -/
theorem omegaRedex_not_value {Sg : Sig} : ¬ Value (omegaRedex (Sg := Sg)) :=
  fun hv => hv.not_step omega_redex_step

end LakeJs.Expr

end
