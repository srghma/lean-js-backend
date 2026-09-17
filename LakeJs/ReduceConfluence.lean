import LakeJs.Reduce

/-!
# `Step` is not confluent

`LakeJs/Reduce.lean` writes the optimiser down as a relation so that questions about it
can be *asked*; `LakeJs/ReduceCycle.lean` answers the first of them (the relation does
not terminate).  This file answers the one the plan names: **is the optimiser
Church-Rosser?**  It is not, and the reason is neither exotic nor a defect of any single
rule.

Take a declaration the inliner may unfold, say `@[inline] def add2 a b := a + b`, and a
wrapper that does nothing but call it:

```
fun (x0, x1) => add2(x0, x1)
```

Two rules apply to that term, and both of them are right:

* **eta** sees a lambda whose body applies a context-independent head to its own
  parameters in order, and contracts it to the head: the term becomes `add2`;
* **delta** (the inliner) sees a saturated call of a declaration of the table and puts
  the callee's body in its place: the term becomes `fun (x0, x1) => x0 + x1`, which
  *eta* then contracts to the extern `lean_nat_add`.

So the same term rewrites to `add2` and to `lean_nat_add`, and both of those are normal
forms: nothing rewrites a reference to a declaration whose body is not a literal, and
nothing rewrites an extern.  They are different terms, so they have no common reduct and
the relation is not confluent — not even *locally*: the two rewrites above are one step
each from the same term.

What this means for the backend is worth saying, since it is not a bug: the two normal
forms are the same function, and the emitted module is correct whichever of them it
prints.  What fails is the stronger property that the answer does not depend on the order
the rules are applied in — which is why the backend fixes an order (the inliner, then the
bottom-up sweep of `LakeJs.Simp`) rather than chasing the relation to a normal form.

## Inverting a step

Every inversion here goes through `Step.inv`.  One cannot case on `Step tbl t u` with a
`t` of a *concrete* type: `Term.callProd` is indexed by `(r1 :: rs).get i`, which is
stuck, so the elaborator cannot decide whether that index unifies with the concrete one.
`stepInv` therefore reads off, by a match on the *shape* of `t`, what a rewrite of a term
of that shape can be; `Step.inv` proves it once, by cases on the rewrite with `t` a
variable, and each fact below is an instance of it.
-/

namespace LakeJs.ReduceConfluence

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename
open LakeJs.Reduce

/-! ## Confluence, stated -/

/-- A relation is **locally confluent** (weakly Church-Rosser) when any two single
    rewrites of one term can be brought back together. -/
def LocallyConfluent {α : Sort u} (R : α → α → Prop) : Prop :=
  ∀ a b c : α, R a b → R a c → ∃ d, Chain R b d ∧ Chain R c d

/-- A relation is **confluent** (Church-Rosser) when any two reductions of one term can
    be brought back together. -/
def Confluent {α : Sort u} (R : α → α → Prop) : Prop :=
  ∀ a b c : α, Chain R a b → Chain R a c → ∃ d, Chain R b d ∧ Chain R c d

/-- Confluence implies local confluence: one rewrite is a reduction. -/
theorem LocallyConfluent.of_confluent {α : Sort u} {R : α → α → Prop}
    (h : Confluent R) : LocallyConfluent R :=
  fun a b c hb hc => h a b c (.single hb) (.single hc)

/-! ## Inverting one rewrite -/

/-- Is the head of an application a reference to a top-level declaration?  This is the
    side condition of the rule `delta`, and the only thing `stepInv` needs to know about
    the head of an application. -/
def isGlobalHead {Sg : Sig} {Γ : Ctx} {ρ : Ty} : Term Sg Γ ρ → Bool
  | .global _ => true
  | _ => false

/-- What one rewrite of a term of a given *shape* can be.  Only the four shapes this
    file reasons about are spelled out; every other shape says nothing (`True`). -/
def stepInv {Sg : Sig} (tbl : Inline.Table Sg) : {Γ : Ctx} → {ρ : Ty} →
    Term Sg Γ ρ → Term Sg Γ ρ → Prop
  | _, _, .var _, _ => False
  | _, _, .lit _, _ => False
  | _, _, .extern _, _ => False
  | _, _, .global r, u => Inline.litGlobal? tbl r = some u
  | _, _, .lamN (params := ps) b, u =>
      Simp.etaTarget? (ps := ps) b = some u ∨ ∃ b', Step tbl b b' ∧ u = .lamN b'
  | _, _, .apN f args, u =>
      isGlobalHead f = true ∨ (∃ f', Step tbl f f' ∧ u = .apN f' args) ∨
        ∃ args', SpineStep tbl args args' ∧ u = .apN f args'
  | _, _, _, _ => True

/-- **The inversion principle.**  A rewrite of a term is one of the rewrites its shape
    admits. -/
theorem Step.inv {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {ρ : Ty} {t u : Term Sg Γ ρ}
    (h : Step tbl t u) : stepInv tbl t u := by
  cases h with
  | deltaLit ht => exact ht
  | delta _ => exact Or.inl rfl
  | eta ht => exact Or.inl ht
  | lamBody hs => exact Or.inr ⟨_, hs, rfl⟩
  | apFun hs => exact Or.inr (Or.inl ⟨_, hs, rfl⟩)
  | apArgs hs => exact Or.inr (Or.inr ⟨_, hs, rfl⟩)
  | _ => trivial

/-- Nothing rewrites a variable. -/
theorem no_step_var {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty} {v : Var Γ τ}
    {u : Term Sg Γ τ} : ¬ Step tbl (.var v) u :=
  fun h => Step.inv h

/-- Nothing rewrites an extern: it is a name of the runtime, not a redex. -/
theorem no_step_extern {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σs : List Ty}
    {τ : Ty} {e : Externs σs τ} {u : Term Sg Γ (.fn σs τ)} :
    ¬ Step tbl (.extern e) u :=
  fun h => Step.inv h

/-- Nothing rewrites a reference to a declaration whose body is not a literal: the only
    rule with a reference on the left is `deltaLit`. -/
theorem no_step_global {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty}
    {r : GlobalRef Sg τ} (hr : Inline.litGlobal? (Γ := Γ) tbl r = none)
    {u : Term Sg Γ τ} : ¬ Step tbl (.global r) u := by
  intro h
  have h' : Inline.litGlobal? (Γ := Γ) tbl r = some u := Step.inv h
  rw [hr] at h'
  exact absurd h' (by simp)

/-! ## The example -/

/-- The signature of the example: one declaration, `add2`, of two `Nat`s. -/
abbrev cfSig : Sig := [{ name := "add2", ty := .fn [Ty.nat, Ty.nat] Ty.nat }]

/-- The reference to `add2`. -/
def cfRef : GlobalRef cfSig (.fn [Ty.nat, Ty.nat] Ty.nat) := .here

/-- `add2`'s body: `fun (x0, x1) => x0 + x1`. -/
def cfAddBody : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat) :=
  .lamN (params := [Ty.nat, Ty.nat])
    (.apN (.extern .lean_nat_add) (.cons (♯1) (.cons (♯0) .nil)))

/-- The table the rules `delta` and `deltaLit` read: `add2` is inlinable. -/
def cfTbl : Inline.Table cfSig := [("add2", ⟨.fn [Ty.nat, Ty.nat] Ty.nat, cfAddBody⟩)]

/-- The two parameters of the enclosing lambda, in order. -/
def cfSpine : Spine cfSig [Ty.nat, Ty.nat] [Ty.nat, Ty.nat] :=
  .cons (♯1) (.cons (♯0) .nil)

/-- The term the example starts from: `fun (x0, x1) => add2(x0, x1)`. -/
def cfCall : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat) :=
  .lamN (params := [Ty.nat, Ty.nat]) (.apN (.global cfRef) cfSpine)

/-- The wrapper once the inliner has put `add2`'s body in its place:
    `fun (x0, x1) => x0 + x1`. -/
def cfInlined : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat) :=
  .lamN (params := [Ty.nat, Ty.nat]) (.apN (.extern .lean_nat_add) cfSpine)

/-! ## The two rewrites -/

/-- **Eta.**  The wrapper is the declaration it wraps. -/
theorem cfCall_step_global : Step cfTbl cfCall (.global cfRef) :=
  .eta (by with_unfolding_all rfl)

/-- **Delta.**  The call of the inlinable declaration is that declaration's body. -/
theorem cfCall_step_inlined : Step cfTbl cfCall cfInlined :=
  .lamBody (.delta (by with_unfolding_all rfl))

/-- And the inlined wrapper is, by eta again, the extern itself. -/
theorem cfInlined_step_extern :
    Step cfTbl cfInlined (.extern (Sg := cfSig) (Γ := []) .lean_nat_add) :=
  .eta (by with_unfolding_all rfl)

/-! ## Both results are normal forms -/

/-- `add2`'s body is not a literal, so `deltaLit` does not fire on a reference to it. -/
theorem cfRef_not_lit : Inline.litGlobal? (Γ := []) cfTbl cfRef = none := by
  with_unfolding_all rfl

/-- The reference to `add2` is a normal form. -/
theorem no_step_cfRef {u : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat)} :
    ¬ Step cfTbl (.global cfRef) u :=
  no_step_global cfRef_not_lit

/-- Nothing rewrites the two parameters of the wrapper, they being variables. -/
theorem no_spineStep_cfSpine {s : Spine cfSig [Ty.nat, Ty.nat] [Ty.nat, Ty.nat]} :
    ¬ SpineStep cfTbl cfSpine s := by
  intro h
  cases h with
  | head hs => exact no_step_var hs
  | tail hs =>
      cases hs with
      | head hs => exact no_step_var hs
      | tail hs => cases hs

/-- The body of the inlined wrapper — the extern applied to the two parameters — is a
    normal form. -/
theorem no_step_cfInlinedBody {u : Term cfSig [Ty.nat, Ty.nat] Ty.nat} :
    ¬ Step cfTbl (.apN (.extern .lean_nat_add) cfSpine) u := by
  intro h
  rcases Step.inv h with hg | ⟨_, hs, _⟩ | ⟨_, hs, _⟩
  · exact Bool.noConfusion hg
  · exact no_step_extern hs
  · exact no_spineStep_cfSpine hs

/-- The eta-contraction of the inlined wrapper is the extern. -/
theorem cfInlined_eta :
    Simp.etaTarget? (ps := [Ty.nat, Ty.nat]) (Sg := cfSig) (Γ := [])
        (.apN (.extern .lean_nat_add) cfSpine)
      = some (.extern .lean_nat_add) := by
  with_unfolding_all rfl

/-- The inlined wrapper has exactly one reduct: the extern. -/
theorem cfInlined_step_eq {u : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat)}
    (h : Step cfTbl cfInlined u) : u = .extern .lean_nat_add := by
  rcases Step.inv h with ht | ⟨_, hs, _⟩
  · rw [cfInlined_eta] at ht
    exact (Option.some.inj ht).symm
  · exact absurd hs no_step_cfInlinedBody

/-- So everything the inlined wrapper reduces to is itself or the extern. -/
theorem cfInlined_chain {u : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat)}
    (h : cfInlined —↠[cfTbl] u) : u = cfInlined ∨ u = .extern .lean_nat_add := by
  cases h with
  | refl => exact Or.inl rfl
  | head hs hrest =>
      have hb := cfInlined_step_eq hs
      subst hb
      cases hrest with
      | refl => exact Or.inr rfl
      | head hs' _ => exact absurd hs' no_step_extern

/-- And everything the reference reduces to is the reference. -/
theorem cfRef_chain {u : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat)}
    (h : (Term.global cfRef) —↠[cfTbl] u) : u = .global cfRef := by
  cases h with
  | refl => rfl
  | head hs _ => exact absurd hs no_step_cfRef

/-! ## The two rewrites do not join -/

/-- **The critical pair does not join.**  `cfCall` rewrites in one step to the reference
    and in one step to the inlined wrapper, and those two have no common reduct. -/
theorem cfCall_not_joinable :
    ¬ ∃ d, ((Term.global cfRef : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat))
        —↠[cfTbl] d) ∧ (cfInlined —↠[cfTbl] d) := by
  rintro ⟨d, hd₁, hd₂⟩
  have hd : d = .global cfRef := cfRef_chain hd₁
  subst hd
  rcases cfInlined_chain hd₂ with h | h
  · exact absurd (congrArg isGlobalHead h) (by with_unfolding_all decide)
  · exact absurd (congrArg isGlobalHead h) (by with_unfolding_all decide)

/-- **`Step` is not locally confluent.**  Contracting the wrapper and inlining the call
    it wraps are both single rewrites of `cfCall`, and they cannot be brought back
    together. -/
theorem step_not_locallyConfluent :
    ¬ LocallyConfluent (fun a b : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat) =>
        Step cfTbl a b) :=
  fun h => cfCall_not_joinable (h cfCall _ _ cfCall_step_global cfCall_step_inlined)

/-- **`Step` is not confluent**: the optimiser is not Church-Rosser, and the term it ends
    at depends on the order its rules are applied in. -/
theorem step_not_confluent :
    ¬ Confluent (fun a b : Term cfSig [] (.fn [Ty.nat, Ty.nat] Ty.nat) =>
        Step cfTbl a b) :=
  fun h => step_not_locallyConfluent (LocallyConfluent.of_confluent h)

/-- The same statement, quantified over the signature, the table, the context and the
    type: some instance of the relation is not confluent. -/
theorem exists_not_confluent :
    ∃ (Sg : Sig) (tbl : Inline.Table Sg) (Γ : Ctx) (τ : Ty),
      ¬ Confluent (fun a b : Term Sg Γ τ => Step tbl a b) :=
  ⟨cfSig, cfTbl, [], .fn [Ty.nat, Ty.nat] Ty.nat, step_not_confluent⟩

end LakeJs.ReduceConfluence
