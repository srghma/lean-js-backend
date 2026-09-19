module

public import LakeJs.Subst

@[expose] public section

/-!
# Currying a block, and uncurrying a function

Two binders of this language bind a **list** of variables at once — `Tail.join`, the join
point, and `Term.fix`, the recursion — and each extends the context by `ps ++ Γ`, so
inside it de Bruijn index `0` is the **first** argument.  A curried `ƛ`-chain binds the same parameters one
at a time, so inside `ƛ ƛ …` index `0` is the **last** one written.  The two orders are
opposite, and a pass that converts between them — uncurrying a chain into a label,
contifying a `let`-bound function into a label, eta-expanding a label back into a chain — has to reverse the list.

**That reversal is the dangerous kind of mistake**: if two adjacent parameters have the
same type, forgetting it leaves a term that is still well-typed and means something else.
Lean will not catch it and a review will not catch it.  So the conversion is written
**once**, here, with the round-trip proved, and passes are meant to use it rather than
reverse a list by hand:

* `VRen.insertParams` / `VRen.extractParams` are the two renamings that move one variable
  past a list of them, and `VRen.extractParams_insertParams` /
  `VRen.insertParams_extractParams` say they are inverse;
* `Term.curryParams` turns a block that binds `σs ++ Γ` into a curried function of type
  `Ty.arrows σs τ`, and `Term.uncurryParams` turns such a function back into a block;
* the examples at the end pin the direction down by computation: they are `rfl`, and two
  of them use a type where *every* parameter has the same type, which is exactly the case
  a mistake would survive.

A `Term` holds no labels at all, so nothing further has to be said about jumps: a body
turned into a function is jump-free by construction.  The recursion context is carried
through untouched — currying moves variables, and a self-reference is not one.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

/-! ## Moving one variable past a list of them -/

/-- Read a context `σ :: σs ++ Γ` — one variable bound *innermost*, in front of a list of
    them — as the context `σs ++ σ :: Γ`, where the same variable is bound *outermost* of
    the list.  This is the whole content of the direction change. -/
def VRen.insertParams {Γ : Ctx} {σ : Ty} (σs : List Ty) :
    VRen (σ :: σs ++ Γ) (σs ++ σ :: Γ) :=
  fun {_} v =>
    match v with
    | .head => VRen.weakenList σs .head
    | .tail v => VRen.liftList σs VRen.weaken v

/-- The other direction: `σs ++ σ :: Γ` read as `σ :: σs ++ Γ`. -/
def VRen.extractParams {Γ : Ctx} {σ : Ty} :
    ∀ (σs : List Ty) {τ : Ty}, σs ++ σ :: Γ ∋ τ → σ :: σs ++ Γ ∋ τ
  | [], _, v => v
  | _ :: _, _, .head => .tail .head
  | _ :: σs, _, .tail v => VRen.lift VRen.weaken (VRen.extractParams σs v)

/-- Extracting the variable a weakening put at the end of the list gives it back. -/
theorem VRen.extractParams_weakenList {Γ : Ctx} {σ : Ty} (σs : List Ty) :
    VRen.extractParams (Γ := Γ) (σ := σ) σs (VRen.weakenList σs (.head : σ :: Γ ∋ σ))
      = .head := by
  induction σs with
  | nil => rfl
  | cons a σs ih =>
      show VRen.extractParams (a :: σs) (Var.tail (VRen.weakenList σs .head)) = _
      rw [VRen.extractParams, ih]
      rfl

/-- Extracting a variable that was only weakened past the list leaves it where it was. -/
theorem VRen.extractParams_liftList_weaken {Γ : Ctx} {σ : Ty} :
    ∀ (σs : List Ty) {τ : Ty} (v : σs ++ Γ ∋ τ),
      VRen.extractParams (σ := σ) σs (VRen.liftList σs (VRen.weaken (σ := σ)) v)
        = .tail v
  | [], _, v => rfl
  | a :: σs, _, v => by
      cases v with
      | head => rfl
      | tail v =>
          show VRen.extractParams (a :: σs)
            (Var.tail (VRen.liftList σs (VRen.weaken (σ := σ)) v)) = _
          rw [VRen.extractParams, VRen.extractParams_liftList_weaken σs v]
          rfl

/-- **The two directions are inverse.**  A pass that curries a block and uncurries the
    result again has moved no parameter. -/
theorem VRen.extractParams_insertParams {Γ : Ctx} {σ : Ty} (σs : List Ty) :
    ∀ {τ : Ty} (v : σ :: σs ++ Γ ∋ τ),
      VRen.extractParams σs (VRen.insertParams σs v) = v := by
  intro τ v
  cases v with
  | head => exact VRen.extractParams_weakenList σs
  | tail v => exact VRen.extractParams_liftList_weaken σs v

/-- Inserting past a longer list is inserting past the shorter one, one variable
    further out. -/
theorem VRen.insertParams_lift_weaken {Γ : Ctx} {σ a : Ty} (σs : List Ty) {τ : Ty}
    (x : σ :: σs ++ Γ ∋ τ) :
    VRen.insertParams (σ := σ) (a :: σs) (VRen.lift (VRen.weaken (σ := a)) x)
      = .tail (VRen.insertParams σs x) := by
  cases x with
  | head => rfl
  | tail y => rfl

/-- …and the round trip the other way round. -/
theorem VRen.insertParams_extractParams {Γ : Ctx} {σ : Ty} :
    ∀ (σs : List Ty) {τ : Ty} (v : σs ++ σ :: Γ ∋ τ),
      VRen.insertParams σs (VRen.extractParams σs v) = v
  | [], _, v => by
      cases v with
      | head => rfl
      | tail y => rfl
  | a :: σs, _, v => by
      cases v with
      | head => rfl
      | tail w =>
          rw [VRen.extractParams, VRen.insertParams_lift_weaken,
            VRen.insertParams_extractParams σs w]

/-! ## Currying -/

/-- **A block, as a curried function.**  `curryParams σs b` is `fun x₁ … xₙ => b`, where
    `b` binds `σs ++ Γ` — its de Bruijn index `0` being the *first* parameter — and the
    chain binds them in the order they are written. -/
def Term.curryParams {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {τ : Ty} :
    (σs : List Ty) → Term Sg (σs ++ Γ) Ρ τ → Term Sg Γ Ρ (Ty.arrows σs τ)
  | [], b => b
  | _ :: σs, b =>
      .lam (Term.curryParams σs (b.rename (VRen.insertParams σs) RRen.id))

/-- **A curried function, as a block**: `f x₁ … xₙ`, in the context the parameters extend,
    with index `0` the first parameter — the inverse reading of `Term.curryParams`. -/
def Term.uncurryParams {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {τ : Ty} (σs : List Ty)
    (f : Term Sg Γ Ρ (Ty.arrows σs τ)) : Term Sg (σs ++ Γ) Ρ τ :=
  Term.appSpine (f.rename (VRen.weakenList σs) RRen.id) (Spine.vars σs)

/-! ## What the direction actually is

These are `rfl`, so they are checked whenever the module is built, and they are the
guard against the silent inversion: in each of them every parameter has the **same
type**, which is the case a reversed list would survive. -/

section Examples

/-- The empty signature. -/
private def sigNone : Sig := ⟨[], rfl⟩

/-- The **first** parameter of a block is index `0` of the block, and the **outermost**
    binder of the chain — which is index `1` inside a chain of two. -/
example :
    Term.curryParams (Sg := sigNone) (Γ := []) (Ρ := []) (τ := Ty.nat) [Ty.nat, Ty.nat]
        (♯0)
      = ƛ (ƛ (♯1)) := rfl

/-- The **second** parameter is index `1` of the block and the innermost binder. -/
example :
    Term.curryParams (Sg := sigNone) (Γ := []) (Ρ := []) (τ := Ty.nat) [Ty.nat, Ty.nat]
        (♯1)
      = ƛ (ƛ (♯0)) := rfl

/-- Three parameters, all of the same type: `fun x y z => x` is the block that reads its
    first parameter. -/
example :
    Term.curryParams (Sg := sigNone) (Γ := []) (Ρ := []) (τ := Ty.nat)
        [Ty.nat, Ty.nat, Ty.nat] (♯0)
      = ƛ (ƛ (ƛ (♯2))) := rfl

/-- A block that reads a variable of the **enclosing** context keeps reading it. -/
example :
    Term.curryParams (Sg := sigNone) (Γ := [Ty.bool]) (Ρ := []) (τ := Ty.bool)
        [Ty.nat, Ty.nat] (♯2)
      = ƛ (ƛ (♯2)) := rfl

/-- Uncurrying a chain reads its parameters in the block's order: the *first* parameter
    is index `0` of the block, and it is the argument the function takes first. -/
example :
    Term.uncurryParams (Sg := sigNone) (Γ := []) (Ρ := []) (τ := Ty.nat) [Ty.nat, Ty.nat]
        (ƛ (ƛ (♯1)))
      = (ƛ (ƛ (♯1))) ⬝ (♯0) ⬝ (♯1) := rfl

/-- The two conversions are inverse on the renaming that carries them, at a list whose
    entries all have the same type — which is the case a reversed list would survive. -/
example (v : (Ty.nat :: [Ty.nat] ++ ([] : Ctx)) ∋ Ty.nat) :
    VRen.extractParams (Γ := []) (σ := Ty.nat) [Ty.nat] (VRen.insertParams [Ty.nat] v)
      = v :=
  VRen.extractParams_insertParams [Ty.nat] v

/-- …and the other way round. -/
example (v : ([Ty.nat] ++ Ty.nat :: ([] : Ctx)) ∋ Ty.nat) :
    VRen.insertParams (Γ := []) (σ := Ty.nat) [Ty.nat] (VRen.extractParams [Ty.nat] v)
      = v :=
  VRen.insertParams_extractParams [Ty.nat] v

end Examples

end LakeJs.Expr

end
