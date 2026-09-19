module

public import LakeJs.TerminatingSubst

@[expose] public section

set_option autoImplicit false

/-!
# The shape of a block

The old grammar's label former carried a flag, `Tail.label (self : Bool) …`: with
`self = false` it bound a join point, with `self = true` a loop.  A loop could repeat work
without bound, so this module had to carve out the shapes on which a certificate could be
produced — `Tail.Flat` (no label at all) and `Tail.LoopFree` (no `self` label) — and prove
that a compiler pass preserved them.

**`Tail.LoopFree` has no content any more.**  The one label former of the grammar is

```lean
| join : ∀ {Γ Ω Ρ τ}, (ps : List Ty) → Tail Sg (ps ++ Γ) Ω Ρ τ →
    Tail Sg Γ (ps :: Ω) Ρ τ → Tail Sg Γ Ω Ρ τ
```

whose **body is typed in the outer label context `Ω`**.  The label being bound is in scope
only in `rest`, so the body cannot jump back to it: there is no `LVar` for it to use.
Every block is loop-free by construction, which is why the certificate generator is gone.

What is left worth saying about shapes is this file:

* `Tail.Flat` — no label at all: no jump and no join.  A flat block is straight-line code
  with branches, and `Tail.eval_flat_lenv_irrel` says its value does not depend on the
  join points in scope at all.
* `Tail.eval_lenv_closed` — a block opened at the empty label context, which is what
  `Term.block` does, likewise has a value that depends only on the value, global and
  recursion environments: there is nothing else for it to depend on.
* `Tail.flat_rename` — flatness survives renaming, so a pass may rename freely.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Flat blocks -/

mutual

/-- **A block with no label in it**: no jump, and no join point.  Straight-line code with
    branches. -/
def Tail.Flat {Sg : Sig} : ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty},
    Tail Sg Γ Ω Ρ τ → Prop
  | _, _, _, _, .ret _ => True
  | _, _, _, _, .jmp _ _ => False
  | _, _, _, _, .letT _ b => b.Flat
  | _, _, _, _, .iteT _ t e => t.Flat ∧ e.Flat
  | _, _, _, _, .caseT _ alts _ => alts.Flat
  | _, _, _, _, .join _ _ _ => False

/-- `Tail.Flat`, on the branches of a dispatch inside a block. -/
def AltsT.Flat {Sg : Sig} :
    ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool},
      AltsT Sg Γ Ω Ρ σ τ tags full → Prop
  | _, _, _, _, _, _, _, .deflt b => b.Flat
  | _, _, _, _, _, _, _, .nilFull => True
  | _, _, _, _, _, _, _, .cons _ _ _ b rest => b.Flat ∧ rest.Flat

end

/-! ## A flat block ignores the join points in scope -/

mutual

/-- **The value of a flat block does not depend on the join points in scope.**  It has no
    jump, so there is nothing for it to read them with. -/
theorem Tail.eval_flat_lenv_irrel {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty}
    (b : Tail Sg Γ Ω Ρ τ) (h : b.Flat) (δ : GEnv Sg.decls) (γ : Env Γ)
    (l₁ l₂ : LEnv τ Ω) (ρ : REnv Ρ) :
    b.eval δ γ l₁ ρ = b.eval δ γ l₂ ρ :=
  match b, h with
  | .ret _, _ => rfl
  | .jmp _ _, h => absurd h (by simp [Tail.Flat])
  | .letT e rest, h =>
      Tail.eval_flat_lenv_irrel rest h δ (.cons (e.eval δ γ ρ) γ) l₁ l₂ ρ
  | .iteT c t e, h => by
      show (if cond (c.eval δ γ ρ) true false then t.eval δ γ l₁ ρ else e.eval δ γ l₁ ρ)
          = if cond (c.eval δ γ ρ) true false then t.eval δ γ l₂ ρ else e.eval δ γ l₂ ρ
      rw [Tail.eval_flat_lenv_irrel t h.1 δ γ l₁ l₂ ρ,
        Tail.eval_flat_lenv_irrel e h.2 δ γ l₁ l₂ ρ]
  | .caseT (σ := σ) scrut alts _, h => by
      show (match alts.eval (σ.tagOfVal (scrut.eval δ γ ρ))
              (σ.fieldsOfVal (scrut.eval δ γ ρ)) δ γ l₁ ρ with
            | some r => r | none => τ.dflt)
          = (match alts.eval (σ.tagOfVal (scrut.eval δ γ ρ))
              (σ.fieldsOfVal (scrut.eval δ γ ρ)) δ γ l₂ ρ with
            | some r => r | none => τ.dflt)
      rw [AltsT.eval_flat_lenv_irrel alts h (σ.tagOfVal (scrut.eval δ γ ρ))
        (σ.fieldsOfVal (scrut.eval δ γ ρ)) δ γ l₁ l₂ ρ]
  | .join _ _ _, h => absurd h (by simp [Tail.Flat])
  termination_by sizeOf b

/-- The same, on the branches of a dispatch. -/
theorem AltsT.eval_flat_lenv_irrel {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty}
    {tags : List Nat} {full : Bool} (alts : AltsT Sg Γ Ω Ρ σ τ tags full) (h : alts.Flat)
    (tag : Nat) (fs : List Data) (δ : GEnv Sg.decls) (γ : Env Γ) (l₁ l₂ : LEnv τ Ω)
    (ρ : REnv Ρ) :
    alts.eval tag fs δ γ l₁ ρ = alts.eval tag fs δ γ l₂ ρ :=
  match alts, h with
  | .deflt b, h =>
      congrArg some (Tail.eval_flat_lenv_irrel b h δ γ l₁ l₂ ρ)
  | .nilFull, _ => rfl
  | .cons t fields _ body rest, h => by
      show (if t = tag then
              some (body.eval δ ((Env.ofData fields fs).append γ) l₁ ρ)
            else rest.eval tag fs δ γ l₁ ρ)
          = if t = tag then
              some (body.eval δ ((Env.ofData fields fs).append γ) l₂ ρ)
            else rest.eval tag fs δ γ l₂ ρ
      rw [Tail.eval_flat_lenv_irrel body h.1 δ ((Env.ofData fields fs).append γ) l₁ l₂ ρ,
        AltsT.eval_flat_lenv_irrel rest h.2 tag fs δ γ l₁ l₂ ρ]
  termination_by sizeOf alts

end

/-! ## A block opened at the empty label context -/

/-- **A closed block reads nothing but its environments.**  `Term.block` opens its tail at
    the empty label context, where the only label environment is the empty one — so the
    value of the block is a function of the global, value and recursion environments
    alone. -/
theorem Tail.eval_lenv_closed {Γ : Ctx} {Ρ : RCtx} {τ : Ty} (b : Tail Sg Γ [] Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (lenv : LEnv τ []) (ρ : REnv Ρ) :
    b.eval δ γ lenv ρ = b.eval δ γ .nil ρ := by
  cases lenv
  rfl

/-! ## Flatness survives renaming -/

mutual

/-- A flat block stays flat when its variables, labels and recursions are renamed. -/
theorem Tail.flat_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ₁ Ρ₂ : RCtx} {τ : Ty}
    (b : Tail Sg Γ₁ Ω₁ Ρ₁ τ) (ρ : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂) (ξ : RRen Ρ₁ Ρ₂)
    (h : b.Flat) : (b.rename ρ κ ξ).Flat :=
  match b, h with
  | .ret _, _ => trivial
  | .jmp _ _, h => absurd h (by simp [Tail.Flat])
  | .letT _ b, h => Tail.flat_rename b ρ.lift κ ξ h
  | .iteT _ t e, h => ⟨Tail.flat_rename t ρ κ ξ h.1, Tail.flat_rename e ρ κ ξ h.2⟩
  | .caseT _ alts _, h => AltsT.flat_rename alts ρ κ ξ h
  | .join _ _ _, h => absurd h (by simp [Tail.Flat])
  termination_by sizeOf b

/-- Flat branches stay flat when they are renamed. -/
theorem AltsT.flat_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ₁ Ρ₂ : RCtx} {σ τ : Ty}
    {tags : List Nat} {full : Bool} (alts : AltsT Sg Γ₁ Ω₁ Ρ₁ σ τ tags full)
    (ρ : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂) (ξ : RRen Ρ₁ Ρ₂) (h : alts.Flat) :
    (alts.rename ρ κ ξ).Flat :=
  match alts, h with
  | .deflt b, h => Tail.flat_rename b ρ κ ξ h
  | .nilFull, _ => trivial
  | .cons _ fields _ b rest, h =>
      ⟨Tail.flat_rename b (VRen.liftList fields ρ) κ ξ h.1,
        AltsT.flat_rename rest ρ κ ξ h.2⟩
  termination_by sizeOf alts

end

/-- The block of `Term.sharedTail` is **not** flat: it binds a join point.  Flatness is a
    real restriction, and the join point is what a dispatch with a shared tail needs. -/
example {Ρ : RCtx} :
    ¬ (Tail.join [Ty.nat] (.ret (♯0))
        (.iteT (♯0) (.jmp .head (.cons (Term.natL 1) .nil))
          (.jmp .head (.cons (Term.natL 2) .nil)))
        : Tail Sg [Ty.bool] [] Ρ Ty.nat).Flat := by
  simp [Tail.Flat]

end LakeJs.Expr

end
