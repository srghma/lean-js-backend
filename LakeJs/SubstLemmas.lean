module

public import LakeJs.Subst
public import LakeJs.Reduce

@[expose] public section

set_option autoImplicit false

/-!
# The laws of renaming and substitution, against the evaluator

`LakeJs.Subst` defines renaming and substitution.  What has to be known about them is that
they **mean** what they are meant to mean: renaming a term is reading it in a renamed
environment, and substituting into a term is reading it in an environment that holds the
values of the substituted terms.

That is what this module proves.  It replaces the older, purely syntactic algebra — a
renaming after a renaming is a renaming, and the three other composition laws, together
with the congruences and the identity laws — which the small-step semantics of the time
needed in order to push substitutions through a reduction sequence.  With a denotational
evaluator those laws are no longer the point: a pass that transforms a term is correct
when it does not change the term's *value*, and the two theorems below are what a proof
of that rests on.

* `Term.eval_rename` — renaming a term evaluates it in the renamed environment, and the
  same for a spine, a case, a block and its branches;
* `Term.eval_weaken` and `Term.eval_rweaken` — the two corollaries a pass uses most: the
  variable, or the recursion, that a weakening adds is not read.

They are stated with the environments related **pointwise** (`Env.Agree`, `REnv.Agree`,
`LEnv.Agree`), which is what makes them usable under a binder: going under one extends
both environments with the same values, and agreement is preserved.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Agreement of environments -/

/-- Two variable environments agree along a renaming when every variable has the same
    value on both sides. -/
def Env.Agree {Γ₁ Γ₂ : Ctx} (ρv : VRen Γ₁ Γ₂) (γ₁ : Env Γ₁) (γ₂ : Env Γ₂) : Prop :=
  ∀ {τ : Ty} (v : Γ₁ ∋ τ), γ₁.get v = γ₂.get (ρv v)

/-- The same for recursion environments. -/
def REnv.Agree {Ρ₁ Ρ₂ : RCtx} (ξ : RRen Ρ₁ Ρ₂) (ρ₁ : REnv Ρ₁) (ρ₂ : REnv Ρ₂) : Prop :=
  ∀ {r : RSig} (x : Ρ₁ ∋ᵣ r), ρ₁.get x = ρ₂.get (ξ x)

/-- The same for label environments. -/
def LEnv.Agree {τ : Ty} {Ω₁ Ω₂ : LCtx} (κ : LRen Ω₁ Ω₂) (l₁ : LEnv τ Ω₁)
    (l₂ : LEnv τ Ω₂) : Prop :=
  ∀ {ps : List Ty} (l : Ω₁ ∋ₗ ps), l₁.get l = l₂.get (κ l)

/-- Agreement survives one variable binder. -/
theorem Env.Agree.lift {Γ₁ Γ₂ : Ctx} {ρv : VRen Γ₁ Γ₂} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂}
    (h : Env.Agree ρv γ₁ γ₂) {σ : Ty} (a : σ.den) :
    Env.Agree ρv.lift (.cons a γ₁) (.cons a γ₂) := by
  intro τ v
  match v with
  | .head => rfl
  | .tail v => exact h v

/-- Agreement survives a binder that binds a whole list at once. -/
theorem Env.Agree.liftList {Γ₁ Γ₂ : Ctx} {ρv : VRen Γ₁ Γ₂} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂}
    (h : Env.Agree ρv γ₁ γ₂) :
    ∀ {ps : List Ty} (as : Env ps),
      Env.Agree (VRen.liftList ps ρv) (as.append γ₁) (as.append γ₂)
  | [], .nil => h
  | _ :: _, .cons a as => Env.Agree.lift (Env.Agree.liftList h as) a

/-- Agreement survives one recursion binder. -/
theorem REnv.Agree.lift {Ρ₁ Ρ₂ : RCtx} {ξ : RRen Ρ₁ Ρ₂} {ρ₁ : REnv Ρ₁} {ρ₂ : REnv Ρ₂}
    (h : REnv.Agree ξ ρ₁ ρ₂) {r : RSig} (f : Env r.ps → r.ret.den) :
    REnv.Agree ξ.lift (.cons f ρ₁) (.cons f ρ₂) := by
  intro s x
  match x with
  | .head => rfl
  | .tail x => exact h x

/-- Agreement survives one label binder. -/
theorem LEnv.Agree.lift {τ : Ty} {Ω₁ Ω₂ : LCtx} {κ : LRen Ω₁ Ω₂} {l₁ : LEnv τ Ω₁}
    {l₂ : LEnv τ Ω₂} (h : LEnv.Agree κ l₁ l₂) {ps : List Ty} (f : Env ps → τ.den) :
    LEnv.Agree κ.lift (.cons f l₁) (.cons f l₂) := by
  intro qs l
  match l with
  | .head => rfl
  | .tail l => exact h l

/-! ## Renaming is reading in a renamed environment -/

mutual

/-- **Renaming a term evaluates it in the renamed environment.** -/
theorem Term.eval_rename {Γ₁ Γ₂ : Ctx} {Ρ₁ Ρ₂ : RCtx} {τ : Ty} :
    ∀ (t : Term Sg Γ₁ Ρ₁ τ) (ρv : VRen Γ₁ Γ₂) (ξ : RRen Ρ₁ Ρ₂) (δ : GEnv Sg.decls)
      (γ₁ : Env Γ₁) (γ₂ : Env Γ₂) (ρ₁ : REnv Ρ₁) (ρ₂ : REnv Ρ₂),
      Env.Agree ρv γ₁ γ₂ → REnv.Agree ξ ρ₁ ρ₂ →
      (t.rename ρv ξ).eval δ γ₂ ρ₂ = t.eval δ γ₁ ρ₁
  | .var v, _, _, _, _, _, _, _, hγ, _ => (hγ v).symm
  | .lam b, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show (fun a => (b.rename ρv.lift ξ).eval δ (.cons a γ₂) ρ₂)
          = fun a => b.eval δ (.cons a γ₁) ρ₁
      funext a
      exact Term.eval_rename b ρv.lift ξ δ _ _ ρ₁ ρ₂ (Env.Agree.lift hγ a) hρ
  | .ap f a, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show (f.rename ρv ξ).eval δ γ₂ ρ₂ ((a.rename ρv ξ).eval δ γ₂ ρ₂) = _
      rw [Term.eval_rename f ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ,
        Term.eval_rename a ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
      rfl
  | .lit _, _, _, _, _, _, _, _, _, _ => rfl
  | .global _, _, _, _, _, _, _, _, _, _ => rfl
  | .extern _, _, _, _, _, _, _, _, _, _ => rfl
  | .lazyMk e, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show (fun _ => (e.rename ρv ξ).eval δ γ₂ ρ₂) = fun _ => e.eval δ γ₁ ρ₁
      funext _
      exact Term.eval_rename e ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ
  | .lazyForce e, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show ((e.rename ρv ξ).eval δ γ₂ ρ₂) () = (e.eval δ γ₁ ρ₁) ()
      rw [Term.eval_rename e ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
  | .letE e b, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show (b.rename ρv.lift ξ).eval δ (.cons ((e.rename ρv ξ).eval δ γ₂ ρ₂) γ₂) ρ₂ = _
      rw [Term.eval_rename e ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
      exact Term.eval_rename b ρv.lift ξ δ _ _ ρ₁ ρ₂ (Env.Agree.lift hγ _) hρ
  | .ite c t e, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show (if cond ((c.rename ρv ξ).eval δ γ₂ ρ₂) true false then
              (t.rename ρv ξ).eval δ γ₂ ρ₂ else (e.rename ρv ξ).eval δ γ₂ ρ₂)
          = if cond (c.eval δ γ₁ ρ₁) true false then t.eval δ γ₁ ρ₁ else e.eval δ γ₁ ρ₁
      rw [Term.eval_rename c ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ,
        Term.eval_rename t ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ,
        Term.eval_rename e ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
  | .ctor (τ := σ) i fs h args, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show σ.buildVal i ((args.rename ρv ξ).eval δ γ₂ ρ₂).toData
          = σ.buildVal i (args.eval δ γ₁ ρ₁).toData
      rw [Spine.eval_rename args ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
  | .proj (σ := σ) (τ := τ') e i j hOne h, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show τ'.ofData ((σ.fieldsOfVal ((e.rename ρv ξ).eval δ γ₂ ρ₂)).getD j .opaque)
          = τ'.ofData ((σ.fieldsOfVal (e.eval δ γ₁ ρ₁)).getD j .opaque)
      rw [Term.eval_rename e ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
  | .tagOf (σ := σ) e h, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show σ.tagOfVal ((e.rename ρv ξ).eval δ γ₂ ρ₂) = σ.tagOfVal (e.eval δ γ₁ ρ₁)
      rw [Term.eval_rename e ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
  | .structSize (σ := σ) e, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show Data.size (σ.toData ((e.rename ρv ξ).eval δ γ₂ ρ₂))
          = Data.size (σ.toData (e.eval δ γ₁ ρ₁))
      rw [Term.eval_rename e ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
  | .caseTag (σ := σ) (τ := τ') scrut alts h, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      have hs := Term.eval_rename scrut ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ
      have ha := Alts.eval_rename alts ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ
      show (match (alts.rename ρv ξ).eval (σ.tagOfVal ((scrut.rename ρv ξ).eval δ γ₂ ρ₂))
              (σ.fieldsOfVal ((scrut.rename ρv ξ).eval δ γ₂ ρ₂)) δ γ₂ ρ₂ with
            | some r => r | none => τ'.dflt)
          = match alts.eval (σ.tagOfVal (scrut.eval δ γ₁ ρ₁))
              (σ.fieldsOfVal (scrut.eval δ γ₁ ρ₁)) δ γ₁ ρ₁ with
            | some r => r | none => τ'.dflt
      rw [hs, ha]
  | .block b, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show (b.rename ρv LRen.id ξ).eval δ γ₂ .nil ρ₂ = b.eval δ γ₁ .nil ρ₁
      exact Tail.eval_rename b ρv LRen.id ξ δ γ₁ γ₂ .nil .nil ρ₁ ρ₂ hγ (fun {_} l => nomatch l)
        hρ
  | .fix (τ := τr) ps k measure body stuck, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show ((Term.fix ps k (measure.rename (VRen.liftList ps ρv) ξ)
              (body.rename (VRen.liftList ps ρv) ξ.lift)
              (stuck.rename (VRen.liftList ps ρv) ξ)).eval δ γ₂ ρ₂)
          = (Term.fix ps k measure body stuck).eval δ γ₁ ρ₁
      rw [Term.eval_fix, Term.eval_fix]
      refine congrArg (Env.curry ps) ?_
      show Term.fixFun _ _ _ δ γ₂ ρ₂ = Term.fixFun _ _ _ δ γ₁ ρ₁
      refine Lex.guardedFix_congr (fun as => ?_) (fun as => ?_) (fun g as => ?_)
      · show Env.toNatVec k _ = Env.toNatVec k _
        rw [Spine.eval_rename measure (VRen.liftList ps ρv) ξ δ (Env.append as γ₁)
          (Env.append as γ₂) ρ₁ ρ₂ (Env.Agree.liftList hγ as) hρ]
      · exact Term.eval_rename stuck (VRen.liftList ps ρv) ξ δ _ _ ρ₁ ρ₂
          (Env.Agree.liftList hγ as) hρ
      · have hfun :
            REnv.Agree (RRen.lift (r := ⟨ps, τr⟩) ξ) (.cons g ρ₁) (.cons g ρ₂) := by
          intro s x
          match x with
          | .head => rfl
          | .tail x => exact hρ x
        exact Term.eval_rename body (VRen.liftList ps ρv) ξ.lift δ _ _ _ _
          (Env.Agree.liftList hγ as) hfun
  | .selfCall r args, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show ρ₂.get (ξ r) ((args.rename ρv ξ).eval δ γ₂ ρ₂) = ρ₁.get r (args.eval δ γ₁ ρ₁)
      rw [Spine.eval_rename args ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ, hρ r]

/-- The same, for a spine. -/
theorem Spine.eval_rename {Γ₁ Γ₂ : Ctx} {Ρ₁ Ρ₂ : RCtx} {σs : List Ty} :
    ∀ (s : Spine Sg Γ₁ Ρ₁ σs) (ρv : VRen Γ₁ Γ₂) (ξ : RRen Ρ₁ Ρ₂) (δ : GEnv Sg.decls)
      (γ₁ : Env Γ₁) (γ₂ : Env Γ₂) (ρ₁ : REnv Ρ₁) (ρ₂ : REnv Ρ₂),
      Env.Agree ρv γ₁ γ₂ → REnv.Agree ξ ρ₁ ρ₂ →
      (s.rename ρv ξ).eval δ γ₂ ρ₂ = s.eval δ γ₁ ρ₁
  | .nil, _, _, _, _, _, _, _, _, _ => rfl
  | .cons a rest, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ => by
      show Env.cons ((a.rename ρv ξ).eval δ γ₂ ρ₂) ((rest.rename ρv ξ).eval δ γ₂ ρ₂)
          = Env.cons (a.eval δ γ₁ ρ₁) (rest.eval δ γ₁ ρ₁)
      rw [Term.eval_rename a ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ,
        Spine.eval_rename rest ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]

/-- The same, for the branches of a case. -/
theorem Alts.eval_rename {Γ₁ Γ₂ : Ctx} {Ρ₁ Ρ₂ : RCtx} {σ τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (alts : Alts Sg Γ₁ Ρ₁ σ τ tags full) (ρv : VRen Γ₁ Γ₂) (ξ : RRen Ρ₁ Ρ₂)
      (δ : GEnv Sg.decls) (γ₁ : Env Γ₁) (γ₂ : Env Γ₂) (ρ₁ : REnv Ρ₁) (ρ₂ : REnv Ρ₂),
      Env.Agree ρv γ₁ γ₂ → REnv.Agree ξ ρ₁ ρ₂ →
      ∀ (tag : Nat) (fs : List Data),
        (alts.rename ρv ξ).eval tag fs δ γ₂ ρ₂ = alts.eval tag fs δ γ₁ ρ₁
  | .deflt t, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ, _, _ => by
      show some ((t.rename ρv ξ).eval δ γ₂ ρ₂) = some (t.eval δ γ₁ ρ₁)
      rw [Term.eval_rename t ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
  | .nilFull, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .cons t fields h body rest, ρv, ξ, δ, γ₁, γ₂, ρ₁, ρ₂, hγ, hρ, tag, fs => by
      show (if t = tag then
              some ((body.rename (VRen.liftList fields ρv) ξ).eval δ
                ((Env.ofData fields fs).append γ₂) ρ₂)
            else (rest.rename ρv ξ).eval tag fs δ γ₂ ρ₂)
          = if t = tag then
              some (body.eval δ ((Env.ofData fields fs).append γ₁) ρ₁)
            else rest.eval tag fs δ γ₁ ρ₁
      by_cases hc : t = tag
      · simp only [hc, if_pos]
        exact congrArg some (Term.eval_rename body (VRen.liftList fields ρv) ξ δ _ _
          ρ₁ ρ₂ (Env.Agree.liftList hγ (Env.ofData fields fs)) hρ)
      · simp only [if_neg hc]
        exact Alts.eval_rename rest ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ tag fs

/-- The same, for a block. -/
theorem Tail.eval_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ₁ Ρ₂ : RCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ₁ Ω₁ Ρ₁ τ) (ρv : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂) (ξ : RRen Ρ₁ Ρ₂)
      (δ : GEnv Sg.decls) (γ₁ : Env Γ₁) (γ₂ : Env Γ₂) (l₁ : LEnv τ Ω₁) (l₂ : LEnv τ Ω₂)
      (ρ₁ : REnv Ρ₁) (ρ₂ : REnv Ρ₂),
      Env.Agree ρv γ₁ γ₂ → LEnv.Agree κ l₁ l₂ → REnv.Agree ξ ρ₁ ρ₂ →
      (b.rename ρv κ ξ).eval δ γ₂ l₂ ρ₂ = b.eval δ γ₁ l₁ ρ₁
  | .ret t, ρv, _, ξ, δ, γ₁, γ₂, _, _, ρ₁, ρ₂, hγ, _, hρ =>
      Term.eval_rename t ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ
  | .jmp l args, ρv, κ, ξ, δ, γ₁, γ₂, l₁, l₂, ρ₁, ρ₂, hγ, hl, hρ => by
      show l₂.get (κ l) ((args.rename ρv ξ).eval δ γ₂ ρ₂) = l₁.get l (args.eval δ γ₁ ρ₁)
      rw [Spine.eval_rename args ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ, hl l]
  | .letT e rest, ρv, κ, ξ, δ, γ₁, γ₂, l₁, l₂, ρ₁, ρ₂, hγ, hl, hρ => by
      show (rest.rename ρv.lift κ ξ).eval δ (.cons ((e.rename ρv ξ).eval δ γ₂ ρ₂) γ₂)
            l₂ ρ₂
          = rest.eval δ (.cons (e.eval δ γ₁ ρ₁) γ₁) l₁ ρ₁
      rw [Term.eval_rename e ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ]
      exact Tail.eval_rename rest ρv.lift κ ξ δ _ _ l₁ l₂ ρ₁ ρ₂ (Env.Agree.lift hγ _) hl hρ
  | .iteT c t e, ρv, κ, ξ, δ, γ₁, γ₂, l₁, l₂, ρ₁, ρ₂, hγ, hl, hρ => by
      show (if cond ((c.rename ρv ξ).eval δ γ₂ ρ₂) true false then
              (t.rename ρv κ ξ).eval δ γ₂ l₂ ρ₂ else (e.rename ρv κ ξ).eval δ γ₂ l₂ ρ₂)
          = if cond (c.eval δ γ₁ ρ₁) true false then t.eval δ γ₁ l₁ ρ₁
            else e.eval δ γ₁ l₁ ρ₁
      rw [Term.eval_rename c ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ,
        Tail.eval_rename t ρv κ ξ δ γ₁ γ₂ l₁ l₂ ρ₁ ρ₂ hγ hl hρ,
        Tail.eval_rename e ρv κ ξ δ γ₁ γ₂ l₁ l₂ ρ₁ ρ₂ hγ hl hρ]
  | .caseT (σ := σ) scrut alts h, ρv, κ, ξ, δ, γ₁, γ₂, l₁, l₂, ρ₁, ρ₂, hγ, hl, hρ => by
      have hs := Term.eval_rename scrut ρv ξ δ γ₁ γ₂ ρ₁ ρ₂ hγ hρ
      have ha := AltsT.eval_rename alts ρv κ ξ δ γ₁ γ₂ l₁ l₂ ρ₁ ρ₂ hγ hl hρ
      show (match (alts.rename ρv κ ξ).eval
              (σ.tagOfVal ((scrut.rename ρv ξ).eval δ γ₂ ρ₂))
              (σ.fieldsOfVal ((scrut.rename ρv ξ).eval δ γ₂ ρ₂)) δ γ₂ l₂ ρ₂ with
            | some r => r | none => _)
          = match alts.eval (σ.tagOfVal (scrut.eval δ γ₁ ρ₁))
              (σ.fieldsOfVal (scrut.eval δ γ₁ ρ₁)) δ γ₁ l₁ ρ₁ with
            | some r => r | none => _
      rw [hs, ha]
  | .join ps body rest, ρv, κ, ξ, δ, γ₁, γ₂, l₁, l₂, ρ₁, ρ₂, hγ, hl, hρ => by
      have hbody : (fun as => (body.rename (VRen.liftList ps ρv) κ ξ).eval δ
            (Env.append as γ₂) l₂ ρ₂)
          = fun as => body.eval δ (Env.append as γ₁) l₁ ρ₁ := by
        funext as
        exact Tail.eval_rename body (VRen.liftList ps ρv) κ ξ δ _ _ l₁ l₂ ρ₁ ρ₂
          (Env.Agree.liftList hγ as) hl hρ
      show (rest.rename ρv κ.lift ξ).eval δ γ₂
            (.cons (fun as => (body.rename (VRen.liftList ps ρv) κ ξ).eval δ
              (Env.append as γ₂) l₂ ρ₂) l₂) ρ₂
          = rest.eval δ γ₁
            (.cons (fun as => body.eval δ (Env.append as γ₁) l₁ ρ₁) l₁) ρ₁
      rw [hbody]
      exact Tail.eval_rename rest ρv κ.lift ξ δ γ₁ γ₂ _ _ ρ₁ ρ₂ hγ
        (LEnv.Agree.lift hl (fun as => body.eval δ (Env.append as γ₁) l₁ ρ₁)) hρ

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.eval_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ₁ Ρ₂ : RCtx} {σ τ : Ty}
    {tags : List Nat} {full : Bool} :
    ∀ (alts : AltsT Sg Γ₁ Ω₁ Ρ₁ σ τ tags full) (ρv : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂)
      (ξ : RRen Ρ₁ Ρ₂) (δ : GEnv Sg.decls) (γ₁ : Env Γ₁) (γ₂ : Env Γ₂) (l₁ : LEnv τ Ω₁)
      (l₂ : LEnv τ Ω₂) (ρ₁ : REnv Ρ₁) (ρ₂ : REnv Ρ₂),
      Env.Agree ρv γ₁ γ₂ → LEnv.Agree κ l₁ l₂ → REnv.Agree ξ ρ₁ ρ₂ →
      ∀ (tag : Nat) (fs : List Data),
        (alts.rename ρv κ ξ).eval tag fs δ γ₂ l₂ ρ₂ = alts.eval tag fs δ γ₁ l₁ ρ₁
  | .deflt b, ρv, κ, ξ, δ, γ₁, γ₂, l₁, l₂, ρ₁, ρ₂, hγ, hl, hρ, _, _ => by
      show some ((b.rename ρv κ ξ).eval δ γ₂ l₂ ρ₂) = some (b.eval δ γ₁ l₁ ρ₁)
      rw [Tail.eval_rename b ρv κ ξ δ γ₁ γ₂ l₁ l₂ ρ₁ ρ₂ hγ hl hρ]
  | .nilFull, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .cons t fields h body rest, ρv, κ, ξ, δ, γ₁, γ₂, l₁, l₂, ρ₁, ρ₂, hγ, hl, hρ,
      tag, fs => by
      show (if t = tag then
              some ((body.rename (VRen.liftList fields ρv) κ ξ).eval δ
                ((Env.ofData fields fs).append γ₂) l₂ ρ₂)
            else (rest.rename ρv κ ξ).eval tag fs δ γ₂ l₂ ρ₂)
          = if t = tag then
              some (body.eval δ ((Env.ofData fields fs).append γ₁) l₁ ρ₁)
            else rest.eval tag fs δ γ₁ l₁ ρ₁
      by_cases hc : t = tag
      · simp only [hc, if_pos]
        exact congrArg some (Tail.eval_rename body (VRen.liftList fields ρv) κ ξ δ _ _
          l₁ l₂ ρ₁ ρ₂ (Env.Agree.liftList hγ (Env.ofData fields fs)) hl hρ)
      · simp only [if_neg hc]
        exact AltsT.eval_rename rest ρv κ ξ δ γ₁ γ₂ l₁ l₂ ρ₁ ρ₂ hγ hl hρ tag fs

end

/-- **Weakening does not change a value**: the variable a weakening adds is not read. -/
theorem Term.eval_weaken {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty} (t : Term Sg Γ Ρ τ)
    (δ : GEnv Sg.decls) (a : σ.den) (γ : Env Γ) (ρ : REnv Ρ) :
    (Term.weaken (σ := σ) t).eval δ (.cons a γ) ρ = t.eval δ γ ρ :=
  Term.eval_rename t VRen.weaken RRen.id δ γ (.cons a γ) ρ ρ (fun _ => rfl) (fun _ => rfl)

/-- **Weakening by a recursion does not change a value** either: the recursion a
    weakening adds cannot be called by a term that was written without it. -/
theorem Term.eval_rweaken {Γ : Ctx} {Ρ : RCtx} {r : RSig} {τ : Ty} (t : Term Sg Γ Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (f : Env r.ps → r.ret.den) (ρ : REnv Ρ) :
    (Term.rweaken (r := r) t).eval δ γ (.cons f ρ) = t.eval δ γ ρ :=
  Term.eval_rename t VRen.id RRen.weaken δ γ γ ρ (.cons f ρ) (fun _ => rfl)
    (fun _ => rfl)

end LakeJs.Expr

end
