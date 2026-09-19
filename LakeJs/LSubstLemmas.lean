module

public import LakeJs.SubstLemmas

@[expose] public section

set_option autoImplicit false

/-!
# Inlining a join point does not change what a block means

`LakeJs.SubstLemmas` is the algebra of the **variable** context, against the evaluator:
renaming a term is reading it in a renamed environment.  This module is the other half —
the algebra of the **label** context — and its purpose is the correctness of the one
transformation the label context admits:

```lean
Tail.eval_lsubst0 :
  (rest.lsubst0 jb).eval δ γ lenv ρ = (Tail.join ps jb rest).eval δ γ lenv ρ
```

**Inlining a join point is meaning-preserving.**  A block that binds a join point and the
block in which every jump to it has been replaced by the join point's body — with the
jump's arguments bound in front of it by `Tail.letSpine` — have the same value, in every
environment.  That is what licenses an emitter to duplicate a small join point rather
than emit a label for it, and (with `Tail.inlineSize_lsubst0_lt`, which says the measure
goes down) to keep doing so until none is left.

Three small facts do the work, and each is worth having on its own:

* `Term.eval_weakenList` — a term does not read the variables a list-weakening adds;
* `Spine.eval_vars` — the spine of a binder's own parameters evaluates to the arguments
  themselves;
* `Tail.eval_letSpine` — binding the arguments of a jump with `let`s is the same as
  evaluating the block in the environment those arguments extend.

The general statement is `Tail.eval_lsubst`, whose hypothesis is that every label of the
source context means what the substitution puts there.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Weakening by a list of variables -/

/-- A list-weakening is an agreement: the variables it adds are the ones the renamed term
    does not read. -/
theorem Env.Agree.weakenList {Γ : Ctx} (γ : Env Γ) :
    ∀ {σs : List Ty} (as : Env σs), Env.Agree (VRen.weakenList σs) γ (as.append γ)
  | [], .nil => fun _ => rfl
  | _ :: _, .cons _ as => fun v => Env.Agree.weakenList γ as v

/-- **A term does not read the variables a list-weakening adds.** -/
theorem Term.eval_weakenList {Γ : Ctx} {Ρ : RCtx} {σs : List Ty} {τ : Ty}
    (t : Term Sg Γ Ρ τ) (δ : GEnv Sg.decls) (as : Env σs) (γ : Env Γ) (ρ : REnv Ρ) :
    (t.rename (VRen.weakenList σs) RRen.id).eval δ (as.append γ) ρ = t.eval δ γ ρ :=
  Term.eval_rename t (VRen.weakenList σs) RRen.id δ γ (as.append γ) ρ ρ
    (Env.Agree.weakenList γ as) (fun _ => rfl)

/-- **The parameters of a binder, read back.**  `Spine.vars ps` is the spine of the
    binder's own parameters, and in an environment that binds them it evaluates to
    exactly those arguments. -/
theorem Spine.eval_vars {Γ : Ctx} {Ρ : RCtx} :
    ∀ {ps : List Ty} (as : Env ps) (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ),
      (Spine.vars (Sg := Sg) (Γ := Γ) (Ρ := Ρ) ps).eval δ (as.append γ) ρ = as
  | [], .nil, _, _, _ => rfl
  | _ :: ps, .cons a as, δ, γ, ρ => by
      show Env.cons a
          ((Spine.vars (Γ := Γ) (Ρ := Ρ) ps |>.rename VRen.weaken RRen.id).eval δ
            (.cons a (as.append γ)) ρ) = Env.cons a as
      have h : ((Spine.vars (Sg := Sg) (Γ := Γ) (Ρ := Ρ) ps).rename VRen.weaken
            RRen.id).eval δ (.cons a (as.append γ)) ρ
          = (Spine.vars (Sg := Sg) (Γ := Γ) (Ρ := Ρ) ps).eval δ (as.append γ) ρ :=
        Spine.eval_rename (Spine.vars ps) VRen.weaken RRen.id δ (as.append γ)
          (.cons a (as.append γ)) ρ ρ (fun _ => rfl) (fun _ => rfl)
      rw [h, Spine.eval_vars as δ γ ρ]

/-- **Binding the arguments of a jump is passing them.**  The `let`s `Tail.letSpine` puts
    in front of a block bind exactly the environment the block is read in. -/
theorem Tail.eval_letSpine {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty} :
    ∀ {σs : List Ty} (args : Spine Sg Γ Ρ σs) (jb : Tail Sg (σs ++ Γ) Ω Ρ τ)
      (δ : GEnv Sg.decls) (γ : Env Γ) (lenv : LEnv τ Ω) (ρ : REnv Ρ),
      (Tail.letSpine args jb).eval δ γ lenv ρ
        = jb.eval δ ((args.eval δ γ ρ).append γ) lenv ρ
  | [], .nil, _, _, _, _, _ => rfl
  | _ :: σs, .cons a rest, jb, δ, γ, lenv, ρ => by
      show (Tail.letSpine rest
          (.letT (a.rename (VRen.weakenList σs) RRen.id) jb)).eval δ γ lenv ρ = _
      rw [Tail.eval_letSpine rest (.letT (a.rename (VRen.weakenList σs) RRen.id) jb)
        δ γ lenv ρ]
      show jb.eval δ (.cons ((a.rename (VRen.weakenList σs) RRen.id).eval δ
            ((rest.eval δ γ ρ).append γ) ρ) ((rest.eval δ γ ρ).append γ)) lenv ρ
          = jb.eval δ (.cons (a.eval δ γ ρ) ((rest.eval δ γ ρ).append γ)) lenv ρ
      rw [Term.eval_weakenList a δ (rest.eval δ γ ρ) γ ρ]

/-! ## What a label substitution has to satisfy -/

/-- A label environment agrees with a label substitution when every label means the block
    the substitution puts there. -/
def LSub.Agree {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {τ : Ty} (θ : LSub Sg Γ Ω₁ Ω₂ Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (l₁ : LEnv τ Ω₁) (l₂ : LEnv τ Ω₂) (ρ : REnv Ρ) :
    Prop :=
  ∀ {ps : List Ty} (l : Ω₁ ∋ₗ ps) (as : Env ps),
    l₁.get l as = (θ l).eval δ (as.append γ) l₂ ρ

/-- Agreement survives one variable binder. -/
theorem LSub.Agree.vlift {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {σ τ : Ty}
    {θ : LSub Sg Γ Ω₁ Ω₂ Ρ τ} {δ : GEnv Sg.decls} {γ : Env Γ} {l₁ : LEnv τ Ω₁}
    {l₂ : LEnv τ Ω₂} {ρ : REnv Ρ} (h : LSub.Agree θ δ γ l₁ l₂ ρ) (v : σ.den) :
    LSub.Agree θ.vlift δ (.cons v γ) l₁ l₂ ρ := by
  intro ps l as
  show l₁.get l as
      = ((θ l).rename (VRen.liftList _ VRen.weaken) LRen.id RRen.id).eval δ
        (as.append (.cons v γ)) l₂ ρ
  have hbase : Env.Agree (VRen.weaken (σ := σ)) γ (Env.cons v γ) := fun _ => rfl
  rw [Tail.eval_rename (θ l) (VRen.liftList _ VRen.weaken) LRen.id RRen.id δ
    (as.append γ) (as.append (.cons v γ)) l₂ l₂ ρ ρ
    (Env.Agree.liftList hbase as) (fun _ => rfl) (fun _ => rfl)]
  exact h l as

/-- Agreement survives a binder that binds a whole list of variables. -/
theorem LSub.Agree.vliftList {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {τ : Ty}
    {θ : LSub Sg Γ Ω₁ Ω₂ Ρ τ} {δ : GEnv Sg.decls} {γ : Env Γ} {l₁ : LEnv τ Ω₁}
    {l₂ : LEnv τ Ω₂} {ρ : REnv Ρ} (h : LSub.Agree θ δ γ l₁ l₂ ρ) {qs : List Ty}
    (bs : Env qs) : LSub.Agree (LSub.vliftList qs θ) δ (bs.append γ) l₁ l₂ ρ := by
  intro ps l as
  show l₁.get l as
      = ((θ l).rename (VRen.liftList _ (VRen.weakenList qs)) LRen.id RRen.id).eval δ
        (as.append (bs.append γ)) l₂ ρ
  rw [Tail.eval_rename (θ l) (VRen.liftList _ (VRen.weakenList qs)) LRen.id RRen.id δ
    (as.append γ) (as.append (bs.append γ)) l₂ l₂ ρ ρ
    (Env.Agree.liftList (Env.Agree.weakenList γ bs) as) (fun _ => rfl) (fun _ => rfl)]
  exact h l as

/-! ## The substitution theorem -/

mutual

/-- **A label substitution means what it says.**  Replacing every jump by the block its
    label names does not change the value of the block, as long as the label environment
    it is read in gives each label that block's meaning. -/
theorem Tail.eval_lsubst {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ Ω₁ Ρ τ) (θ : LSub Sg Γ Ω₁ Ω₂ Ρ τ) (δ : GEnv Sg.decls) (γ : Env Γ)
      (l₁ : LEnv τ Ω₁) (l₂ : LEnv τ Ω₂) (ρ : REnv Ρ),
      LSub.Agree θ δ γ l₁ l₂ ρ →
      (b.lsubst θ).eval δ γ l₂ ρ = b.eval δ γ l₁ ρ
  | .ret _, _, _, _, _, _, _, _ => rfl
  | .jmp l args, θ, δ, γ, l₁, l₂, ρ, hθ => by
      show (Tail.letSpine args (θ l)).eval δ γ l₂ ρ = l₁.get l (args.eval δ γ ρ)
      rw [Tail.eval_letSpine args (θ l) δ γ l₂ ρ, hθ l (args.eval δ γ ρ)]
  | .letT e b, θ, δ, γ, l₁, l₂, ρ, hθ => by
      show (b.lsubst θ.vlift).eval δ (.cons (e.eval δ γ ρ) γ) l₂ ρ
          = b.eval δ (.cons (e.eval δ γ ρ) γ) l₁ ρ
      exact Tail.eval_lsubst b θ.vlift δ _ l₁ l₂ ρ (hθ.vlift (e.eval δ γ ρ))
  | .iteT c t e, θ, δ, γ, l₁, l₂, ρ, hθ => by
      show (if cond (c.eval δ γ ρ) true false then (t.lsubst θ).eval δ γ l₂ ρ
            else (e.lsubst θ).eval δ γ l₂ ρ)
          = if cond (c.eval δ γ ρ) true false then t.eval δ γ l₁ ρ else e.eval δ γ l₁ ρ
      rw [Tail.eval_lsubst t θ δ γ l₁ l₂ ρ hθ, Tail.eval_lsubst e θ δ γ l₁ l₂ ρ hθ]
  | .caseT (σ := σ) scrut alts h, θ, δ, γ, l₁, l₂, ρ, hθ => by
      have ha := AltsT.eval_lsubst alts θ δ γ l₁ l₂ ρ hθ
      show (match (alts.lsubst θ).eval (σ.tagOfVal (scrut.eval δ γ ρ))
              (σ.fieldsOfVal (scrut.eval δ γ ρ)) δ γ l₂ ρ with
            | some r => r | none => _)
          = match alts.eval (σ.tagOfVal (scrut.eval δ γ ρ))
              (σ.fieldsOfVal (scrut.eval δ γ ρ)) δ γ l₁ ρ with
            | some r => r | none => _
      rw [ha]
  | .join ps body rest, θ, δ, γ, l₁, l₂, ρ, hθ => by
      have hbody : ∀ as : Env ps,
          (body.lsubst (LSub.vliftList ps θ)).eval δ (as.append γ) l₂ ρ
            = body.eval δ (as.append γ) l₁ ρ := fun as =>
        Tail.eval_lsubst body (LSub.vliftList ps θ) δ _ l₁ l₂ ρ (hθ.vliftList as)
      have hfun : (fun as => (body.lsubst (LSub.vliftList ps θ)).eval δ
            (Env.append as γ) l₂ ρ)
          = fun as => body.eval δ (Env.append as γ) l₁ ρ := funext hbody
      show (rest.lsubst θ.lift).eval δ γ
            (.cons (fun as => (body.lsubst (LSub.vliftList ps θ)).eval δ
              (Env.append as γ) l₂ ρ) l₂) ρ
          = rest.eval δ γ (.cons (fun as => body.eval δ (Env.append as γ) l₁ ρ) l₁) ρ
      rw [hfun]
      refine Tail.eval_lsubst rest θ.lift δ γ _ _ ρ ?_
      intro qs l as
      cases l with
      | head =>
          show (fun bs => body.eval δ (Env.append bs γ) l₁ ρ) as
              = (Tail.jmp (Ω := ps :: Ω₂) LVar.head (Spine.vars ps)).eval δ
                (as.append γ) (.cons (fun bs => body.eval δ (Env.append bs γ) l₁ ρ) l₂) ρ
          show body.eval δ (Env.append as γ) l₁ ρ
              = body.eval δ (Env.append
                  ((Spine.vars (Sg := Sg) (Γ := Γ) (Ρ := Ρ) ps).eval δ (as.append γ) ρ)
                  γ) l₁ ρ
          rw [Spine.eval_vars (ps := ps) as δ γ ρ]
      | tail l =>
          have hw : ((θ l).lweaken).eval δ (as.append γ)
                (.cons (fun bs => body.eval δ (Env.append bs γ) l₁ ρ) l₂) ρ
              = (θ l).eval δ (as.append γ) l₂ ρ :=
            Tail.eval_rename (θ l) VRen.id LRen.weaken RRen.id δ (as.append γ)
              (as.append γ) l₂
              (.cons (fun bs => body.eval δ (Env.append bs γ) l₁ ρ) l₂) ρ ρ
              (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          show l₁.get l as
              = ((θ l).lweaken).eval δ (as.append γ)
                (.cons (fun bs => body.eval δ (Env.append bs γ) l₁ ρ) l₂) ρ
          rw [hw]
          exact hθ l as

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.eval_lsubst {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {Ρ : RCtx} {σ τ : Ty}
    {tags : List Nat} {full : Bool} :
    ∀ (alts : AltsT Sg Γ Ω₁ Ρ σ τ tags full) (θ : LSub Sg Γ Ω₁ Ω₂ Ρ τ)
      (δ : GEnv Sg.decls) (γ : Env Γ) (l₁ : LEnv τ Ω₁) (l₂ : LEnv τ Ω₂) (ρ : REnv Ρ),
      LSub.Agree θ δ γ l₁ l₂ ρ →
      ∀ (tag : Nat) (fs : List Data),
        (alts.lsubst θ).eval tag fs δ γ l₂ ρ = alts.eval tag fs δ γ l₁ ρ
  | .deflt b, θ, δ, γ, l₁, l₂, ρ, hθ, _, _ => by
      show some ((b.lsubst θ).eval δ γ l₂ ρ) = some (b.eval δ γ l₁ ρ)
      rw [Tail.eval_lsubst b θ δ γ l₁ l₂ ρ hθ]
  | .nilFull, _, _, _, _, _, _, _, _, _ => rfl
  | .cons t fields h body rest, θ, δ, γ, l₁, l₂, ρ, hθ, tag, fs => by
      show (if t = tag then
              some ((body.lsubst (LSub.vliftList fields θ)).eval δ
                ((Env.ofData fields fs).append γ) l₂ ρ)
            else (rest.lsubst θ).eval tag fs δ γ l₂ ρ)
          = if t = tag then some (body.eval δ ((Env.ofData fields fs).append γ) l₁ ρ)
            else rest.eval tag fs δ γ l₁ ρ
      by_cases hc : t = tag
      · simp only [hc, if_pos]
        exact congrArg some (Tail.eval_lsubst body (LSub.vliftList fields θ) δ _ l₁ l₂ ρ
          (hθ.vliftList (Env.ofData fields fs)))
      · simp only [if_neg hc]
        exact AltsT.eval_lsubst rest θ δ γ l₁ l₂ ρ hθ tag fs

end

/-- **Inlining a join point is meaning-preserving.**  The block in which the label has
    been replaced by the block it names — with each jump's arguments bound in front of it
    — has the same value as the block that binds the join point. -/
theorem Tail.eval_lsubst0 {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {ps : List Ty} {τ : Ty}
    (rest : Tail Sg Γ (ps :: Ω) Ρ τ) (jb : Tail Sg (ps ++ Γ) Ω Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (lenv : LEnv τ Ω) (ρ : REnv Ρ) :
    (rest.lsubst0 jb).eval δ γ lenv ρ = (Tail.join ps jb rest).eval δ γ lenv ρ := by
  refine Tail.eval_lsubst rest (LSub.zero jb) δ γ _ lenv ρ ?_
  intro qs l as
  cases l with
  | head => rfl
  | tail l =>
      show lenv.get l as
          = (Tail.jmp (Ω := Ω) l (Spine.vars qs)).eval δ (as.append γ) lenv ρ
      show lenv.get l as
          = lenv.get l ((Spine.vars (Sg := Sg) (Γ := Γ) (Ρ := Ρ) qs).eval δ
            (as.append γ) ρ)
      rw [Spine.eval_vars as δ γ ρ]

end LakeJs.Expr

end
