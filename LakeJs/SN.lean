module

public import LakeJs.Progress

@[expose] public section

/-!
# Strong normalisation, and what an answer cannot do

This module is the elementary half of the totality proof: the definitions and the facts
about them that need no logical relation.

* `Term.SN t` — **`t` runs out of steps**: every reduction sequence from `t` is finite.
  It is `Acc` of the step relation read backwards, so a proof of it is exactly what a
  Lean function may recurse on — which is how `LakeJs.TermTotal` gets a *fuel-free*
  evaluator.
* An answer is a normal form (`Step.not_value`): nothing the evaluator is done with can
  take another step.  This is what makes `Value` a sensible notion of *the* result.
* A term that runs out of steps **reaches an answer** (`Term.SN.halts`): progress says a
  closed term is an answer or steps, so the normal form at the end of a finite reduction
  is an answer rather than a stuck term.
* The fields of a constructor that runs out of steps run out of steps
  (`Term.SN.ctor_spine`) — which is what a field read needs, since reading a field of a
  constructor takes the field out from under the constructor.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Many steps -/

/-- One step, as many steps. -/
theorem Steps.single {Γ : Ctx} {τ : Ty} {t u : Term Sg Γ τ} (h : Step t u) :
    Steps t u := .tail .refl h

/-- A reduction may be read from the front. -/
theorem Steps.head {Γ : Ctx} {τ : Ty} {t u w : Term Sg Γ τ}
    (h : Step t u) (hs : Steps u w) : Steps t w :=
  Steps.trans (Steps.single h) hs

/-- A reduction either does nothing or begins with a step. -/
theorem Steps.cases_head {Γ : Ctx} {τ : Ty} {t w : Term Sg Γ τ} (h : Steps t w) :
    t = w ∨ ∃ u, Step t u ∧ Steps u w := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hsteps hstep ih =>
      rcases ih with rfl | ⟨u, hu, hus⟩
      · exact Or.inr ⟨_, hstep, .refl⟩
      · exact Or.inr ⟨u, hu, .tail hus hstep⟩

/-! ## An answer is a normal form -/

/-- The shapes a neutral term can have.  A `Term.lam`, a literal and a delayed value are
    answers in their own right rather than terms waiting for something, and this is what
    says so — by computation, which is what a proof needs when the *type* of the term
    (`Ty.arrows` for a function of the runtime) is not a constructor application. -/
def Term.neutralShape {Γ : Ctx} {τ : Ty} : Term Sg Γ τ → Bool
  | .var _ | .global _ | .extern _ | .ap _ _ | .proj .. | .tagOf .. | .caseTag ..
  | .ite .. | .lazyForce _ | .block _ => true
  | _ => false

/-- A neutral term has one of those shapes. -/
theorem Neutral.shape {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ} (h : Neutral t) :
    t.neutralShape = true := by
  cases h <;> rfl

/-- A function is not neutral. -/
theorem Neutral.not_lam {Γ : Ctx} {σ τ : Ty} {b : Term Sg (σ :: Γ) τ} :
    ¬ Neutral (Term.lam (Sg := Sg) b) := fun h => by
  simpa [Term.neutralShape] using h.shape

/-- A literal is not neutral. -/
theorem Neutral.not_lit {Γ : Ctx} {p : LeanPrimTy} {l : LeanPrimLit p} :
    ¬ Neutral (Term.lit (Sg := Sg) (Γ := Γ) l) := fun h => by
  simpa [Term.neutralShape] using h.shape

/-- A delayed value is not neutral. -/
theorem Neutral.not_lazyMk {Γ : Ctx} {τ : Ty} {e : Term Sg Γ τ} :
    ¬ Neutral (Term.lazyMk (Sg := Sg) e) := fun h => by
  simpa [Term.neutralShape] using h.shape

/-- What a neutral term says about the subterm it is waiting on, read off the shape of
    the term.  Stating the inversion this way — as a predicate the term *computes* —
    is what lets it be proved by a case analysis on the neutral judgement, which is the
    only direction a case analysis goes when the type of a term (`Ty.arrows`, for a
    function of the runtime) is not a constructor application. -/
def Term.neutralInner {Γ : Ctx} {τ : Ty} : Term Sg Γ τ → Prop
  | .ap f a => Neutral f ∧ Value a ∧ ¬ DeltaRedex (.ap f a)
  | .proj e _ _ _ _ => Neutral e
  | .tagOf e _ => Neutral e
  | .caseTag e _ _ => Neutral e
  | .ite c _ _ => Neutral c
  | .lazyForce e => Neutral e
  | .block b => TailNeutral b
  | _ => True

/-- A neutral term is waiting on a neutral subterm. -/
theorem Neutral.inner {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ} (h : Neutral t) :
    t.neutralInner := by
  cases h with
  | var _ => trivial
  | global _ => trivial
  | extern _ _ => trivial
  | ap hf hv hd => exact ⟨hf, hv, hd⟩
  | proj _ _ _ _ he => exact he
  | tagOf _ he => exact he
  | caseTag _ he => exact he
  | ite hc => exact hc
  | lazyForce he => exact he
  | block hb => exact hb

/-- **A neutral term is not a δ-redex**: it waits for something outside the language,
    and a function of the runtime saturated by literals does not. -/
theorem Neutral.not_delta {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ} (hn : Neutral t) :
    ¬ DeltaRedex t := by
  cases hn with
  | var _ => intro hd; cases hd
  | global _ => intro hd; cases hd
  | extern _ h => exact h
  | ap _ _ hd => exact hd
  | proj _ _ _ _ _ => intro hd; cases hd
  | tagOf _ _ => intro hd; cases hd
  | caseTag _ _ => intro hd; cases hd
  | ite _ => intro hd; cases hd
  | lazyForce _ => intro hd; cases hd
  | block _ => intro hd; cases hd

mutual

/-- **An answer cannot step.**  A term the evaluator is done with is done with. -/
theorem Step.not_value {Γ : Ctx} :
    ∀ {τ : Ty} {t t' : Term Sg Γ τ}, Step t t' → Value t → False
  | _, _, _, .beta _, hv => by
      cases hv with | neutral hn => cases hn with | ap hf => exact Neutral.not_lam hf
  -- `LeanInitPureExternLazy` has no entry today — the constants of the host are
  -- commented out of the catalogue — so this rule has no instance at all.
  | _, _, _, .deltaConst e, _ => nomatch e
  | _, _, _, .deltaPrim1 e l, hv => by
      cases hv with | neutral hn => exact hn.not_delta (.prim1 e l)
  | _, _, _, .deltaPrim2 e l1 l2, hv => by
      cases hv with | neutral hn => exact hn.not_delta (.prim2 e l1 l2)
  | _, _, _, .deltaPrim3 e l1 l2 l3, hv => by
      cases hv with | neutral hn => exact hn.not_delta (.prim3 e l1 l2 l3)
  | _, _, _, .deltaPrim5 e l1 l2 l3 l4 l5, hv => by
      cases hv with | neutral hn => exact hn.not_delta (.prim5 e l1 l2 l3 l4 l5)
  | _, _, _, .quick, hv => by
      cases hv with | neutral hn => exact hn.not_delta .quick
  | _, _, _, .apFun hst, hv => by
      cases hv with | neutral hn => cases hn with | ap hf => exact hst.not_value (.neutral hf)
  | _, _, _, .apArg _ hst, hv => by
      cases hv with | neutral hn => cases hn with | ap _ hva => exact hst.not_value hva
  | _, _, _, .letV _, hv => by cases hv with | neutral hn => cases hn
  | _, _, _, .letStep _, hv => by cases hv with | neutral hn => cases hn
  | _, _, _, .iteTrue, hv => by
      cases hv with | neutral hn => cases hn with | ite hc => exact Neutral.not_lit hc
  | _, _, _, .iteFalse, hv => by
      cases hv with | neutral hn => cases hn with | ite hc => exact Neutral.not_lit hc
  | _, _, _, .iteCond hst, hv => by
      cases hv with
      | neutral hn => cases hn with | ite hc => exact hst.not_value (.neutral hc)
  | _, _, _, .force, hv => by
      cases hv with
      | neutral hn => cases hn with | lazyForce he => exact Neutral.not_lazyMk he
  | _, _, _, .forceStep hst, hv => by
      cases hv with
      | neutral hn => cases hn with | lazyForce he => exact hst.not_value (.neutral he)
  | _, _, _, .projCtor _, hv => by
      cases hv with | neutral hn => cases hn with | proj _ _ _ _ he => cases he
  | _, _, _, .projStep hst, hv => by
      cases hv with
      | neutral hn => cases hn with | proj _ _ _ _ he => exact hst.not_value (.neutral he)
  | _, _, _, .tagOfCtor, hv => by
      cases hv with | neutral hn => exact not_neutral_ctor hn.inner
  | _, _, _, .tagOfBool, hv => by
      cases hv with | neutral hn => exact Neutral.not_lit hn.inner
  | _, _, _, .tagOfStep hst, hv => by
      cases hv with | neutral hn => exact hst.not_value (.neutral hn.inner)
  | _, _, _, .caseCtor, hv => by
      cases hv with | neutral hn => cases hn with | caseTag _ he => cases he
  | _, _, _, .caseBool, hv => by
      cases hv with | neutral hn => cases hn with | caseTag _ he => exact Neutral.not_lit he
  | _, _, _, .caseStep hst, hv => by
      cases hv with
      | neutral hn => cases hn with | caseTag _ he => exact hst.not_value (.neutral he)
  | _, _, _, .ctorBool, hv => by
      cases hv with
      | ctor _ _ _ hb _ => exact hb rfl
      | neutral hn => exact not_neutral_ctor hn
  | _, _, _, .ctorStep hss, hv => by
      cases hv with
      | ctor _ _ _ _ hsv => exact hss.not_spineValue hsv
      | neutral hn => exact not_neutral_ctor hn
  | _, _, _, .blockRet, hv => by
      cases hv with | neutral hn => cases hn with | block htn => cases htn
  | _, _, _, .blockStep hst, hv => by
      cases hv with | neutral hn => cases hn with | block htn => exact hst.not_tailNeutral htn

/-- **A tail the evaluator is stuck on cannot step.** -/
theorem StepT.not_tailNeutral {Γ : Ctx} :
    ∀ {τ : Ty} {b b' : Tail Sg Γ [] τ}, StepT b b' → TailNeutral b → False
  | _, _, _, .retStep _, htn => by cases htn
  | _, _, _, .letV _, htn => by cases htn
  | _, _, _, .letStep _, htn => by cases htn
  | _, _, _, .iteTrue, htn => by cases htn with | iteT hc => exact Neutral.not_lit hc
  | _, _, _, .iteFalse, htn => by cases htn with | iteT hc => exact Neutral.not_lit hc
  | _, _, _, .iteCond hst, htn => by
      cases htn with | iteT hc => exact hst.not_value (.neutral hc)
  | _, _, _, .caseCtor, htn => by
      cases htn with | caseT _ he => exact not_neutral_ctor he
  | _, _, _, .caseBool, htn => by
      cases htn with | caseT _ he => exact Neutral.not_lit he
  | _, _, _, .caseStep hst, htn => by
      cases htn with | caseT _ he => exact hst.not_value (.neutral he)
  | _, _, _, .labelJoin, htn => by cases htn
  | _, _, _, .labelLoop, htn => by cases htn

/-- **A spine of answers cannot step.** -/
theorem SpineStep.not_spineValue {Γ : Ctx} :
    ∀ {σs : List Ty} {s s' : Spine Sg Γ σs}, SpineStep s s' → SpineValue s → False
  | _, _, _, .head hst, hsv => by cases hsv with | cons hv _ => exact hst.not_value hv
  | _, _, _, .tail _ hss, hsv => by
      cases hsv with | cons _ hrest => exact hss.not_spineValue hrest

end

/-- An answer takes no step. -/
theorem Value.not_step {Γ : Ctx} {τ : Ty} {t t' : Term Sg Γ τ} (hv : Value t)
    (hs : Step t t') : False := hs.not_value hv

/-- A neutral term takes no step. -/
theorem Neutral.not_step {Γ : Ctx} {τ : Ty} {t t' : Term Sg Γ τ} (hn : Neutral t)
    (hs : Step t t') : False := hs.not_value (.neutral hn)

/-! ## Strong normalisation -/

/-- **`t` runs out of steps**: the step relation, read backwards, is well-founded below
    `t`.  Every reduction sequence from `t` is finite, and a Lean function may recurse
    on a proof of this — which is what makes a fuel-free evaluator possible. -/
def Term.SN {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Prop :=
  Acc (fun u t' => Step t' u) t

/-- What `t` steps to also runs out of steps. -/
theorem Term.SN.step {Γ : Ctx} {τ : Ty} {t t' : Term Sg Γ τ} (h : t.SN)
    (hs : Step t t') : t'.SN :=
  h.inv hs

/-- If everything `t` steps to runs out of steps, so does `t`. -/
theorem Term.SN.intro {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ}
    (h : ∀ t', Step t t' → t'.SN) : t.SN :=
  Acc.intro t h

/-- What `t` reaches also runs out of steps. -/
theorem Term.SN.steps {Γ : Ctx} {τ : Ty} {t t' : Term Sg Γ τ} (h : t.SN)
    (hs : Steps t t') : t'.SN := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact ih.step hstep

/-- **An answer runs out of steps**, having none to take. -/
theorem Value.sn {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ} (hv : Value t) : t.SN :=
  .intro (fun _ hs => absurd hs (fun h => hv.not_step h))

/-- **A subterm that a step-preserving context keeps runs out of steps too.**  If every
    step of `a` is a step of `f a`, and `f a` runs out of steps, then so does `a`. -/
theorem Term.SN.of_map {Γ Γ' : Ctx} {τ τ' : Ty}
    (f : Term Sg Γ τ → Term Sg Γ' τ')
    (hf : ∀ {a a' : Term Sg Γ τ}, Step a a' → Step (f a) (f a')) :
    ∀ {u : Term Sg Γ' τ'}, u.SN → ∀ {a : Term Sg Γ τ}, u = f a → a.SN := by
  intro u hu
  induction hu with
  | intro _ _ ih =>
      rintro a rfl
      exact .intro fun a' hst => ih (f a') (hf hst) rfl

/-! ## Running out of steps means reaching an answer

Progress (`Term.progress`) says a closed term is an answer or takes a step; so a closed
term that runs out of steps ends at an answer. -/

/-- **A closed term that runs out of steps reaches an answer.** -/
theorem Term.SN.halts {τ : Ty} {t : Term Sg [] τ} (h : t.SN) :
    ∃ v : Term Sg [] τ, Steps t v ∧ Value v := by
  induction h with
  | intro t _ ih =>
      rcases Term.progress t with hv | ⟨t', hstep⟩
      · exact ⟨t, .refl, hv⟩
      · obtain ⟨v, hsteps, hv⟩ := ih t' hstep
        exact ⟨v, Steps.head hstep hsteps, hv⟩

/-! ## The fields of a constructor -/

/-- A context that preserves steps preserves running out of them.  This is the general
    form of `Term.SN.of_map`, used below for a spine inside a constructor. -/
theorem acc_of_map {α β : Type} {ra : α → α → Prop} {rb : β → β → Prop}
    (f : α → β) (hf : ∀ {x y : α}, ra x y → rb (f x) (f y)) :
    ∀ {b : β}, Acc rb b → ∀ {a : α}, b = f a → Acc ra a := by
  intro b hb
  induction hb with
  | intro _ _ ih => rintro a rfl; exact .intro _ fun x hx => ih (f x) (hf hx) rfl

/-- **The spine runs out of steps**: no infinite sequence of steps inside it. -/
def SpineSNAcc {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs) : Prop :=
  Acc (fun u t => SpineStep t u) s

/-- Every term of the spine runs out of steps. -/
def SpineSN {Γ : Ctx} : ∀ {σs : List Ty}, Spine Sg Γ σs → Prop
  | [], _ => True
  | _ :: _, .cons t rest => t.SN ∧ SpineSN rest

/-- Reducing the first term of a spine reduces the spine. -/
theorem SpineSNAcc.head_steps {Γ : Ctx} {σ : Ty} {σs : List Ty} {t t' : Term Sg Γ σ}
    {rest : Spine Sg Γ σs} (h : SpineSNAcc (.cons t rest)) (hs : Steps t t') :
    SpineSNAcc (.cons t' rest) := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact ih.inv (.head hstep)

/-- **The spine of a constructor that runs out of steps runs out of steps.** -/
theorem Term.SN.ctor_acc {Γ : Ctx} {τ : Ty} {i : Nat} {fs : Layout.FieldLayout}
    {h : τ.ctorFields? i = some fs} {args : Spine Sg Γ fs}
    (hsn : (Term.ctor i fs h args).SN) : SpineSNAcc args :=
  acc_of_map (ra := fun u t => SpineStep t u) (rb := fun u t => Step t u)
    (fun s => Term.ctor i fs h s) (fun hx => .ctorStep hx) hsn rfl

/-- **A spine that runs out of steps does so term by term.** -/
theorem SpineSNAcc.elems :
    ∀ {σs : List Ty} {args : Spine Sg [] σs}, SpineSNAcc args → SpineSN args
  | [], .nil, _ => trivial
  | _ :: _, .cons t rest, hacc => by
      have ht : t.SN :=
        acc_of_map (ra := fun u t' => Step t' u) (rb := fun u t' => SpineStep t' u)
          (fun x => Spine.cons x rest) (fun hx => .head hx) hacc rfl
      refine ⟨ht, ?_⟩
      obtain ⟨v, hsv, hv⟩ := ht.halts
      have hacc' : SpineSNAcc (Spine.cons v rest) := hacc.head_steps hsv
      have hrest : SpineSNAcc rest :=
        acc_of_map (ra := fun u t' => SpineStep t' u) (rb := fun u t' => SpineStep t' u)
          (fun r => Spine.cons v r) (fun hx => .tail hv hx) hacc' rfl
      exact SpineSNAcc.elems hrest

/-- **The fields of a constructor that runs out of steps run out of steps.** -/
theorem Term.SN.ctor_spine {τ : Ty} {i : Nat} {fs : Layout.FieldLayout}
    {h : τ.ctorFields? i = some fs} {args : Spine Sg [] fs}
    (hsn : (Term.ctor i fs h args).SN) : SpineSN args :=
  hsn.ctor_acc.elems

/-- Reading a field of a spine that runs out of steps runs out of steps. -/
theorem SpineSN.get? {σs : List Ty} :
    ∀ {args : Spine Sg [] σs}, SpineSN args → ∀ (j : Nat) {τ : Ty}
      (hg : σs[j]? = some τ), (args.get? j hg).SN
  | .cons t _, h, 0, _, hg => by
      simp only [Spine.get?]
      cases hg
      exact h.1
  | .cons _ rest, h, j + 1, _, hg => SpineSN.get? h.2 j (by simpa using hg)

/-- **A spine whose terms run out of steps runs out of steps.** -/
theorem SpineSNAcc.cons {σ : Ty} {σs : List Ty} :
    ∀ {t : Term Sg [] σ}, t.SN →
      ∀ (rest : Spine Sg [] σs), SpineSNAcc rest → SpineSNAcc (.cons t rest) := by
  intro t ht
  induction ht with
  | intro t _ iht =>
      intro rest hr
      induction hr with
      | intro rest hrest ihr =>
          refine Acc.intro _ fun s hs => ?_
          cases hs with
          | head hst => exact iht _ hst rest (Acc.intro rest hrest)
          | tail _ hss => exact ihr _ hss

/-- The converse of `SpineSNAcc.elems`. -/
theorem SpineSN.acc :
    ∀ {σs : List Ty} {args : Spine Sg [] σs}, SpineSN args → SpineSNAcc args
  | [], .nil, _ => Acc.intro _ (fun _ hs => nomatch hs)
  | _ :: _, .cons _ rest, h => SpineSNAcc.cons h.1 rest (SpineSN.acc h.2)

/-- **A constructor whose fields run out of steps runs out of steps.** -/
theorem SpineSNAcc.ctor_sn {τ : Ty} {i : Nat} {fs : Layout.FieldLayout}
    {h : τ.ctorFields? i = some fs} {args : Spine Sg [] fs} :
    SpineSNAcc args → (Term.ctor i fs h args).SN := by
  intro hacc
  induction hacc with
  | intro args _ ih =>
      refine .intro fun t' hst => ?_
      cases hst with
      | ctorBool => exact (Value.lit _).sn
      | ctorStep hss => exact ih _ hss

/-- **A tag test of a term that runs out of steps runs out of steps.** -/
theorem Term.SN.tagOf {σ : Ty} {e : Term Sg [] σ} {h : σ.isTagged = true} :
    e.SN → (Term.tagOf e h).SN := by
  intro hsn
  induction hsn with
  | intro e _ ihacc =>
      refine .intro fun t' hst => ?_
      cases hst with
      | tagOfCtor => exact (Value.lit _).sn
      | tagOfBool => exact (Value.lit _).sn
      | tagOfStep hste => exact ihacc _ hste

/-- **A field read of a term that runs out of steps runs out of steps.**  The field a
    read takes out from under a constructor runs out of steps by
    `Term.SN.ctor_spine`. -/
theorem Term.SN.proj {σ τ : Ty} {e : Term Sg [] σ} {i j : Nat}
    {hOne : σ.numCtors? = some 1} {h : σ.fieldTy? i j = some τ} :
    e.SN → (Term.proj e i j hOne h).SN := by
  intro hsn
  induction hsn with
  | intro e hacc ihacc =>
      refine .intro fun t' hst => ?_
      cases hst with
      | projCtor hg => exact (Term.SN.ctor_spine (Acc.intro _ hacc)).get? _ hg
      | projStep hste => exact ihacc _ hste

end LakeJs.Expr

end
