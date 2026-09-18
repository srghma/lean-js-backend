module

public import LakeJs.Fragment
public import LakeJs.SubstLemmas

@[expose] public section

/-!
# Reducibility: why a closed term of the fragment runs out of steps

This is the logical-relation (Tait) argument.  `Red τ t` — *`t` is reducible at `τ`* —
says that `t` runs out of steps **and** that every answer it reaches is reducible as an
answer (`RedV`), where an answer of

* a **function** type is one that sends reducible arguments to reducible results;
* a **delayed** type is one whose body is reducible;
* a **value** type (`Ty.ground`: anything else) is any answer at all.

`RedV` is defined by recursion on the type, which is what makes the argument go through
where induction on the term does not: β puts an argument *inside* a body, so the term
gets bigger, but the type of the function it came from gets smaller.

The two halves are then:

* the closure properties of `Red` — it is preserved by a step, it is *created* by a step
  backwards (`Red.expand`), a neutral term is reducible (`Red.neutral`), and each
  construct of the language preserves reducibility (`Red.app`, `Red.lam`, `Red.letE`,
  `Red.ite`, `Red.lazyMk`, `Red.lazyForce`, `Red.ctor`, `Red.proj`, `Red.tagOf`,
  `Red.caseTag`);
* the **fundamental theorem** `Term.fundamental`: a term of the fragment is reducible
  under any reducible substitution — in particular a closed one is reducible, and
  therefore runs out of steps.
-/

namespace LakeJs

/-- How much of a type the logical relation looks at: a function type and a delayed type
    are the two it takes apart. -/
def Ty.redDepth : Ty → Nat
  | .fn σ τ => σ.redDepth + τ.redDepth + 1
  | .primCovariant (.lazy τ) => τ.redDepth + 1
  | _ => 0

namespace Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## The relation -/

/-- **A reducible answer.**  At a function type, one that answers reducibly on every
    reducible argument; at a delayed type, one whose body is reducible; at a value type,
    any answer.  `Red` below is the companion for terms that are not yet answers; the two
    are written out together because `RedV` is defined by recursion on the type and `Red`
    is not recursive at all. -/
def RedV {Sg : Sig} : (τ : Ty) → Term Sg [] τ → Prop
  | .fn σ τ, v => ∀ a : Term Sg [] σ,
      (a.SN ∧ ∀ w, Steps a w → Value w → RedV σ w) →
      ((Term.ap v a).SN ∧ ∀ w, Steps (Term.ap v a) w → Value w → RedV τ w)
  | .primCovariant (.lazy τ), v => ∀ e : Term Sg [] τ,
      v = .lazyMk e → (e.SN ∧ ∀ w, Steps e w → Value w → RedV τ w)
  | _, _ => True
  termination_by τ => τ.redDepth
  decreasing_by all_goals (simp [Ty.redDepth]; try omega)

/-- **A reducible term**: it runs out of steps, and every answer it reaches is a
    reducible answer. -/
def Red {Sg : Sig} (τ : Ty) (t : Term Sg [] τ) : Prop :=
  t.SN ∧ ∀ w, Steps t w → Value w → RedV τ w

/-- At a function type, reducibility of an answer is what it should be. -/
theorem RedV_fn {σ τ : Ty} {v : Term Sg [] (σ ⇒ τ)} :
    RedV (σ ⇒ τ) v ↔ ∀ a : Term Sg [] σ, Red σ a → Red τ (.ap v a) := by
  simp only [RedV, Red]

/-- At a delayed type, reducibility of an answer is reducibility of what it delays. -/
theorem RedV_lazy {τ : Ty} {v : Term Sg [] (Ty.lazy τ)} :
    RedV (Ty.lazy τ) v ↔ ∀ e : Term Sg [] τ, v = .lazyMk e → Red τ e := by
  simp only [RedV, Red]

/-- At a value type there is nothing to ask of an answer. -/
theorem RedV.ground {τ : Ty} (h : τ.ground = true) (v : Term Sg [] τ) : RedV τ v := by
  cases τ with
  | fn _ _ => exact absurd h (by simp [Ty.ground])
  | primCovariant c =>
      cases c with
      | lazy _ => exact absurd h (by simp [Ty.ground])
      | array _ => simp [RedV]
      | list _ => simp [RedV]
      | task _ => simp [RedV]
      | promise _ => simp [RedV]
      | thunk _ => simp [RedV]
  | prim _ => simp [RedV]
  | enum _ => simp [RedV]
  | record _ => simp [RedV]
  | taggedUnion _ => simp [RedV]
  | recTaggedUnion _ _ => simp [RedV]
  | recObject _ _ => simp [RedV]
  | recAlias _ _ => simp [RedV]
  | mutualRecursiveFamily _ _ => simp [RedV]

/-! ## The closure properties -/

/-- A reducible term runs out of steps. -/
theorem Red.sn {τ : Ty} {t : Term Sg [] τ} (h : Red τ t) : t.SN := h.1

/-- An answer a reducible term reaches is a reducible answer. -/
theorem Red.redv {τ : Ty} {t v : Term Sg [] τ} (h : Red τ t) (hs : Steps t v)
    (hv : Value v) : RedV τ v := h.2 v hs hv

/-- **A reducible answer is a reducible term.** -/
theorem Red.val {τ : Ty} {v : Term Sg [] τ} (hv : Value v) (h : RedV τ v) : Red τ v :=
  ⟨hv.sn, fun w hs hw => by
    rcases Steps.cases_head hs with rfl | ⟨u, hstep, _⟩
    · exact h
    · exact absurd hstep (fun hst => hv.not_step hst)⟩

/-- At a value type, running out of steps is all reducibility asks. -/
theorem Red.of_ground {τ : Ty} {t : Term Sg [] τ} (hg : τ.ground = true) (hsn : t.SN) :
    Red τ t := ⟨hsn, fun w _ _ => RedV.ground hg w⟩

/-- **Reducibility is preserved by a step.** -/
theorem Red.step {τ : Ty} {t t' : Term Sg [] τ} (h : Red τ t) (hs : Step t t') :
    Red τ t' := ⟨h.sn.step hs, fun w hsteps hw => h.2 w (Steps.head hs hsteps) hw⟩

/-- **Reducibility is created by a step backwards.**  A term that is not itself an
    answer is reducible as soon as everything it steps to is. -/
theorem Red.expand {τ : Ty} {t : Term Sg [] τ} (hnv : ¬ Value t)
    (h : ∀ t', Step t t' → Red τ t') : Red τ t := by
  refine ⟨.intro fun t' hst => (h t' hst).sn, fun w hs hw => ?_⟩
  rcases Steps.cases_head hs with rfl | ⟨u, hstep, hus⟩
  · exact absurd hw hnv
  · exact (h u hstep).2 w hus hw

/-! ## A neutral term is reducible

The one place the recursion on the type is doing work: an application of a neutral term
is neutral again, or it is a function of the runtime running on literals — and then it
answers with a literal, at a value type. -/

/-- **A neutral term is a reducible answer**, at every type. -/
theorem RedV.neutral : ∀ (τ : Ty) {v : Term Sg [] τ}, Neutral v → RedV τ v
  | .fn σ τ, v, hn => by
      rw [RedV_fn]
      have key : ∀ a : Term Sg [] σ, a.SN → Red σ a → Red τ (.ap v a) := by
        intro a hsn
        induction hsn with
        | intro a _ ihacc =>
            intro ha
            by_cases hva : Value (Term.ap v a)
            · exact Red.val hva
                (RedV.neutral τ (by cases hva with | neutral h => exact h))
            · refine Red.expand hva fun t' hst => ?_
              cases hst with
              | beta _ => exact absurd hn Neutral.not_lam
              | apFun hstf => exact absurd hstf (fun h => hn.not_step h)
              | apArg _ hsta => exact ihacc _ hsta (ha.step hsta)
              | deltaPrim1 _ _ => exact Red.of_ground rfl (Value.lit _).sn
              | deltaPrim2 _ _ _ => exact Red.of_ground rfl (Value.lit _).sn
              | deltaPrim3 _ _ _ _ => exact Red.of_ground rfl (Value.lit _).sn
              | deltaPrim5 _ _ _ _ _ _ => exact Red.of_ground rfl (Value.lit _).sn
              | quick => exact ha
      exact fun a ha => key a ha.sn ha
  | .primCovariant (.lazy τ), v, hn => by
      rw [RedV_lazy]
      intro e heq
      exact absurd (heq ▸ hn) Neutral.not_lazyMk
  | .prim _, _, _ => RedV.ground rfl _
  | .primCovariant (.array _), _, _ => RedV.ground rfl _
  | .primCovariant (.list _), _, _ => RedV.ground rfl _
  | .primCovariant (.task _), _, _ => RedV.ground rfl _
  | .primCovariant (.promise _), _, _ => RedV.ground rfl _
  | .primCovariant (.thunk _), _, _ => RedV.ground rfl _
  | .enum _, _, _ => RedV.ground rfl _
  | .record _, _, _ => RedV.ground rfl _
  | .taggedUnion _, _, _ => RedV.ground rfl _
  | .recObject _ _, _, _ => RedV.ground rfl _
  | .recTaggedUnion _ _, _, _ => RedV.ground rfl _
  | .recAlias _ _, _, _ => RedV.ground rfl _
  | .mutualRecursiveFamily _ _, _, _ => RedV.ground rfl _
  termination_by τ => τ.redDepth
  decreasing_by all_goals (simp [Ty.redDepth]; try omega)

/-- **A neutral term is reducible.** -/
theorem Red.neutral {τ : Ty} {t : Term Sg [] τ} (hn : Neutral t) : Red τ t :=
  Red.val (.neutral hn) (RedV.neutral τ hn)

/-! ## Each construct preserves reducibility

One lemma per construct of the fragment.  They all have the same shape: either the term
is already an answer, and reducibility of the answer is what has to be shown, or it is
not, and `Red.expand` reduces the claim to reducibility of everything it steps to — which
is a case analysis on the step relation, with the induction hypothesis for the congruence
rules and the hypothesis of the lemma for the rules that do work. -/

/-- **A function is reducible when its body is**, on every reducible answer. -/
theorem Red.lam {σ τ : Ty} {b : Term Sg [σ] τ}
    (h : ∀ a : Term Sg [] σ, Value a → Red σ a → Red τ (b.subst0 a)) :
    Red (σ ⇒ τ) (.lam b) := by
  refine Red.val (Value.lam b) (RedV_fn.mpr ?_)
  have key : ∀ a : Term Sg [] σ, a.SN → Red σ a → Red τ (.ap (Term.lam b) a) := by
    intro a hsn
    induction hsn with
    | intro a _ ihacc =>
        intro ha
        refine Red.expand ?_ ?_
        · intro hv
          cases hv with
          | neutral hn => cases hn with | ap hf _ _ => exact Neutral.not_lam hf
        · intro t' hst
          cases hst with
          | beta hva => exact h a hva ha
          | apFun hstf => exact absurd hstf (fun hs => (Value.lam b).not_step hs)
          | apArg _ hsta => exact ihacc _ hsta (ha.step hsta)
  exact fun a ha => key a ha.sn ha

/-- **An application of reducible terms is reducible.**  The β case is where the work
    happens: the function is an answer at a function type, so it is a reducible answer,
    and that is precisely the statement that it answers reducibly here. -/
theorem Red.app {σ τ : Ty} {f : Term Sg [] (σ ⇒ τ)} {a : Term Sg [] σ}
    (hf : Red (σ ⇒ τ) f) (ha : Red σ a) : Red τ (.ap f a) := by
  have key : ∀ f : Term Sg [] (σ ⇒ τ), f.SN → ∀ a : Term Sg [] σ, a.SN →
      Red (σ ⇒ τ) f → Red σ a → Red τ (.ap f a) := by
    intro f hfsn
    induction hfsn with
    | intro f _ ihf =>
        intro a hasn
        induction hasn with
        | intro a _ iha =>
            intro hf ha
            by_cases hv : Value (Term.ap f a)
            · exact Red.val hv (RedV.neutral τ (by cases hv with | neutral hn => exact hn))
            · refine Red.expand hv fun t' hst => ?_
              cases hst with
              | beta hva =>
                  exact Red.step (RedV_fn.mp (hf.redv .refl (Value.lam _)) a ha) (.beta hva)
              | apFun hstf => exact ihf _ hstf a ha.sn (hf.step hstf) ha
              | apArg _ hsta => exact iha _ hsta hf (ha.step hsta)
              | deltaPrim1 _ _ => exact Red.of_ground rfl (Value.lit _).sn
              | deltaPrim2 _ _ _ => exact Red.of_ground rfl (Value.lit _).sn
              | deltaPrim3 _ _ _ _ => exact Red.of_ground rfl (Value.lit _).sn
              | deltaPrim5 _ _ _ _ _ _ => exact Red.of_ground rfl (Value.lit _).sn
              | quick => exact ha
  exact key f hf.sn a ha.sn hf ha

/-- **A `let` is reducible when what it binds is and its body is**, on every reducible
    answer. -/
theorem Red.letE {σ τ : Ty} {e : Term Sg [] σ} {b : Term Sg [σ] τ}
    (he : Red σ e)
    (hb : ∀ a : Term Sg [] σ, Value a → Red σ a → Red τ (b.subst0 a)) :
    Red τ (.letE e b) := by
  have key : ∀ e : Term Sg [] σ, e.SN → Red σ e → Red τ (Term.letE e b) := by
    intro e hsn
    induction hsn with
    | intro e _ ih =>
        intro he
        refine Red.expand ?_ ?_
        · intro hv; cases hv with | neutral hn => cases hn
        · intro t' hst
          cases hst with
          | letV hve => exact hb e hve he
          | letStep hste => exact ih _ hste (he.step hste)
  exact key e he.sn he

/-- **A two-way branch of reducible terms is reducible.** -/
theorem Red.ite {τ : Ty} {c : Term Sg [] (.prim .bool)} {t e : Term Sg [] τ}
    (hc : Red (.prim .bool) c) (ht : Red τ t) (he : Red τ e) : Red τ (.ite c t e) := by
  have key : ∀ c : Term Sg [] (.prim .bool), c.SN → Red (.prim .bool) c →
      Red τ (Term.ite c t e) := by
    intro c hsn
    induction hsn with
    | intro c _ ih =>
        intro hc
        by_cases hv : Value (Term.ite c t e)
        · exact Red.val hv (RedV.neutral τ (by cases hv with | neutral hn => exact hn))
        · refine Red.expand hv fun t' hst => ?_
          cases hst with
          | iteTrue => exact ht
          | iteFalse => exact he
          | iteCond hstc => exact ih _ hstc (hc.step hstc)
  exact key c hc.sn hc

/-- **A delayed reducible term is reducible.** -/
theorem Red.lazyMk {τ : Ty} {e : Term Sg [] τ} (he : Red τ e) :
    Red (Ty.lazy τ) (.lazyMk e) := by
  refine Red.val (Value.lazyMk e) (RedV_lazy.mpr ?_)
  intro e' heq
  simp only [Term.lazyMk.injEq] at heq
  exact heq ▸ he

/-- **Running a reducible delayed value is reducible.** -/
theorem Red.lazyForce {τ : Ty} {le : Term Sg [] (Ty.lazy τ)} (h : Red (Ty.lazy τ) le) :
    Red τ (.lazyForce le) := by
  have key : ∀ le : Term Sg [] (Ty.lazy τ), le.SN → Red (Ty.lazy τ) le →
      Red τ (Term.lazyForce le) := by
    intro le hsn
    induction hsn with
    | intro le _ ih =>
        intro h
        by_cases hv : Value (Term.lazyForce le)
        · exact Red.val hv (RedV.neutral τ (by cases hv with | neutral hn => exact hn))
        · refine Red.expand hv fun t' hst => ?_
          cases hst with
          | force => exact RedV_lazy.mp (h.redv .refl (Value.lazyMk _)) _ rfl
          | forceStep hste => exact ih _ hste (h.step hste)
  exact key le h.sn h

/-! ## Constructors, field reads, tag tests and dispatches -/

/-- Every term of a spine is reducible. -/
def SpineRed : ∀ {σs : List Ty}, Spine Sg [] σs → Prop
  | [], _ => True
  | σ :: _, .cons t rest => Red σ t ∧ SpineRed rest

/-- A reducible spine runs out of steps term by term. -/
theorem SpineRed.sn :
    ∀ {σs : List Ty} {args : Spine Sg [] σs}, SpineRed args → SpineSN args
  | [], .nil, _ => trivial
  | _ :: _, .cons _ _, h => ⟨h.1.sn, SpineRed.sn h.2⟩

/-- **A constructor of reducible fields is reducible.**  A type with a constructor is a
    value type, so there is nothing to show beyond running out of steps. -/
theorem Red.ctor {τ : Ty} {i : Nat} {fs : Layout.FieldLayout}
    {h : τ.ctorFields? i = some fs} {args : Spine Sg [] fs} (hargs : SpineRed args) :
    Red τ (.ctor i fs h args) :=
  Red.of_ground (Ty.ground_of_ctorFields? h) (SpineSNAcc.ctor_sn (SpineSN.acc hargs.sn))

/-- **A tag test of a reducible term is reducible**: it answers with a number. -/
theorem Red.tagOf {σ : Ty} {e : Term Sg [] σ} {h : σ.isTagged = true} (he : Red σ e) :
    Red (.prim .nat) (.tagOf e h) :=
  Red.of_ground rfl (Term.SN.tagOf he.sn)

/-- **A field read of a reducible term, at a value type, is reducible.**  The restriction
    to a value type is the second of the two the fragment carries; see
    `LakeJs.Fragment`. -/
theorem Red.proj {σ τ : Ty} {e : Term Sg [] σ} {i j : Nat}
    {hOne : σ.numCtors? = some 1} {h : σ.fieldTy? i j = some τ}
    (hg : τ.ground = true) (he : Red σ e) : Red τ (.proj e i j hOne h) :=
  Red.of_ground hg (Term.SN.proj he.sn)

/-- Every branch of a dispatch is reducible. -/
def RedAlts {τ : Ty} :
    ∀ {tags : List Nat} {full : Bool}, Alts Sg [] τ tags full → Prop
  | _, _, .deflt t => Red τ t
  | _, _, .nilFull => True
  | _, _, .cons _ t rest => Red τ t ∧ RedAlts rest

/-- The branch a dispatch with reducible branches takes is reducible. -/
theorem RedAlts.select {τ : Ty} :
    ∀ {tags : List Nat} {full : Bool} {alts : Alts Sg [] τ tags full}, RedAlts alts →
      ∀ (i : Nat) (hcov : full = true → i ∈ tags), Red τ (alts.select i hcov)
  | _, _, .deflt _, h, _, _ => h
  | _, _, .nilFull, _, _, hcov => absurd (hcov rfl) (by simp)
  | _, _, .cons _ _ _, h, i, hcov => by
      simp only [Alts.select]
      split
      · exact h.1
      · exact RedAlts.select h.2 i _

/-- **A dispatch on a reducible term with reducible branches is reducible.** -/
theorem Red.caseTag {σ τ : Ty} {tags : List Nat} {full : Bool} {e : Term Sg [] σ}
    {alts : Alts Sg [] τ tags full} {h : σ.caseOkAlts full tags = true}
    (he : Red σ e) (halts : RedAlts alts) : Red τ (.caseTag e alts h) := by
  have key : ∀ e : Term Sg [] σ, e.SN → Red σ e → Red τ (Term.caseTag e alts h) := by
    intro e hsn
    induction hsn with
    | intro e _ ih =>
        intro he
        by_cases hv : Value (Term.caseTag e alts h)
        · exact Red.val hv (RedV.neutral τ (by cases hv with | neutral hn => exact hn))
        · refine Red.expand hv fun t' hst => ?_
          cases hst with
          | caseCtor => exact halts.select _ _
          | caseBool => exact halts.select _ _
          | caseStep hste => exact ih _ hste (he.step hste)
  exact key e he.sn he

/-! ## Reducible substitutions

A substitution is reducible when it gives every variable a reducible answer.  This is
what the fundamental theorem (`LakeJs.Fundamental`) carries through the term, and what a
block's termination certificate (`LakeJs.Terminating`) quantifies over. -/

/-- **A reducible substitution**: it gives every variable a reducible *answer*.  The
    answer part is what a call-by-value β step puts into the body, so it is what the
    induction has to carry. -/
def RedSub {Γ : Ctx} (γ : VSub Sg Γ []) : Prop :=
  ∀ {σ : Ty} (v : Γ ∋ σ), Value (γ v) ∧ Red σ (γ v)

/-- The empty substitution is reducible: there is no variable to give anything to. -/
theorem RedSub.nil : RedSub (Sg := Sg) (Γ := []) VSub.id := fun v => nomatch v

/-- **Extending a reducible substitution by a reducible answer keeps it reducible.** -/
theorem RedSub.cons {Γ : Ctx} {σ : Ty} {γ : VSub Sg Γ []} {a : Term Sg [] σ}
    (hva : Value a) (ha : Red σ a) (hγ : RedSub γ) : RedSub (VSub.cons a γ) := by
  intro ν v
  match v with
  | .head => exact ⟨hva, ha⟩
  | .tail v => exact hγ v

end Expr

end LakeJs

end
