/-
# The proposed `StackProfile` index, typechecked

This file is the machine-checked part of `TERM_STACK_PROFILE_ASSESSMENT.md`.  It contains
two miniature languages, each a faithful scale model of the relevant fragment of
`LakeJs.Expr.Term` — variables, abstraction, application, a measured recursion, a self
call, and a block with a tail call — and nothing else.  Neither is meant to be used; each
exists so that a claim about the *shape* of an index can be stated as a theorem instead of
asserted in prose.

* `Sketch`  — the index exactly as proposed: `lam` propagates its body's profile, `ap`
  joins, `fixAcc` is unconditionally `deepStack`, `loopJmp` is unconditionally
  `constStack`, and `lift` embeds `constStack` into `deepStack`.

  `Sketch.MTerm.deep_of_hasFix` and `Sketch.MTerm.const_fixFree` say what that index
  actually classifies: **a `constStack` term contains no recursion at all.**  The index is
  sound, and it is empty — it never distinguishes one recursive function from another,
  which is the job it was introduced to do.

* `Latent` — the same language with the profile moved onto the **arrow**, which is where a
  function's stack cost lives, and with `fix` taking the profile of its body as a
  parameter rather than fixing it.

  `Latent.CTerm.deep_of_costly` says that a `constStack` term makes no non-tail self call
  *and* applies no `deepStack` function.  `Latent.countdown` and `Latent.sumdown` are a
  tail recursion typed at `constStack` and a non-tail recursion typed at `deepStack`: the
  distinction the index was wanted for, now expressible.
-/

/-! ## The lattice, shared by both models -/

namespace ExamplesStackProfile

/-- Operational stack footprint, as proposed. -/
inductive SP
  /-- `O(1)` stack. -/
  | const
  /-- May consume stack frames proportional to the measure. -/
  | deep
  deriving DecidableEq, Repr

/-- The join of the two-point lattice `const ≤ deep`. -/
def SP.join : SP → SP → SP
  | .const, .const => .const
  | _, _ => .deep

instance : Max SP := ⟨SP.join⟩

theorem SP.join_eq_deep_left {m : SP} (h : m = SP.deep) (n : SP) : m.join n = SP.deep := by
  cases n <;> subst h <;> rfl

theorem SP.join_eq_deep_right (m : SP) {n : SP} (h : n = SP.deep) : m.join n = SP.deep := by
  cases m <;> subst h <;> rfl

/-! # Model A: the index as proposed -/

namespace Sketch

/-- Simple types: one base type and a curried arrow, with no profile on it. -/
inductive MTy
  | base
  | arr (σ τ : MTy)

abbrev Ctx := List MTy
/-- A recursion context: parameter types and result type of each recursion in scope. -/
abbrev RCtx := List (List MTy × MTy)

inductive Var : Ctx → MTy → Type
  | here : Var (τ :: Γ) τ
  | there : Var Γ τ → Var (σ :: Γ) τ

inductive RVar : RCtx → (List MTy × MTy) → Type
  | here : RVar (e :: Ρ) e
  | there : RVar Ρ e → RVar (f :: Ρ) e

def MTy.arrows : List MTy → MTy → MTy
  | [], τ => τ
  | σ :: σs, τ => .arr σ (arrows σs τ)

mutual

/-- The proposal, transcribed: the profile is an index of the term. -/
inductive MTerm : SP → Ctx → RCtx → MTy → Type
  | var : Var Γ τ → MTerm m Γ Ρ τ
  | lam : MTerm m (σ :: Γ) Ρ τ → MTerm m Γ Ρ (.arr σ τ)
  | ap : MTerm m₁ Γ Ρ (.arr σ τ) → MTerm m₂ Γ Ρ σ → MTerm (m₁.join m₂) Γ Ρ τ
  /-- Subtyping, as proposed: any `constStack` term is usable where `deepStack` is. -/
  | lift : MTerm .const Γ Ρ τ → MTerm .deep Γ Ρ τ
  /-- The measured recursion: its body, and so it, is `deepStack` by construction. -/
  | fixAcc : (ps : List MTy) → (measure : MTerm .const (ps ++ Γ) Ρ .base) →
      (body : MTerm .deep (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) →
      MTerm .deep Γ Ρ (MTy.arrows ps τ)
  /-- A non-tail recursive call: `deepStack`. -/
  | selfCall : RVar Ρ ⟨ps, τ⟩ → MSpine m Γ Ρ ps → MTerm .deep Γ Ρ τ
  | block : MTail m Γ Ρ τ → MTerm m Γ Ρ τ

inductive MTail : SP → Ctx → RCtx → MTy → Type
  | ret : MTerm m Γ Ρ τ → MTail m Γ Ρ τ
  /-- A tail recursive call: `constStack`. -/
  | loopJmp : RVar Ρ ⟨ps, τ⟩ → MSpine .const Γ Ρ ps → MTail .const Γ Ρ τ

inductive MSpine : SP → Ctx → RCtx → List MTy → Type
  | nil : MSpine m Γ Ρ []
  | cons : MTerm m₁ Γ Ρ σ → MSpine m₂ Γ Ρ σs → MSpine (m₁.join m₂) Γ Ρ (σ :: σs)

end

mutual

/-- "A recursion is defined somewhere in here." -/
def MTerm.HasFix : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {τ : MTy}, MTerm m Γ Ρ τ → Prop
  | _, _, _, _, .var _ => False
  | _, _, _, _, .lam b => b.HasFix
  | _, _, _, _, .ap f a => f.HasFix ∨ a.HasFix
  | _, _, _, _, .lift t => t.HasFix
  | _, _, _, _, .fixAcc _ _ _ => True
  | _, _, _, _, .selfCall _ sp => sp.HasFix
  | _, _, _, _, .block t => t.HasFix

def MTail.HasFix : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {τ : MTy}, MTail m Γ Ρ τ → Prop
  | _, _, _, _, .ret t => t.HasFix
  | _, _, _, _, .loopJmp _ sp => sp.HasFix

def MSpine.HasFix : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {σs : List MTy},
    MSpine m Γ Ρ σs → Prop
  | _, _, _, _, .nil => False
  | _, _, _, _, .cons t sp => t.HasFix ∨ sp.HasFix

end

mutual

/-- **Every term that contains a recursion is indexed `deepStack`.**  Sound — and, read in
    the other direction, the whole content of the index. -/
theorem MTerm.deep_of_hasFix : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {τ : MTy}
    (t : MTerm m Γ Ρ τ), t.HasFix → m = SP.deep
  | _, _, _, _, .var _, h => absurd h (by simp [MTerm.HasFix])
  | _, _, _, _, .lam b, h => MTerm.deep_of_hasFix b h
  | _, _, _, _, .ap f a, h => by
      rcases (show f.HasFix ∨ a.HasFix from h) with hf | ha
      · exact SP.join_eq_deep_left (MTerm.deep_of_hasFix f hf) _
      · exact SP.join_eq_deep_right _ (MTerm.deep_of_hasFix a ha)
  | _, _, _, _, .lift _, _ => rfl
  | _, _, _, _, .fixAcc _ _ _, _ => rfl
  | _, _, _, _, .selfCall _ _, _ => rfl
  | _, _, _, _, .block t, h => MTail.deep_of_hasFix t h

theorem MTail.deep_of_hasFix : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {τ : MTy}
    (t : MTail m Γ Ρ τ), t.HasFix → m = SP.deep
  | _, _, _, _, .ret t, h => MTerm.deep_of_hasFix t h
  | _, _, _, _, .loopJmp _ sp, h => SP.noConfusion (MSpine.deep_of_hasFix sp h)

theorem MSpine.deep_of_hasFix : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {σs : List MTy}
    (sp : MSpine m Γ Ρ σs), sp.HasFix → m = SP.deep
  | _, _, _, _, .nil, h => absurd h (by simp [MSpine.HasFix])
  | _, _, _, _, .cons t sp, h => by
      rcases (show t.HasFix ∨ sp.HasFix from h) with ht | hs
      · exact SP.join_eq_deep_left (MTerm.deep_of_hasFix t ht) _
      · exact SP.join_eq_deep_right _ (MSpine.deep_of_hasFix sp hs)

end

/-- **The finding.**  Under the index as proposed, a `constStack` term contains no
    recursion whatsoever.  So the index never separates a tail-recursive function from a
    non-tail-recursive one — every recursion is `deepStack`, including the ones that are
    nothing but a `loopJmp`.  `constStack` means "recursion-free", not "runs in constant
    stack". -/
theorem MTerm.const_fixFree {Γ : Ctx} {Ρ : RCtx} {τ : MTy} (t : MTerm .const Γ Ρ τ) :
    ¬ t.HasFix := fun h => SP.noConfusion (MTerm.deep_of_hasFix t h)

/-- The same for a block: a `constStack` tail defines no recursion either, so the one
    `constStack` recursive construct, `loopJmp`, can only ever occur inside the
    `deepStack` body of a `fixAcc`. -/
theorem MTail.const_fixFree {Γ : Ctx} {Ρ : RCtx} {τ : MTy} (t : MTail .const Γ Ρ τ) :
    ¬ t.HasFix := fun h => SP.noConfusion (MTail.deep_of_hasFix t h)

/-- The index is not unique: `lift` and the profile-polymorphic `var` mean one and the
    same term is typeable at both profiles, so "the profile of a term" is a choice the
    producer makes, not a fact the tree records. -/
def varAtBothProfiles {Γ : Ctx} {Ρ : RCtx} {τ : MTy} (x : Var Γ τ) :
    MTerm SP.const Γ Ρ τ × MTerm SP.deep Γ Ρ τ := (.var x, .var x)

end Sketch

/-! # Model B: the profile on the arrow -/

namespace Latent

/-- Types, with the callee's stack profile recorded on the arrow.  This is the change that
    makes the classification survive higher-order code: what costs stack is *calling* a
    function, and the caller can only see the callee through its type. -/
inductive CTy
  | base
  | arr (p : SP) (σ τ : CTy)

abbrev Ctx := List CTy
abbrev RCtx := List (List CTy × CTy)

inductive Var : Ctx → CTy → Type
  | here : Var (τ :: Γ) τ
  | there : Var Γ τ → Var (σ :: Γ) τ

inductive RVar : RCtx → (List CTy × CTy) → Type
  | here : RVar (e :: Ρ) e
  | there : RVar Ρ e → RVar (f :: Ρ) e

/-- A curried `n`-ary function whose body has profile `p`: the intermediate arrows are
    partial applications, which cost nothing; the last one runs the body. -/
def CTy.arrows (p : SP) : List CTy → CTy → CTy
  | [], τ => τ
  | [σ], τ => .arr p σ τ
  | σ :: σ' :: σs, τ => .arr .const σ (arrows p (σ' :: σs) τ)

mutual

/-- The same language, with the profile of a term meaning "evaluating *this* term, now". -/
inductive CTerm : SP → Ctx → RCtx → CTy → Type
  | var : Var Γ τ → CTerm .const Γ Ρ τ
  | lit : Nat → CTerm .const Γ Ρ .base
  /-- Stand-in for the first-order primitives: costs what its argument costs. -/
  | prim : CTerm m Γ Ρ .base → CTerm m Γ Ρ .base
  /-- Building a closure is `O(1)`; the body's profile goes on the arrow. -/
  | lam : CTail p (σ :: Γ) Ρ τ → CTerm .const Γ Ρ (.arr p σ τ)
  /-- Applying costs the two subterms *and* the callee's latent profile. -/
  | ap : ∀ {Γ : Ctx} {Ρ : RCtx} {m₁ m₂ p : SP} {σ τ : CTy},
      CTerm m₁ Γ Ρ (.arr p σ τ) → CTerm m₂ Γ Ρ σ →
      CTerm (m₁.join (m₂.join p)) Γ Ρ τ
  /-- The measured recursion.  Building it is `O(1)`; its profile is the profile of its
      body, and is visible to callers in the result type. -/
  | fix : (ps : List CTy) → (p : SP) → (measure : CTerm .const (ps ++ Γ) Ρ .base) →
      (body : CTail p (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) →
      CTerm .const Γ Ρ (CTy.arrows p ps τ)
  /-- A self call in a non-tail position: a frame. -/
  | selfCall : RVar Ρ ⟨ps, τ⟩ → CSpine m Γ Ρ ps → CTerm .deep Γ Ρ τ
  | block : CTail m Γ Ρ τ → CTerm m Γ Ρ τ

inductive CTail : SP → Ctx → RCtx → CTy → Type
  | ret : CTerm m Γ Ρ τ → CTail m Γ Ρ τ
  /-- A self call in tail position: no frame, only the cost of the arguments. -/
  | tailCall : RVar Ρ ⟨ps, τ⟩ → CSpine m Γ Ρ ps → CTail m Γ Ρ τ
  | ifz : CTerm m₀ Γ Ρ .base → CTail m₁ Γ Ρ τ → CTail m₂ Γ Ρ τ →
      CTail (m₀.join (m₁.join m₂)) Γ Ρ τ

inductive CSpine : SP → Ctx → RCtx → List CTy → Type
  | nil : CSpine .const Γ Ρ []
  | cons : CTerm m₁ Γ Ρ σ → CSpine m₂ Γ Ρ σs → CSpine (m₁.join m₂) Γ Ρ (σ :: σs)

end

mutual

/-- "Evaluating this pushes a frame": a non-tail self call, or an application of a
    function whose latent profile is `deepStack`.  Note `lam` and `fix` are *not* costly —
    they build a closure. -/
def CTerm.Costly : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {τ : CTy}, CTerm m Γ Ρ τ → Prop
  | _, _, _, _, .var _ => False
  | _, _, _, _, .lit _ => False
  | _, _, _, _, .prim t => t.Costly
  | _, _, _, _, .lam _ => False
  | _, _, _, _, @CTerm.ap _ _ _ _ p _ _ f a => f.Costly ∨ a.Costly ∨ p = SP.deep
  | _, _, _, _, .fix _ _ _ _ => False
  | _, _, _, _, .selfCall _ _ => True
  | _, _, _, _, .block t => t.Costly

def CTail.Costly : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {τ : CTy}, CTail m Γ Ρ τ → Prop
  | _, _, _, _, .ret t => t.Costly
  | _, _, _, _, .tailCall _ sp => sp.Costly
  | _, _, _, _, .ifz c t e => c.Costly ∨ t.Costly ∨ e.Costly

def CSpine.Costly : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {σs : List CTy},
    CSpine m Γ Ρ σs → Prop
  | _, _, _, _, .nil => False
  | _, _, _, _, .cons t sp => t.Costly ∨ sp.Costly

end

mutual

/-- **Every frame-pushing term is indexed `deepStack`.** -/
theorem CTerm.deep_of_costly : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {τ : CTy}
    (t : CTerm m Γ Ρ τ), t.Costly → m = SP.deep
  | _, _, _, _, .var _, h => absurd h (by simp [CTerm.Costly])
  | _, _, _, _, .lit _, h => absurd h (by simp [CTerm.Costly])
  | _, _, _, _, .prim t, h => CTerm.deep_of_costly t h
  | _, _, _, _, .lam _, h => absurd h (by simp [CTerm.Costly])
  | _, _, _, _, .ap f a, h => by
      rcases (show f.Costly ∨ a.Costly ∨ _ = SP.deep from h) with hf | ha | hp
      · exact SP.join_eq_deep_left (CTerm.deep_of_costly f hf) _
      · exact SP.join_eq_deep_right _
          (SP.join_eq_deep_left (CTerm.deep_of_costly a ha) _)
      · exact SP.join_eq_deep_right _ (SP.join_eq_deep_right _ hp)
  | _, _, _, _, .fix _ _ _ _, h => absurd h (by simp [CTerm.Costly])
  | _, _, _, _, .selfCall _ _, _ => rfl
  | _, _, _, _, .block t, h => CTail.deep_of_costly t h

theorem CTail.deep_of_costly : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {τ : CTy}
    (t : CTail m Γ Ρ τ), t.Costly → m = SP.deep
  | _, _, _, _, .ret t, h => CTerm.deep_of_costly t h
  | _, _, _, _, .tailCall _ sp, h => CSpine.deep_of_costly sp h
  | _, _, _, _, .ifz c t e, h => by
      rcases (show c.Costly ∨ t.Costly ∨ e.Costly from h) with hc | ht | he
      · exact SP.join_eq_deep_left (CTerm.deep_of_costly c hc) _
      · exact SP.join_eq_deep_right _
          (SP.join_eq_deep_left (CTail.deep_of_costly t ht) _)
      · exact SP.join_eq_deep_right _
          (SP.join_eq_deep_right _ (CTail.deep_of_costly e he))

theorem CSpine.deep_of_costly : ∀ {m : SP} {Γ : Ctx} {Ρ : RCtx} {σs : List CTy}
    (sp : CSpine m Γ Ρ σs), sp.Costly → m = SP.deep
  | _, _, _, _, .nil, h => absurd h (by simp [CSpine.Costly])
  | _, _, _, _, .cons t sp, h => by
      rcases (show t.Costly ∨ sp.Costly from h) with ht | hs
      · exact SP.join_eq_deep_left (CTerm.deep_of_costly t ht) _
      · exact SP.join_eq_deep_right _ (CSpine.deep_of_costly sp hs)

end

/-- **What `constStack` means here**: a `constStack` term makes no non-tail self call and
    applies no function whose latent profile is `deepStack`.  Unlike Model A this says
    something about recursions, because a recursion may itself be `constStack`. -/
theorem CTail.const_notCostly {Γ : Ctx} {Ρ : RCtx} {τ : CTy} (t : CTail .const Γ Ρ τ) :
    ¬ t.Costly := fun h => SP.noConfusion (CTail.deep_of_costly t h)

/-! ## The two recursions the index is supposed to separate -/

/-- A tail recursion: `countdown n = if n = 0 then 0 else countdown (n-1)`.  Its body is a
    `CTail .const`, so its type is `.arr .const base base` — a `while` loop. -/
def countdown : CTerm .const [] [] (CTy.arrows .const [CTy.base] CTy.base) :=
  .fix [.base] .const (.var .here)
    (.ifz (.var .here) (.ret (.lit 0)) (.tailCall .here (.cons (.prim (.var .here)) .nil)))

/-- A non-tail recursion: `sumdown n = if n = 0 then 0 else n + sumdown (n-1)`.  The self
    call sits under a primitive, so the body is a `CTail .deep` and the type is
    `.arr .deep base base` — the caller can see that calling it costs frames. -/
def sumdown : CTerm .const [] [] (CTy.arrows .deep [CTy.base] CTy.base) :=
  .fix [.base] .deep (.var .here)
    (.ifz (.var .here) (.ret (.lit 0))
      (.ret (.prim (.selfCall .here (.cons (.prim (.var .here)) .nil)))))

/-- Applying `countdown` is free of frames … -/
example : (CTerm.ap countdown (.lit 5)).Costly ↔ False := by
  simp [CTerm.Costly, countdown]

/-- … and applying `sumdown` is not: the `deepStack` shows up at the call site, in a term
    that never mentions `sumdown`'s body. -/
example : (CTerm.ap sumdown (.lit 5)).Costly := by
  simp [CTerm.Costly, sumdown]

end Latent

end ExamplesStackProfile
