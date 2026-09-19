module

public import LakeJs.Descends

@[expose] public section

set_option autoImplicit false

/-!
# A calculus of verification conditions for `Term.Descends`

`LakeJs.Descends` states the condition — *the body consults its self-reference only at
arguments of strictly smaller measure* — and derives from it that the `stuck` branch is
unreachable.  This module is the other half of §5.4 of
`TERM_RANK_FLAKINESS_AND_ALTERNATIVES.md`: the **verification-condition generator** that
reduces that condition, syntactically, to one arithmetic obligation per self call.

The judgment is `Term.SelfIndepOn δ ρ S Φ t`:

> for any two self-references that agree on the argument set `S`, and any local
> environment satisfying the **path condition** `Φ`, the term `t` has the same value.

`S` is instantiated with *"measure strictly below the measure of the current arguments"*,
and `Φ` is the path condition the term sits under, which is what makes the calculus
usable: the rule for `if` refines `Φ` with the truth of the test in each arm, and the rule
for `let` records the value the binder took, so by the time a self call is reached the
obligation it leaves — `Φ γ → S (arguments)` — carries exactly the branch tests that
Lean's own `decreasing_by` had available.

The rules are stated as lemmas rather than as an inductive definition on purpose: a proof
is then built by `apply`ing them, structurally, and what is left over is precisely the
arithmetic.  `Term.descends_of_selfIndepOn` closes the circle back to `Term.Descends`, and
`LakeJs.Examples.Descent` uses the calculus to re-derive a verification condition that was
first proved by hand, so the two routes can be compared.

**Coverage.**  There is a rule for every value constructor the arithmetic and the data
fragments of the grammar use — variables, literals, globals, externs, application,
abstraction, `let`, `if`, constructors, projections, tags, structural size, delay and
force, dispatch (`Term.caseTag`, with its own judgment for `Alts`), and both kinds of self
call — and for the block grammar too: `Term.block`, and `Tail`'s `ret`, `jmp`, `letT`,
`iteT`, `caseT` and `join`, with `AltsT` beside them.  The one construct with no rule is a
*nested* `Term.fix`, which shifts the self-reference away from the head of the recursion
context, where this judgment fixes it.  That is an addition to this file, not a change to
it; until then such a body's condition is proved directly against `Term.Descends`, as
`LakeJs.Examples.Descent` does.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout)

/-! ## The judgment -/

/-- The environment one binder out. -/
def Env.pop : ∀ {σ : Ty} {Γ : Ctx}, Env (σ :: Γ) → Env Γ
  | _, _, .cons _ rest => rest

@[simp] theorem Env.pop_cons {σ : Ty} {Γ : Ctx} (v : σ.den) (γ : Env Γ) :
    Env.pop (.cons v γ) = γ := rfl

@[simp] theorem Env.get_head_cons {σ : Ty} {Γ : Ctx} (v : σ.den) (γ : Env Γ) :
    (Env.cons v γ).get .head = v := rfl

variable {Sg : Sig} {Ρ : RCtx} {ps : List Ty} {τ : Ty}

/-- **The judgment.**  Under the path condition `Φ`, the value of `t` depends on the
    self-reference only through its behaviour on `S`. -/
def Term.SelfIndepOn (δ : GEnv Sg.decls) (ρ : REnv Ρ) (S : Env ps → Prop)
    {Γ' : Ctx} {σ : Ty} (Φ : Env Γ' → (Env ps → τ.den) → Prop)
    (t : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ) : Prop :=
  ∀ (γ' : Env Γ') (g₁ g₂ : Env ps → τ.den),
    (∀ bs : Env ps, S bs → g₁ bs = g₂ bs) → Φ γ' g₁ → Φ γ' g₂ →
    t.eval δ γ' (.cons g₁ ρ) = t.eval δ γ' (.cons g₂ ρ)

/-- The same, for a spine of arguments. -/
def Spine.SelfIndepOn (δ : GEnv Sg.decls) (ρ : REnv Ρ) (S : Env ps → Prop)
    {Γ' : Ctx} {σs : List Ty} (Φ : Env Γ' → (Env ps → τ.den) → Prop)
    (s : Spine Sg Γ' (⟨ps, τ⟩ :: Ρ) σs) : Prop :=
  ∀ (γ' : Env Γ') (g₁ g₂ : Env ps → τ.den),
    (∀ bs : Env ps, S bs → g₁ bs = g₂ bs) → Φ γ' g₁ → Φ γ' g₂ →
    s.eval δ γ' (.cons g₁ ρ) = s.eval δ γ' (.cons g₂ ρ)

variable {δ : GEnv Sg.decls} {ρ : REnv Ρ} {S : Env ps → Prop} {Γ' : Ctx}
  {Φ : Env Γ' → (Env ps → τ.den) → Prop}

/-! ## The leaves: nothing that reads the self-reference -/

/-- A variable. -/
theorem Term.selfIndepOn_var {σ : Ty} (x : Γ' ∋ σ) :
    Term.SelfIndepOn (τ := τ) δ ρ S Φ (.var x) := fun _ _ _ _ _ _ => rfl

/-- A literal. -/
theorem Term.selfIndepOn_lit {p : LeanPrimTy} (l : LeanPrimLit p) :
    Term.SelfIndepOn (τ := τ) δ ρ S Φ (.lit (Γ := Γ') (Ρ := ⟨ps, τ⟩ :: Ρ) l) :=
  fun _ _ _ _ _ _ => rfl

/-- A reference to a top-level declaration. -/
theorem Term.selfIndepOn_global {σ : Ty} (r : GlobalRef Sg.decls σ) :
    Term.SelfIndepOn (τ := τ) δ ρ S Φ (.global (Γ := Γ') (Ρ := ⟨ps, τ⟩ :: Ρ) r) :=
  fun _ _ _ _ _ _ => rfl

/-- A runtime primitive. -/
theorem Term.selfIndepOn_extern {σs : List Ty} {σ : Ty} (e : Externs σs σ) :
    Term.SelfIndepOn (τ := τ) δ ρ S Φ (.extern (Γ := Γ') (Ρ := ⟨ps, τ⟩ :: Ρ) e) :=
  fun _ _ _ _ _ _ => rfl

/-! ## The structural rules -/

/-- An application. -/
theorem Term.selfIndepOn_ap {σ₁ σ₂ : Ty} {f : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) (σ₁ ⇒ σ₂)}
    {a : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ₁}
    (hf : Term.SelfIndepOn δ ρ S Φ f) (ha : Term.SelfIndepOn δ ρ S Φ a) :
    Term.SelfIndepOn δ ρ S Φ (.ap f a) := by
  intro γ' g₁ g₂ hS h1 h2
  show (f.eval δ γ' (.cons g₁ ρ)) (a.eval δ γ' (.cons g₁ ρ))
      = (f.eval δ γ' (.cons g₂ ρ)) (a.eval δ γ' (.cons g₂ ρ))
  rw [hf γ' g₁ g₂ hS h1 h2, ha γ' g₁ g₂ hS h1 h2]

/-- An abstraction.  The path condition is carried past the new binder unchanged: it
    speaks about the environment the abstraction was written in. -/
theorem Term.selfIndepOn_lam {σ₁ σ₂ : Ty} {b : Term Sg (σ₁ :: Γ') (⟨ps, τ⟩ :: Ρ) σ₂}
    (hb : Term.SelfIndepOn δ ρ S (fun γ'' g => Φ (Env.pop γ'') g) b) :
    Term.SelfIndepOn δ ρ S Φ (.lam b) := by
  intro γ' g₁ g₂ hS h1 h2
  show (fun a => b.eval δ (.cons a γ') (.cons g₁ ρ))
      = (fun a => b.eval δ (.cons a γ') (.cons g₂ ρ))
  funext a
  exact hb (.cons a γ') g₁ g₂ hS h1 h2

/-- A delay. -/
theorem Term.selfIndepOn_lazyMk {σ : Ty} {e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ}
    (he : Term.SelfIndepOn δ ρ S Φ e) :
    Term.SelfIndepOn δ ρ S Φ (.lazyMk e) := by
  intro γ' g₁ g₂ hS h1 h2
  show (fun _ => e.eval δ γ' (.cons g₁ ρ)) = (fun _ => e.eval δ γ' (.cons g₂ ρ))
  rw [he γ' g₁ g₂ hS h1 h2]

/-- Forcing a delay. -/
theorem Term.selfIndepOn_lazyForce {σ : Ty} {e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) (.lazy σ)}
    (he : Term.SelfIndepOn δ ρ S Φ e) :
    Term.SelfIndepOn δ ρ S Φ (.lazyForce e) := by
  intro γ' g₁ g₂ hS h1 h2
  show (e.eval δ γ' (.cons g₁ ρ)) () = (e.eval δ γ' (.cons g₂ ρ)) ()
  rw [he γ' g₁ g₂ hS h1 h2]

/-- A `let`.  The body's path condition records **what the binder was bound to**, which is
    what lets a self call under a `let` be justified by the bound value. -/
theorem Term.selfIndepOn_letE {σ₁ σ₂ : Ty} {e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ₁}
    {b : Term Sg (σ₁ :: Γ') (⟨ps, τ⟩ :: Ρ) σ₂}
    (he : Term.SelfIndepOn δ ρ S Φ e)
    (hb : Term.SelfIndepOn δ ρ S
      (fun γ'' g => Φ (Env.pop γ'') g ∧
        γ''.get .head = e.eval δ (Env.pop γ'') (.cons g ρ)) b) :
    Term.SelfIndepOn δ ρ S Φ (.letE e b) := by
  intro γ' g₁ g₂ hS h1 h2
  have hev : e.eval δ γ' (.cons g₁ ρ) = e.eval δ γ' (.cons g₂ ρ) := he γ' g₁ g₂ hS h1 h2
  show b.eval δ (.cons (e.eval δ γ' (.cons g₁ ρ)) γ') (.cons g₁ ρ)
      = b.eval δ (.cons (e.eval δ γ' (.cons g₂ ρ)) γ') (.cons g₂ ρ)
  rw [← hev]
  exact hb (.cons (e.eval δ γ' (.cons g₁ ρ)) γ') g₁ g₂ hS ⟨h1, rfl⟩ ⟨h2, hev⟩

/-- **A two-way branch**, and the rule that makes the calculus worth having: each arm is
    checked under a path condition refined by the test. -/
theorem Term.selfIndepOn_ite {σ : Ty} {c : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) (.prim .bool)}
    {t e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ}
    (hc : Term.SelfIndepOn δ ρ S Φ c)
    (ht : Term.SelfIndepOn δ ρ S
      (fun γ'' g => Φ γ'' g ∧ (show Bool from c.eval δ γ'' (.cons g ρ)) = true) t)
    (he : Term.SelfIndepOn δ ρ S
      (fun γ'' g => Φ γ'' g ∧ (show Bool from c.eval δ γ'' (.cons g ρ)) = false) e) :
    Term.SelfIndepOn δ ρ S Φ (.ite c t e) := by
  intro γ' g₁ g₂ hS h1 h2
  have hcv : (show Bool from c.eval δ γ' (.cons g₁ ρ))
      = (show Bool from c.eval δ γ' (.cons g₂ ρ)) := hc γ' g₁ g₂ hS h1 h2
  show (if cond (c.eval δ γ' (.cons g₁ ρ)) true false
        then t.eval δ γ' (.cons g₁ ρ) else e.eval δ γ' (.cons g₁ ρ))
      = (if cond (c.eval δ γ' (.cons g₂ ρ)) true false
        then t.eval δ γ' (.cons g₂ ρ) else e.eval δ γ' (.cons g₂ ρ))
  cases hb : (show Bool from c.eval δ γ' (.cons g₁ ρ)) with
  | true =>
    have hb2 : (show Bool from c.eval δ γ' (.cons g₂ ρ)) = true := by rw [← hcv, hb]
    simp only [hb, hb2, cond_true, if_true]
    exact ht γ' g₁ g₂ hS ⟨h1, hb⟩ ⟨h2, hb2⟩
  | false =>
    have hb2 : (show Bool from c.eval δ γ' (.cons g₂ ρ)) = false := by rw [← hcv, hb]
    simp only [hb, hb2, cond_false, if_false, Bool.false_eq_true]
    exact he γ' g₁ g₂ hS ⟨h1, hb⟩ ⟨h2, hb2⟩

/-! ## Data -/

/-- Building a tagged value. -/
theorem Term.selfIndepOn_ctor {σ : Ty} {i : Nat} {fields : FieldLayout}
    {h : σ.ctorFields? i = some fields} {s : Spine Sg Γ' (⟨ps, τ⟩ :: Ρ) fields}
    (hs : Spine.SelfIndepOn δ ρ S Φ s) :
    Term.SelfIndepOn δ ρ S Φ (.ctor i fields h s) := by
  intro γ' g₁ g₂ hS h1 h2
  show σ.buildVal i (s.eval δ γ' (.cons g₁ ρ)).toData
      = σ.buildVal i (s.eval δ γ' (.cons g₂ ρ)).toData
  rw [hs γ' g₁ g₂ hS h1 h2]

/-- Reading a field. -/
theorem Term.selfIndepOn_proj {σ₁ σ₂ : Ty} {e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ₁} {i j : Nat}
    {hOne : σ₁.numCtors? = some 1} {hf : σ₁.fieldTy? i j = some σ₂}
    (he : Term.SelfIndepOn δ ρ S Φ e) :
    Term.SelfIndepOn δ ρ S Φ (.proj e i j hOne hf) := by
  intro γ' g₁ g₂ hS h1 h2
  show σ₂.ofData ((σ₁.fieldsOfVal (e.eval δ γ' (.cons g₁ ρ))).getD j .opaque)
      = σ₂.ofData ((σ₁.fieldsOfVal (e.eval δ γ' (.cons g₂ ρ))).getD j .opaque)
  rw [he γ' g₁ g₂ hS h1 h2]

/-- Reading a tag. -/
theorem Term.selfIndepOn_tagOf {σ : Ty} {e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ}
    {ht : σ.isTagged = true} (he : Term.SelfIndepOn δ ρ S Φ e) :
    Term.SelfIndepOn δ ρ S Φ (.tagOf e ht) := by
  intro γ' g₁ g₂ hS h1 h2
  show σ.tagOfVal (e.eval δ γ' (.cons g₁ ρ)) = σ.tagOfVal (e.eval δ γ' (.cons g₂ ρ))
  rw [he γ' g₁ g₂ hS h1 h2]

/-- The structural size of a value: the measure of a structural recursion. -/
theorem Term.selfIndepOn_structSize {σ : Ty} {e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ}
    (he : Term.SelfIndepOn δ ρ S Φ e) :
    Term.SelfIndepOn δ ρ S Φ (.structSize e) := by
  intro γ' g₁ g₂ hS h1 h2
  show Data.size (σ.toData (e.eval δ γ' (.cons g₁ ρ)))
      = Data.size (σ.toData (e.eval δ γ' (.cons g₂ ρ)))
  rw [he γ' g₁ g₂ hS h1 h2]

/-! ## Spines -/

/-- The empty spine. -/
theorem Spine.selfIndepOn_nil :
    Spine.SelfIndepOn (τ := τ) δ ρ S Φ (.nil (Γ := Γ') (Ρ := ⟨ps, τ⟩ :: Ρ)) :=
  fun _ _ _ _ _ _ => rfl

/-- One more argument. -/
theorem Spine.selfIndepOn_cons {σ : Ty} {σs : List Ty}
    {a : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ} {rest : Spine Sg Γ' (⟨ps, τ⟩ :: Ρ) σs}
    (ha : Term.SelfIndepOn δ ρ S Φ a) (hrest : Spine.SelfIndepOn δ ρ S Φ rest) :
    Spine.SelfIndepOn δ ρ S Φ (.cons a rest) := by
  intro γ' g₁ g₂ hS h1 h2
  show Env.cons (a.eval δ γ' (.cons g₁ ρ)) (rest.eval δ γ' (.cons g₁ ρ))
      = Env.cons (a.eval δ γ' (.cons g₂ ρ)) (rest.eval δ γ' (.cons g₂ ρ))
  rw [ha γ' g₁ g₂ hS h1 h2, hrest γ' g₁ g₂ hS h1 h2]

/-! ## Dispatch

A `Term.caseTag` needs a judgment for its branches, and that judgment's path condition has
to speak about **which branch was taken**: the tag and the field data of the scrutinee.
So the branch judgment is indexed by a predicate of the tag and the fields as well as of
the environment, and the `caseTag` rule instantiates it with "the tag and fields are the
scrutinee's". -/

/-- The judgment for the branches of a dispatch. -/
def Alts.SelfIndepOn (δ : GEnv Sg.decls) (ρ : REnv Ρ) (S : Env ps → Prop)
    {Γ' : Ctx} {σ σ' : Ty} {tags : List Nat} {full : Bool}
    (Ψ : Nat → List Data → Env Γ' → (Env ps → τ.den) → Prop)
    (alts : Alts Sg Γ' (⟨ps, τ⟩ :: Ρ) σ σ' tags full) : Prop :=
  ∀ (tag : Nat) (fs : List Data) (γ' : Env Γ') (g₁ g₂ : Env ps → τ.den),
    (∀ bs : Env ps, S bs → g₁ bs = g₂ bs) → Ψ tag fs γ' g₁ → Ψ tag fs γ' g₂ →
    alts.eval tag fs δ γ' (.cons g₁ ρ) = alts.eval tag fs δ γ' (.cons g₂ ρ)

variable {σ σ' : Ty} {Ψ : Nat → List Data → Env Γ' → (Env ps → τ.den) → Prop}

/-- The default branch: reached at some tag, with some fields, and binding nothing. -/
theorem Alts.selfIndepOn_deflt {e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ'}
    (he : Term.SelfIndepOn δ ρ S
      (fun γ' g => ∃ (tag : Nat) (fs : List Data), Ψ tag fs γ' g) e) :
    Alts.SelfIndepOn (σ := σ) δ ρ S Ψ (.deflt e) := by
  intro tag fs γ' g₁ g₂ hS h1 h2
  show some (e.eval δ γ' (.cons g₁ ρ)) = some (e.eval δ γ' (.cons g₂ ρ))
  rw [he γ' g₁ g₂ hS ⟨tag, fs, h1⟩ ⟨tag, fs, h2⟩]

/-- The end of an exhaustive dispatch. -/
theorem Alts.selfIndepOn_nilFull :
    Alts.SelfIndepOn (Sg := Sg) (τ := τ) (σ := σ) (σ' := σ') δ ρ S Ψ .nilFull :=
  fun _ _ _ _ _ _ _ _ => rfl

/-- One more branch.  Its body is checked under a path condition that records the tag it
    matched and **the fields it bound**, which is how a self call on a field of the
    scrutinee is justified. -/
theorem Alts.selfIndepOn_cons {tag : Nat} {fields : FieldLayout}
    {hf : σ.ctorFields? tag = some fields} {tags : List Nat} {full : Bool}
    {body : Term Sg (fields ++ Γ') (⟨ps, τ⟩ :: Ρ) σ'}
    {rest : Alts Sg Γ' (⟨ps, τ⟩ :: Ρ) σ σ' tags full}
    (hbody : Term.SelfIndepOn δ ρ S
      (fun γ'' g => ∃ (γ' : Env Γ') (fs : List Data),
        Ψ tag fs γ' g ∧ γ'' = (Env.ofData fields fs).append γ') body)
    (hrest : Alts.SelfIndepOn δ ρ S Ψ rest) :
    Alts.SelfIndepOn δ ρ S Ψ (.cons tag fields hf body rest) := by
  intro tag' fs γ' g₁ g₂ hS h1 h2
  show (if tag = tag'
        then some (body.eval δ ((Env.ofData fields fs).append γ') (.cons g₁ ρ))
        else rest.eval tag' fs δ γ' (.cons g₁ ρ))
      = (if tag = tag'
        then some (body.eval δ ((Env.ofData fields fs).append γ') (.cons g₂ ρ))
        else rest.eval tag' fs δ γ' (.cons g₂ ρ))
  by_cases ht : tag = tag'
  · subst ht
    rw [hbody ((Env.ofData fields fs).append γ') g₁ g₂ hS ⟨γ', fs, h1, rfl⟩
      ⟨γ', fs, h2, rfl⟩]
    simp
  · simp only [if_neg ht]
    exact hrest tag' fs γ' g₁ g₂ hS h1 h2

/-- **A dispatch.**  The branches are checked knowing the scrutinee's tag and fields. -/
theorem Term.selfIndepOn_caseTag {tags : List Nat} {full : Bool}
    {scrut : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ}
    {alts : Alts Sg Γ' (⟨ps, τ⟩ :: Ρ) σ σ' tags full}
    {h : σ.caseOkAlts full tags = true}
    (hscrut : Term.SelfIndepOn δ ρ S Φ scrut)
    (halts : Alts.SelfIndepOn δ ρ S
      (fun tag fs γ' g => Φ γ' g ∧
        tag = σ.tagOfVal (scrut.eval δ γ' (.cons g ρ)) ∧
        fs = σ.fieldsOfVal (scrut.eval δ γ' (.cons g ρ))) alts) :
    Term.SelfIndepOn δ ρ S Φ (.caseTag scrut alts h) := by
  intro γ' g₁ g₂ hS h1 h2
  have hv : scrut.eval δ γ' (.cons g₁ ρ) = scrut.eval δ γ' (.cons g₂ ρ) :=
    hscrut γ' g₁ g₂ hS h1 h2
  have halt := halts (σ.tagOfVal (scrut.eval δ γ' (.cons g₁ ρ)))
    (σ.fieldsOfVal (scrut.eval δ γ' (.cons g₁ ρ))) γ' g₁ g₂ hS
    ⟨h1, rfl, rfl⟩ ⟨h2, by rw [hv], by rw [hv]⟩
  show (match alts.eval (σ.tagOfVal (scrut.eval δ γ' (.cons g₁ ρ)))
          (σ.fieldsOfVal (scrut.eval δ γ' (.cons g₁ ρ))) δ γ' (.cons g₁ ρ) with
        | some r => r | none => σ'.dflt)
      = (match alts.eval (σ.tagOfVal (scrut.eval δ γ' (.cons g₂ ρ)))
          (σ.fieldsOfVal (scrut.eval δ γ' (.cons g₂ ρ))) δ γ' (.cons g₂ ρ) with
        | some r => r | none => σ'.dflt)
  rw [← hv, halt]

/-! ## The two kinds of call -/

/-- **A self call.**  This is the only rule that leaves an obligation, and the obligation
    is exactly the one Lean's `decreasing_by` discharges: under the path condition the
    call sits under, its arguments are in `S` — i.e. their measure descends. -/
theorem Term.selfIndepOn_selfCall {s : Spine Sg Γ' (⟨ps, τ⟩ :: Ρ) ps}
    (hs : Spine.SelfIndepOn δ ρ S Φ s)
    (hdesc : ∀ (γ' : Env Γ') (g : Env ps → τ.den), Φ γ' g →
      S (s.eval δ γ' (.cons g ρ))) :
    Term.SelfIndepOn δ ρ S Φ (.selfCall .head s) := by
  intro γ' g₁ g₂ hS h1 h2
  show g₁ (s.eval δ γ' (.cons g₁ ρ)) = g₂ (s.eval δ γ' (.cons g₂ ρ))
  rw [← hs γ' g₁ g₂ hS h1 h2]
  exact hS _ (hdesc γ' g₁ h1)

/-- **A call of an enclosing recursion**, i.e. one of `Ρ` rather than the one being
    checked.  Its value comes from `ρ`, so there is no obligation at all. -/
theorem Term.selfIndepOn_outerCall {qs : List Ty} {σ : Ty} (r : Ρ ∋ᵣ ⟨qs, σ⟩)
    {s : Spine Sg Γ' (⟨ps, τ⟩ :: Ρ) qs} (hs : Spine.SelfIndepOn δ ρ S Φ s) :
    Term.SelfIndepOn δ ρ S Φ (.selfCall (.tail r) s) := by
  intro γ' g₁ g₂ hS h1 h2
  show ρ.get r (s.eval δ γ' (.cons g₁ ρ)) = ρ.get r (s.eval δ γ' (.cons g₂ ρ))
  rw [hs γ' g₁ g₂ hS h1 h2]

/-! ## Blocks

`Term.block` opens the tail grammar, whose evaluator carries a **label environment** — one
Lean function per join point in scope.  Those functions are built from the block's own
bodies, so they depend on the self-reference too; the judgment therefore quantifies over
two label environments that **agree**, and the `join` rule is what establishes the
agreement of the pair it adds. -/

/-- Two label environments of the *same* context agree pointwise when every join point in
    scope answers the same at every argument list.  (`LEnv.Agree` of
    `LakeJs.SubstLemmas` is the different, renaming-indexed relation.) -/
def LEnv.Pointwise {σ' : Ty} {Ω : LCtx} (l₁ l₂ : LEnv σ' Ω) : Prop :=
  ∀ (qs : List Ty) (l : Ω ∋ₗ qs) (args : Env qs), l₁.get l args = l₂.get l args

/-- Agreement of the empty label environment. -/
theorem LEnv.pointwise_nil {σ' : Ty} : LEnv.Pointwise (σ' := σ') .nil .nil := by
  intro _ l _
  cases l

/-- Extending two agreeing label environments with agreeing join points. -/
theorem LEnv.pointwise_cons {σ' : Ty} {Ω : LCtx} {qs : List Ty} {f₁ f₂ : Env qs → σ'.den}
    {l₁ l₂ : LEnv σ' Ω} (hf : ∀ args : Env qs, f₁ args = f₂ args) (hl : LEnv.Pointwise l₁ l₂) :
    LEnv.Pointwise (.cons f₁ l₁) (.cons f₂ l₂) := by
  intro rs l args
  cases l with
  | head => exact hf args
  | tail l' => exact hl rs l' args

/-- The judgment for a block. -/
def Tail.SelfIndepOn (δ : GEnv Sg.decls) (ρ : REnv Ρ) (S : Env ps → Prop)
    {Γ' : Ctx} {Ω : LCtx} {σ' : Ty} (Φ : Env Γ' → (Env ps → τ.den) → Prop)
    (b : Tail Sg Γ' Ω (⟨ps, τ⟩ :: Ρ) σ') : Prop :=
  ∀ (γ' : Env Γ') (lenv₁ lenv₂ : LEnv σ' Ω) (g₁ g₂ : Env ps → τ.den),
    LEnv.Pointwise lenv₁ lenv₂ → (∀ bs : Env ps, S bs → g₁ bs = g₂ bs) → Φ γ' g₁ → Φ γ' g₂ →
    b.eval δ γ' lenv₁ (.cons g₁ ρ) = b.eval δ γ' lenv₂ (.cons g₂ ρ)

/-- The judgment for the branches of a dispatch in tail position. -/
def AltsT.SelfIndepOn (δ : GEnv Sg.decls) (ρ : REnv Ρ) (S : Env ps → Prop)
    {Γ' : Ctx} {Ω : LCtx} {σ σ' : Ty} {tags : List Nat} {full : Bool}
    (Ψ : Nat → List Data → Env Γ' → (Env ps → τ.den) → Prop)
    (alts : AltsT Sg Γ' Ω (⟨ps, τ⟩ :: Ρ) σ σ' tags full) : Prop :=
  ∀ (tag : Nat) (fs : List Data) (γ' : Env Γ') (lenv₁ lenv₂ : LEnv σ' Ω)
    (g₁ g₂ : Env ps → τ.den),
    LEnv.Pointwise lenv₁ lenv₂ → (∀ bs : Env ps, S bs → g₁ bs = g₂ bs) →
    Ψ tag fs γ' g₁ → Ψ tag fs γ' g₂ →
    alts.eval tag fs δ γ' lenv₁ (.cons g₁ ρ) = alts.eval tag fs δ γ' lenv₂ (.cons g₂ ρ)

variable {Ω : LCtx}

/-- Answering with a value. -/
theorem Tail.selfIndepOn_ret {σ' : Ty} {e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ'}
    (he : Term.SelfIndepOn δ ρ S Φ e) :
    Tail.SelfIndepOn (Ω := Ω) δ ρ S Φ (.ret e) := by
  intro γ' _ _ g₁ g₂ _ hS h1 h2
  exact he γ' g₁ g₂ hS h1 h2

/-- Jumping to a join point: the label environments agree, so the answers do. -/
theorem Tail.selfIndepOn_jmp {σ' : Ty} {qs : List Ty} (l : Ω ∋ₗ qs)
    {s : Spine Sg Γ' (⟨ps, τ⟩ :: Ρ) qs} (hs : Spine.SelfIndepOn δ ρ S Φ s) :
    Tail.SelfIndepOn (σ' := σ') δ ρ S Φ (.jmp l s) := by
  intro γ' lenv₁ lenv₂ g₁ g₂ hl hS h1 h2
  show lenv₁.get l (s.eval δ γ' (.cons g₁ ρ)) = lenv₂.get l (s.eval δ γ' (.cons g₂ ρ))
  rw [hs γ' g₁ g₂ hS h1 h2]
  exact hl qs l _

/-- A `let` in front of the rest of the block. -/
theorem Tail.selfIndepOn_letT {σ₁ σ' : Ty} {e : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ₁}
    {rest : Tail Sg (σ₁ :: Γ') Ω (⟨ps, τ⟩ :: Ρ) σ'}
    (he : Term.SelfIndepOn δ ρ S Φ e)
    (hrest : Tail.SelfIndepOn δ ρ S
      (fun γ'' g => Φ (Env.pop γ'') g ∧
        γ''.get .head = e.eval δ (Env.pop γ'') (.cons g ρ)) rest) :
    Tail.SelfIndepOn δ ρ S Φ (.letT e rest) := by
  intro γ' lenv₁ lenv₂ g₁ g₂ hl hS h1 h2
  have hev : e.eval δ γ' (.cons g₁ ρ) = e.eval δ γ' (.cons g₂ ρ) := he γ' g₁ g₂ hS h1 h2
  show rest.eval δ (.cons (e.eval δ γ' (.cons g₁ ρ)) γ') lenv₁ (.cons g₁ ρ)
      = rest.eval δ (.cons (e.eval δ γ' (.cons g₂ ρ)) γ') lenv₂ (.cons g₂ ρ)
  rw [← hev]
  exact hrest (.cons (e.eval δ γ' (.cons g₁ ρ)) γ') lenv₁ lenv₂ g₁ g₂ hl hS
    ⟨h1, rfl⟩ ⟨h2, hev⟩

/-- A branch in tail position. -/
theorem Tail.selfIndepOn_iteT {σ' : Ty} {c : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) (.prim .bool)}
    {t e : Tail Sg Γ' Ω (⟨ps, τ⟩ :: Ρ) σ'}
    (hc : Term.SelfIndepOn δ ρ S Φ c)
    (ht : Tail.SelfIndepOn δ ρ S
      (fun γ'' g => Φ γ'' g ∧ (show Bool from c.eval δ γ'' (.cons g ρ)) = true) t)
    (he : Tail.SelfIndepOn δ ρ S
      (fun γ'' g => Φ γ'' g ∧ (show Bool from c.eval δ γ'' (.cons g ρ)) = false) e) :
    Tail.SelfIndepOn δ ρ S Φ (.iteT c t e) := by
  intro γ' lenv₁ lenv₂ g₁ g₂ hl hS h1 h2
  have hcv : (show Bool from c.eval δ γ' (.cons g₁ ρ))
      = (show Bool from c.eval δ γ' (.cons g₂ ρ)) := hc γ' g₁ g₂ hS h1 h2
  show (if cond (c.eval δ γ' (.cons g₁ ρ)) true false
        then t.eval δ γ' lenv₁ (.cons g₁ ρ) else e.eval δ γ' lenv₁ (.cons g₁ ρ))
      = (if cond (c.eval δ γ' (.cons g₂ ρ)) true false
        then t.eval δ γ' lenv₂ (.cons g₂ ρ) else e.eval δ γ' lenv₂ (.cons g₂ ρ))
  cases hb : (show Bool from c.eval δ γ' (.cons g₁ ρ)) with
  | true =>
    have hb2 : (show Bool from c.eval δ γ' (.cons g₂ ρ)) = true := by rw [← hcv, hb]
    simp only [hb, hb2, cond_true, if_true]
    exact ht γ' lenv₁ lenv₂ g₁ g₂ hl hS ⟨h1, hb⟩ ⟨h2, hb2⟩
  | false =>
    have hb2 : (show Bool from c.eval δ γ' (.cons g₂ ρ)) = false := by rw [← hcv, hb]
    simp only [hb, hb2, cond_false, if_false, Bool.false_eq_true]
    exact he γ' lenv₁ lenv₂ g₁ g₂ hl hS ⟨h1, hb⟩ ⟨h2, hb2⟩

/-- **A join point.**  Its body is checked knowing only that the environment begins with
    the join point's arguments; the rule then hands the `rest` a pair of label
    environments that agree, which is exactly what its own judgment asks for. -/
theorem Tail.selfIndepOn_join {σ' : Ty} {qs : List Ty}
    {body : Tail Sg (qs ++ Γ') Ω (⟨ps, τ⟩ :: Ρ) σ'}
    {rest : Tail Sg Γ' (qs :: Ω) (⟨ps, τ⟩ :: Ρ) σ'}
    (hbody : Tail.SelfIndepOn δ ρ S
      (fun γ'' g => ∃ (args : Env qs) (γ' : Env Γ'), Φ γ' g ∧ γ'' = args.append γ') body)
    (hrest : Tail.SelfIndepOn δ ρ S Φ rest) :
    Tail.SelfIndepOn δ ρ S Φ (.join qs body rest) := by
  intro γ' lenv₁ lenv₂ g₁ g₂ hl hS h1 h2
  show rest.eval δ γ'
      (.cons (fun args : Env qs => body.eval δ (args.append γ') lenv₁ (.cons g₁ ρ)) lenv₁)
      (.cons g₁ ρ)
    = rest.eval δ γ'
      (.cons (fun args : Env qs => body.eval δ (args.append γ') lenv₂ (.cons g₂ ρ)) lenv₂)
      (.cons g₂ ρ)
  refine hrest γ' _ _ g₁ g₂ (LEnv.pointwise_cons (fun args => ?_) hl) hS h1 h2
  exact hbody (args.append γ') lenv₁ lenv₂ g₁ g₂ hl hS ⟨args, γ', h1, rfl⟩ ⟨args, γ', h2, rfl⟩

/-- The default branch of a dispatch in tail position. -/
theorem AltsT.selfIndepOn_deflt {σ σ' : Ty}
    {Ψ : Nat → List Data → Env Γ' → (Env ps → τ.den) → Prop}
    {b : Tail Sg Γ' Ω (⟨ps, τ⟩ :: Ρ) σ'}
    (hb : Tail.SelfIndepOn δ ρ S
      (fun γ' g => ∃ (tag : Nat) (fs : List Data), Ψ tag fs γ' g) b) :
    AltsT.SelfIndepOn (σ := σ) δ ρ S Ψ (.deflt b) := by
  intro tag fs γ' lenv₁ lenv₂ g₁ g₂ hl hS h1 h2
  show some (b.eval δ γ' lenv₁ (.cons g₁ ρ)) = some (b.eval δ γ' lenv₂ (.cons g₂ ρ))
  rw [hb γ' lenv₁ lenv₂ g₁ g₂ hl hS ⟨tag, fs, h1⟩ ⟨tag, fs, h2⟩]

/-- The end of an exhaustive dispatch in tail position. -/
theorem AltsT.selfIndepOn_nilFull {σ σ' : Ty}
    {Ψ : Nat → List Data → Env Γ' → (Env ps → τ.den) → Prop} :
    AltsT.SelfIndepOn (Sg := Sg) (τ := τ) (Ω := Ω) (σ := σ) (σ' := σ') δ ρ S Ψ .nilFull :=
  fun _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- One more branch of a dispatch in tail position. -/
theorem AltsT.selfIndepOn_cons {σ σ' : Ty}
    {Ψ : Nat → List Data → Env Γ' → (Env ps → τ.den) → Prop}
    {tag : Nat} {fields : FieldLayout} {hf : σ.ctorFields? tag = some fields}
    {tags : List Nat} {full : Bool}
    {body : Tail Sg (fields ++ Γ') Ω (⟨ps, τ⟩ :: Ρ) σ'}
    {rest : AltsT Sg Γ' Ω (⟨ps, τ⟩ :: Ρ) σ σ' tags full}
    (hbody : Tail.SelfIndepOn δ ρ S
      (fun γ'' g => ∃ (γ' : Env Γ') (fs : List Data),
        Ψ tag fs γ' g ∧ γ'' = (Env.ofData fields fs).append γ') body)
    (hrest : AltsT.SelfIndepOn δ ρ S Ψ rest) :
    AltsT.SelfIndepOn δ ρ S Ψ (.cons tag fields hf body rest) := by
  intro tag' fs γ' lenv₁ lenv₂ g₁ g₂ hl hS h1 h2
  show (if tag = tag'
        then some (body.eval δ ((Env.ofData fields fs).append γ') lenv₁ (.cons g₁ ρ))
        else rest.eval tag' fs δ γ' lenv₁ (.cons g₁ ρ))
      = (if tag = tag'
        then some (body.eval δ ((Env.ofData fields fs).append γ') lenv₂ (.cons g₂ ρ))
        else rest.eval tag' fs δ γ' lenv₂ (.cons g₂ ρ))
  by_cases ht : tag = tag'
  · subst ht
    rw [hbody ((Env.ofData fields fs).append γ') lenv₁ lenv₂ g₁ g₂ hl hS
      ⟨γ', fs, h1, rfl⟩ ⟨γ', fs, h2, rfl⟩]
    simp
  · simp only [if_neg ht]
    exact hrest tag' fs γ' lenv₁ lenv₂ g₁ g₂ hl hS h1 h2

/-- A dispatch in tail position. -/
theorem Tail.selfIndepOn_caseT {σ σ' : Ty} {tags : List Nat} {full : Bool}
    {scrut : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ}
    {alts : AltsT Sg Γ' Ω (⟨ps, τ⟩ :: Ρ) σ σ' tags full}
    {h : σ.caseOkAlts full tags = true}
    (hscrut : Term.SelfIndepOn δ ρ S Φ scrut)
    (halts : AltsT.SelfIndepOn δ ρ S
      (fun tag fs γ' g => Φ γ' g ∧
        tag = σ.tagOfVal (scrut.eval δ γ' (.cons g ρ)) ∧
        fs = σ.fieldsOfVal (scrut.eval δ γ' (.cons g ρ))) alts) :
    Tail.SelfIndepOn δ ρ S Φ (.caseT scrut alts h) := by
  intro γ' lenv₁ lenv₂ g₁ g₂ hl hS h1 h2
  have hv : scrut.eval δ γ' (.cons g₁ ρ) = scrut.eval δ γ' (.cons g₂ ρ) :=
    hscrut γ' g₁ g₂ hS h1 h2
  have halt := halts (σ.tagOfVal (scrut.eval δ γ' (.cons g₁ ρ)))
    (σ.fieldsOfVal (scrut.eval δ γ' (.cons g₁ ρ))) γ' lenv₁ lenv₂ g₁ g₂ hl hS
    ⟨h1, rfl, rfl⟩ ⟨h2, by rw [hv], by rw [hv]⟩
  show (match alts.eval (σ.tagOfVal (scrut.eval δ γ' (.cons g₁ ρ)))
          (σ.fieldsOfVal (scrut.eval δ γ' (.cons g₁ ρ))) δ γ' lenv₁ (.cons g₁ ρ) with
        | some r => r | none => σ'.dflt)
      = (match alts.eval (σ.tagOfVal (scrut.eval δ γ' (.cons g₂ ρ)))
          (σ.fieldsOfVal (scrut.eval δ γ' (.cons g₂ ρ))) δ γ' lenv₂ (.cons g₂ ρ) with
        | some r => r | none => σ'.dflt)
  rw [← hv, halt]

/-- **A block**, in a term: its tail is checked in the empty label environment. -/
theorem Term.selfIndepOn_block {σ' : Ty} {b : Tail Sg Γ' [] (⟨ps, τ⟩ :: Ρ) σ'}
    (hb : Tail.SelfIndepOn δ ρ S Φ b) :
    Term.SelfIndepOn δ ρ S Φ (.block b) := by
  intro γ' g₁ g₂ hS h1 h2
  exact hb γ' .nil .nil g₁ g₂ LEnv.pointwise_nil hS h1 h2

/-! ## Back to `Term.Descends` -/

/-- **The calculus discharges the verification condition.**  A body that is
    self-independent below its own measure, under the trivial path condition that fixes
    the environment to the arguments, descends. -/
theorem Term.descends_of_selfIndepOn {k : Nat} {Γ : Ctx}
    (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)
    (h : ∀ as : Env ps,
      Term.SelfIndepOn δ ρ
        (fun bs => Lex.NatVec.Lt (Term.measureVal measure δ γ ρ bs)
          (Term.measureVal measure δ γ ρ as))
        (fun γ' (_ : Env ps → τ.den) => γ' = as.append γ) body) :
    Term.Descends measure body δ γ ρ := by
  intro as g₁ g₂ hg
  exact h as (as.append γ) g₁ g₂ hg rfl rfl

end LakeJs.Expr

end
