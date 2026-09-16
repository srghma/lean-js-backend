/-!
# A scaled-down model of the "usage-indexed `Term`" proposal

This file is the evidence behind `USAGE_INDEX_ASSESSMENT.md`.  It is *not* part of the
build (it is not under a library root); check it with

    lake env lean scripts/UsageProposalExperiment.lean

and it should report nothing but the two `unused variable` linter warnings.  Every
failure below is pinned with `#guard_msgs`, so a change of behaviour shows up as an
error.

The model keeps the shape of the proposal — `Usage`, `Var.usage`, and a `Term` indexed
by a usage mask — over a two-constructor `Ty`, and keeps the constructors the argument
turns on: `var`, `lamN`, `apN`, `lit`, `letE`, `ite` and `Spine`.
-/

inductive Ty where
  | base : Ty
  | fn : List Ty → Ty → Ty

abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type
  | head : ∀ {Γ τ}, Var (τ :: Γ) τ
  | tail : ∀ {Γ τ1 τ2}, Var Γ τ1 → Var (τ2 :: Γ) τ1

infix:40 " ∋ " => Var

/-- A usage bitmask tracking which variables in `Γ` are used. -/
inductive Usage : Ctx → Type where
  | nil  : Usage []
  | cons {Γ τ} : Bool → Usage Γ → Usage (τ :: Γ)

namespace Usage

def none : (Γ : Ctx) → Usage Γ
  | []     => .nil
  | _ :: Γ => .cons false (none Γ)

def all : (Γ : Ctx) → Usage Γ
  | []     => .nil
  | _ :: Γ => .cons true (all Γ)

def or : {Γ : Ctx} → Usage Γ → Usage Γ → Usage Γ
  | [],     .nil,        .nil        => .nil
  | _ :: _, .cons b1 u1, .cons b2 u2 => .cons (b1 || b2) (or u1 u2)

def append : {Δ Γ : Ctx} → Usage Δ → Usage Γ → Usage (Δ ++ Γ)
  | [],     _, .nil,       u2 => u2
  | _ :: _, _, .cons b u1, u2 => .cons b (append u1 u2)

end Usage

def Var.usage : {Γ : Ctx} → {τ : Ty} → (Γ ∋ τ) → Usage Γ
  | _ :: Γ, _, .head   => .cons true (Usage.none Γ)
  | _ :: _, _, .tail v => .cons false v.usage

mutual

inductive Term : (Γ : Ctx) → Usage Γ → Ty → Type
  | var : ∀ {Γ τ} (v : Γ ∋ τ), Term Γ v.usage τ
  | lamN : ∀ {Γ params ret uΓ},
      Term (params.reverse ++ Γ) (Usage.append (Usage.all params.reverse) uΓ) ret →
      Term Γ uΓ (.fn params ret)
  | apN : ∀ {Γ params ret uf us},
      Term Γ uf (.fn params ret) → Spine Γ us params → Term Γ (uf.or us) ret
  | lit : ∀ {Γ}, Nat → Term Γ (Usage.none Γ) .base
  | letE : ∀ {Γ σ τ u1 u2 b},
      Term Γ u1 σ → Term (σ :: Γ) (.cons b u2) τ →
      Term Γ (if b then u1.or u2 else u2) τ
  | ite : ∀ {Γ τ uc ut ue},
      Term Γ uc .base → Term Γ ut τ → Term Γ ue τ → Term Γ (uc.or (ut.or ue)) τ

inductive Spine : (Γ : Ctx) → Usage Γ → List Ty → Type
  | nil : ∀ {Γ}, Spine Γ (Usage.none Γ) []
  | cons : ∀ {Γ σ σs u1 u2},
      Term Γ u1 σ → Spine Γ u2 σs → Spine Γ (u1.or u2) (σ :: σs)

end

/-! ## 1. The idea works: small closed terms go through, and `K` does not -/

/-- `(v0) => v0` is accepted. -/
def tId : Term [] .nil (.fn [Ty.base] Ty.base) :=
  .lamN (params := [Ty.base]) (.var .head)

-- `(v0) => 1` — a constant function of one argument — is rejected, as intended.
/--
error: Application type mismatch: The argument
  Term.lit 1
has type
  Term ?m.9 (Usage.none ?m.9) Ty.base
but is expected to have type
  Term ([Ty.base].reverse ++ []) ((Usage.all [Ty.base].reverse).append Usage.nil) Ty.base
in the application
  (Term.lit 1).lamN
-/
#guard_msgs in
def tConstLit : Term [] .nil (.fn [Ty.base] Ty.base) :=
  .lamN (params := [Ty.base]) (.lit 1)

-- `(v0, v1) => v0` — the `K` combinator — is rejected, as intended.
/--
error: Application type mismatch: The argument
  Term.var Var.head
has type
  Term (?m.14 :: ?m.13) Var.head.usage ?m.14
but is expected to have type
  Term ([Ty.base, Ty.base].reverse ++ []) ((Usage.all [Ty.base, Ty.base].reverse).append Usage.nil) Ty.base
in the application
  (Term.var Var.head).lamN
-/
#guard_msgs in
def tConst : Term [] .nil (.fn [Ty.base, Ty.base] Ty.base) :=
  .lamN (params := [Ty.base, Ty.base]) (.var .head)

/-! ## 2. `Usage.or` is a commutative idempotent monoid only *propositionally* -/

/-- On a closed context the laws compute. -/
example (u : Usage [Ty.base]) : u.or (Usage.none _) = u := by
  cases u with | cons b u => cases u; cases b <;> rfl

-- On an abstract context they do not: `rfl` fails.
/--
error: Type mismatch
  rfl
has type
  ?m.4 = ?m.4
but is expected to have type
  u.or (Usage.none Γ) = u
-/
#guard_msgs in
example {Γ : Ctx} (u : Usage Γ) : u.or (Usage.none Γ) = u := rfl

theorem Usage.or_comm : {Γ : Ctx} → (u v : Usage Γ) → u.or v = v.or u
  | [], .nil, .nil => rfl
  | _ :: _, .cons b1 u1, .cons b2 u2 => by
      simp [Usage.or, Bool.or_comm, Usage.or_comm u1 u2]

/-! ## 3. A usage-preserving rewrite needs a transport -/

/-- Swapping the two branches of a conditional (a rewrite the peephole pass does) is
    still expressible, but only through `Usage.or_comm` and a `rw`. -/
def swapBranches {Γ : Ctx} {τ : Ty} {uc ut ue : Usage Γ}
    (c : Term Γ uc .base) (t : Term Γ ut τ) (e : Term Γ ue τ) :
    Term Γ (uc.or (ut.or ue)) τ := by
  rw [Usage.or_comm ut ue]
  exact Term.ite c e t

/-- A rewrite that *deletes* a use cannot even be given this type: the result of
    simplifying `if c then t else e` to `t` has usage `ut`, not `uc.or (ut.or ue)`.
    So no usage-deleting pass has type `Term Γ u τ → Term Γ u τ`; it must change the
    index, and at a `lamN` it may then fail to have any index at all. -/
example : True := trivial

/-! ## 4. What a translation from an external IR has to do -/

/-- The index is not known while translating, so it has to be packaged. -/
structure SomeTerm (Γ : Ctx) (τ : Ty) where
  usage : Usage Γ
  term  : Term Γ usage τ

def Usage.decEq : {Γ : Ctx} → (u v : Usage Γ) → Decidable (u = v)
  | [], .nil, .nil => isTrue rfl
  | _ :: _, .cons b1 u1, .cons b2 u2 =>
    match decEq u1 u2, b1, b2 with
    | isTrue h, false, false => isTrue (by simp [h])
    | isTrue h, true,  true  => isTrue (by simp [h])
    | isTrue _, false, true  => isFalse (by intro h; cases h)
    | isTrue _, true,  false => isFalse (by intro h; cases h)
    | isFalse h, _, _ => isFalse (by intro he; cases he; exact h rfl)

instance {Γ : Ctx} : DecidableEq (Usage Γ) := Usage.decEq

/-- Building a lambda over one parameter from a translated body: the mask of the body
    has to be *taken apart* and the "parameter used" bit checked at run time.  The
    dependent type contributes nothing to the check — it only records its outcome — and
    a body that does not use the parameter has no `Term` to return, so the translation
    becomes partial (`Option`). -/
def mkLam1 {Γ : Ctx} (σ : Ty) {ret : Ty} (body : SomeTerm (σ :: Γ) ret) :
    Option (SomeTerm Γ (.fn [σ] ret)) :=
  match body with
  | ⟨.cons true u, t⟩ => some ⟨u, .lamN (params := [σ]) t⟩
  | ⟨.cons false _, _⟩ => none   -- the parameter is unused: no term exists

/-- And it does reject exactly what it should. -/
example : mkLam1 (Γ := []) Ty.base ⟨.cons false .nil, .lit 1⟩ = none := rfl

/-! ## 5. Consumers are *not* affected: recursion over an indexed term is routine -/

mutual

def Term.size : {Γ : Ctx} → {u : Usage Γ} → {τ : Ty} → Term Γ u τ → Nat
  | _, _, _, .var _ => 1
  | _, _, _, .lit _ => 1
  | _, _, _, .lamN b => b.size + 1
  | _, _, _, .apN f s => f.size + s.size + 1
  | _, _, _, .letE e b => e.size + b.size + 1
  | _, _, _, .ite c t e => c.size + t.size + e.size + 1

def Spine.size : {Γ : Ctx} → {u : Usage Γ} → {σs : List Ty} → Spine Γ u σs → Nat
  | _, _, _, .nil => 0
  | _, _, _, .cons t r => t.size + r.size

end

/-- The usage index never has to be inspected by a consumer: it stays a variable. -/
example : tId.size = 2 := rfl
