module

@[expose] public section

set_option autoImplicit false

universe u

/-!
# `NatVec`: lexicographic measures, and a kernel-computable runner for them

This module is the arithmetic core of the **guarded lexicographic recursion** of
`LakeJs.Expr`.  It is about nothing but numbers: a `Term` does not occur here.

A termination measure is a tuple of natural numbers — what Lean's `termination_by n m =>
(n, m)` writes — so the value of a measure is a `NatVec k`, and "the recursion descends"
is `NatVec.Lt`, the lexicographic order with the *most significant* component first.

Two things are needed of that order, and this file provides both.

* **It is well founded** (`NatVec.acc`).  That is what a *proof* that a recursion computes
  the function it came from inducts on.
* **It has a runner that the kernel computes** (`LexRun`).  A recursion run by
  `WellFounded.fix` does not reduce definitionally — `Acc.rec` gets stuck on an opaque
  proof — and the examples of this library check what a term computes with `rfl`, so the
  evaluator may not use one.  `LexRun` is therefore built out of `Nat.rec` and structural
  recursion on the number of components, with a *fuel* discipline that is invisible from
  outside: `LexRun_unfold` states the equation it satisfies, and that equation mentions no
  fuel.

## The equation

```
LexRun k dflt F v = F (fun w => if w.lt v then LexRun k dflt F w else dflt) v
```

`F` is the body of the recursion; it is handed a function `rec` which answers with the
recursion's value at `w` when `w` is **strictly smaller** than the current bound `v`, and
with `dflt` — the `stuck` branch of `Term.fix` — when it is not.  So a body that calls
itself at a measure that does not descend gets `dflt`: an observable answer, not a wrong
one, and not a hang.

## How the fuel works, and why it is not visible

At `k = 0` there is nothing to descend, so the body is run once with `rec` constantly
`dflt`.

At `k + 1` the run is a `Nat.rec` on a *head fuel* `fh`, maintained at or above the head
component of the current bound.  A call that decreases the head can be answered at fuel
`fh - 1`, because the new head is then at most `fh - 1`; a call that keeps the head and
descends in the tail is answered by the level-`k` runner, whose own fuel is the tail.
`lexHead_fuel_irrelevant` is the lemma that the fuel is slack — running at any sufficient
fuel gives the same answer as running at exactly the head — and it is what makes
`LexRun_unfold` true.
-/

namespace LakeJs.Lex

/-! ## Vectors of naturals -/

/-- The value of a `k`-component termination measure. -/
inductive NatVec : Nat → Type
  /-- No components. -/
  | nil : NatVec 0
  /-- One more component, more significant than the ones after it. -/
  | cons : ∀ {k : Nat}, Nat → NatVec k → NatVec (k + 1)

namespace NatVec

/-- The most significant component. -/
def head : ∀ {k : Nat}, NatVec (k + 1) → Nat
  | _, .cons a _ => a

/-- Everything but the most significant component. -/
def tail : ∀ {k : Nat}, NatVec (k + 1) → NatVec k
  | _, .cons _ t => t

@[simp] theorem head_cons {k : Nat} (a : Nat) (t : NatVec k) : (NatVec.cons a t).head = a :=
  rfl

@[simp] theorem tail_cons {k : Nat} (a : Nat) (t : NatVec k) : (NatVec.cons a t).tail = t :=
  rfl

/-- A vector of `k + 1` components is a head and a tail. -/
theorem cons_head_tail {k : Nat} (v : NatVec (k + 1)) : NatVec.cons v.head v.tail = v := by
  cases v with
  | cons a t => rfl

/-- The only vector of no components. -/
theorem eq_nil (v : NatVec 0) : v = .nil := by
  cases v; rfl

/-- **The lexicographic order**, most significant component first. -/
inductive Lt : ∀ {k : Nat}, NatVec k → NatVec k → Prop
  /-- The most significant component descends; the rest is free. -/
  | head : ∀ {k : Nat} {a b : Nat} {xs ys : NatVec k}, a < b → Lt (.cons a xs) (.cons b ys)
  /-- The most significant component is kept and the rest descends. -/
  | tail : ∀ {k : Nat} {a : Nat} {xs ys : NatVec k}, Lt xs ys → Lt (.cons a xs) (.cons a ys)

/-- The lexicographic order, as a decision procedure: this is what the evaluator's guard
    computes. -/
def lt : ∀ {k : Nat}, NatVec k → NatVec k → Bool
  | 0, _, _ => false
  | _ + 1, .cons a xs, .cons b ys => if a < b then true else if a = b then lt xs ys else false

/-- Nothing descends below the empty vector. -/
theorem not_lt_nil (v : NatVec 0) : ¬ Lt v .nil := by
  intro h
  cases h

/-- The decision procedure decides the order. -/
theorem lt_iff : ∀ {k : Nat} (x y : NatVec k), x.lt y = true ↔ Lt x y
  | 0, x, y => by
      cases NatVec.eq_nil x
      cases NatVec.eq_nil y
      constructor
      · intro h; exact absurd h (by simp [NatVec.lt])
      · intro h; exact absurd h (not_lt_nil _)
  | _ + 1, .cons a xs, .cons b ys => by
      constructor
      · intro h
        by_cases hab : a < b
        · exact Lt.head hab
        · by_cases hab' : a = b
          · subst hab'
            have : xs.lt ys = true := by
              simpa [NatVec.lt, hab] using h
            exact Lt.tail ((lt_iff xs ys).mp this)
          · simp [NatVec.lt, hab, hab'] at h
      · intro h
        cases h with
        | head hab => simp [NatVec.lt, hab]
        | tail hxy =>
            have : xs.lt ys = true := (lt_iff xs ys).mpr hxy
            simp [NatVec.lt, this]

/-- The guard is false exactly when the call does not descend. -/
theorem lt_eq_false_iff {k : Nat} (x y : NatVec k) : x.lt y = false ↔ ¬ Lt x y := by
  constructor
  · intro h hlt
    have := (lt_iff x y).mpr hlt
    rw [h] at this
    exact Bool.noConfusion this
  · intro h
    cases hb : x.lt y with
    | false => rfl
    | true => exact absurd ((lt_iff x y).mp hb) h

/-- Nothing descends below itself: a self call at an unchanged measure is refused. -/
theorem lt_irrefl : ∀ {k : Nat} (v : NatVec k), ¬ Lt v v
  | 0, v, h => by
      cases NatVec.eq_nil v
      exact not_lt_nil _ h
  | _ + 1, .cons a t, h => by
      cases h with
      | head hab => exact absurd hab (Nat.lt_irrefl a)
      | tail hlt => exact lt_irrefl t hlt

/-- With one component the lexicographic order is `Nat`'s own. -/
theorem lt_one_iff (a b : Nat) :
    Lt (NatVec.cons a .nil) (NatVec.cons b .nil) ↔ a < b := by
  constructor
  · intro h
    cases h with
    | head hab => exact hab
    | tail hlt => exact absurd hlt (not_lt_nil _)
  · exact Lt.head

/-- A vector with a fixed head is accessible as soon as its tail is, provided everything
    with a smaller head already is. -/
private theorem accCons {k : Nat} {a : Nat}
    (hprev : ∀ (b : Nat) (u : NatVec k), b < a → Acc (Lt (k := k + 1)) (.cons b u)) :
    ∀ (t : NatVec k), Acc (Lt (k := k)) t → Acc (Lt (k := k + 1)) (.cons a t) := by
  intro t ht
  induction ht with
  | intro t _ iht =>
    refine Acc.intro _ (fun w hw => ?_)
    cases hw with
    | head hab => exact hprev _ _ hab
    | tail hlt => exact iht _ hlt

/-- **The lexicographic order is well founded.**  This is what a faithfulness proof
    inducts on; the evaluator does not use it. -/
theorem acc : ∀ {k : Nat} (v : NatVec k), Acc (Lt (k := k)) v
  | 0, v => by
      cases NatVec.eq_nil v
      exact Acc.intro _ (fun _ h => absurd h (not_lt_nil _))
  | k + 1, v => by
      cases v with
      | cons a t =>
        induction a using Nat.strongRecOn generalizing t with
        | _ a iha => exact accCons (fun b u hb => iha b hb u) t (acc t)

end NatVec

/-! ## The runner -/

open NatVec

/-- The body of a `k + 1`-component run, specialised to a fixed head value `a`.

    `recT` is the level-`k` runner's guarded self-reference — it answers a call that keeps
    the head `a` and descends in the tail — and `below b u` answers a call that descends
    in the head, to `b < a`.  Anything else gets `dflt`. -/
def lexAt {k : Nat} {γ : Type u} (dflt : γ)
    (F : (NatVec (k + 1) → γ) → NatVec (k + 1) → γ) (below : Nat → NatVec k → γ)
    (a : Nat) (recT : NatVec k → γ) (t : NatVec k) : γ :=
  F (fun w =>
      if w.head = a then recT w.tail
      else if w.head < a then below w.head w.tail
      else dflt)
    (.cons a t)

/-- **Restarting the run at a smaller head.**  `lexBelow run dflt F fuel b t` is the run at
    the bound `(b, t)`, for any `b < fuel`.  It is `Nat.rec` on the fuel, walking down from
    `fuel` to `b` — so the kernel computes it, and the total walking a whole run does is
    bounded by the head component it started from.

    Note what the walk buys: the head the restarted run compares against is the *literal*
    the recursor produced, not an expression to be recomputed.  A version that kept the
    head symbolically inside the self-reference would make each activation capture the
    arguments of the one before it, and the term the kernel reduces would grow
    exponentially with the depth of the recursion. -/
def lexBelow {k : Nat} {γ : Type u}
    (run : ((NatVec k → γ) → NatVec k → γ) → NatVec k → γ) (dflt : γ)
    (F : (NatVec (k + 1) → γ) → NatVec (k + 1) → γ) : Nat → Nat → NatVec k → γ :=
  Nat.rec (motive := fun _ => Nat → NatVec k → γ)
    (fun _ _ => dflt)
    (fun fh below b t => if b = fh then run (lexAt dflt F below fh) t else below b t)

@[simp] theorem lexBelow_zero {k : Nat} {γ : Type u}
    (run : ((NatVec k → γ) → NatVec k → γ) → NatVec k → γ) (dflt : γ)
    (F : (NatVec (k + 1) → γ) → NatVec (k + 1) → γ) (b : Nat) (t : NatVec k) :
    lexBelow run dflt F 0 b t = dflt := rfl

@[simp] theorem lexBelow_succ {k : Nat} {γ : Type u}
    (run : ((NatVec k → γ) → NatVec k → γ) → NatVec k → γ) (dflt : γ)
    (F : (NatVec (k + 1) → γ) → NatVec (k + 1) → γ) (fh b : Nat) (t : NatVec k) :
    lexBelow run dflt F (fh + 1) b t =
      if b = fh then run (lexAt dflt F (lexBelow run dflt F fh) fh) t
      else lexBelow run dflt F fh b t := rfl

/-- **The runner.**  `LexRun k dflt F v` runs the body `F` at the bound `v`, answering
    `dflt` for any self call that does not descend lexicographically.  It is structural
    recursion on the number of components with `Nat.rec` on the head at each level, so it
    reduces in the kernel — `LexRun_unfold` is the equation it satisfies. -/
def LexRun : (k : Nat) → {γ : Type u} → γ → ((NatVec k → γ) → NatVec k → γ) →
    NatVec k → γ
  | 0, _, dflt, F, _ => F (fun _ => dflt) .nil
  | k + 1, _, dflt, F, v =>
      LexRun k dflt (lexAt dflt F (lexBelow (LexRun k dflt) dflt F v.head) v.head) v.tail

@[simp] theorem LexRun_zero {γ : Type u} (dflt : γ)
    (F : (NatVec 0 → γ) → NatVec 0 → γ) (v : NatVec 0) :
    LexRun 0 dflt F v = F (fun _ => dflt) .nil := rfl

@[simp] theorem LexRun_succ {k : Nat} {γ : Type u} (dflt : γ)
    (F : (NatVec (k + 1) → γ) → NatVec (k + 1) → γ) (v : NatVec (k + 1)) :
    LexRun (k + 1) dflt F v =
      LexRun k dflt (lexAt dflt F (lexBelow (LexRun k dflt) dflt F v.head) v.head)
        v.tail := rfl

/-- The runner only looks at its body, so extensionally equal bodies run the same. -/
theorem LexRun_congr {k : Nat} {γ : Type u} (dflt : γ)
    {F₁ F₂ : (NatVec k → γ) → NatVec k → γ}
    (h : ∀ rec v, F₁ rec v = F₂ rec v) (v : NatVec k) :
    LexRun k dflt F₁ v = LexRun k dflt F₂ v := by
  have : F₁ = F₂ := by
    funext rec w
    exact h rec w
  rw [this]

/-- **Restarting is running.**  Walking the fuel down to `b` gives the run at `b`. -/
theorem lexBelow_eq {k : Nat} {γ : Type u} (dflt : γ)
    (F : (NatVec (k + 1) → γ) → NatVec (k + 1) → γ) :
    ∀ (fuel b : Nat) (u : NatVec k), b < fuel →
      lexBelow (LexRun k dflt) dflt F fuel b u = LexRun (k + 1) dflt F (.cons b u)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, b, u, h => by
      rw [lexBelow_succ]
      by_cases hb : b = fuel
      · subst hb
        rw [if_pos rfl]
        rfl
      · rw [if_neg hb]
        exact lexBelow_eq dflt F fuel b u (by omega)

/-- **The equation the runner satisfies.**  This is the whole specification of `LexRun`:
    the body is run once at the bound `v`, with a self-reference that answers the run at
    `w` when `w` descends lexicographically and `dflt` when it does not.  No fuel appears
    in it. -/
theorem LexRun_unfold : ∀ (k : Nat) {γ : Type u} (dflt : γ)
    (F : (NatVec k → γ) → NatVec k → γ) (v : NatVec k),
    LexRun k dflt F v = F (fun w => if w.lt v then LexRun k dflt F w else dflt) v
  | 0, _, dflt, F, v => by
      cases NatVec.eq_nil v
      show F (fun _ => dflt) .nil = _
      congr 1
      funext w
      cases NatVec.eq_nil w
      rfl
  | k + 1, γ, dflt, F, v => by
      have hv : NatVec.cons v.head v.tail = v := NatVec.cons_head_tail v
      rw [LexRun_succ,
        LexRun_unfold k dflt
          (lexAt dflt F (lexBelow (LexRun k dflt) dflt F v.head) v.head) v.tail]
      show F _ (NatVec.cons v.head v.tail) = _
      rw [hv]
      congr 1
      funext w
      have hw : NatVec.cons w.head w.tail = w := NatVec.cons_head_tail w
      by_cases h1 : w.head = v.head
      · -- same head: the guard is the tail's guard, and the run is the same run
        have hlt : w.lt v = w.tail.lt v.tail := by
          rw [← hw, ← hv, h1]
          show (if v.head < v.head then true
                else if v.head = v.head then w.tail.lt v.tail else false) = _
          simp
        simp only [h1, if_true, hlt]
        by_cases h2 : w.tail.lt v.tail = true
        · simp only [h2, if_true]
          show LexRun k dflt
              (lexAt dflt F (lexBelow (LexRun k dflt) dflt F v.head) v.head) w.tail
              = LexRun (k + 1) dflt F w
          rw [LexRun_succ, h1]
        · simp only [h2]
          rfl
      · by_cases h2 : w.head < v.head
        · -- smaller head: the call restarts the run there
          have hlt : w.lt v = true := by
            rw [← hw, ← hv]
            show (if w.head < v.head then true else _) = true
            simp [h2]
          simp only [h1, h2, if_false, if_true, hlt]
          show lexBelow (LexRun k dflt) dflt F v.head w.head w.tail
              = LexRun (k + 1) dflt F w
          rw [lexBelow_eq dflt F v.head w.head w.tail h2, hw]
        · -- larger head: the call does not descend
          have hlt : w.lt v = false := by
            rw [← hw, ← hv]
            show (if w.head < v.head then true
                  else if w.head = v.head then w.tail.lt v.tail else false) = false
            simp [h1, h2]
          simp [h1, h2, hlt]

/-! ## The guarded recursion, as the evaluator uses it -/

/-- **A guarded recursion.**  `guardedFix m stuck step` is the function that, at an
    argument `as`, runs `step` with a self-reference which

    * answers `guardedFix m stuck step bs` when the measure of `bs` is lexicographically
      **strictly smaller** than the measure of the arguments the current activation was
      entered with, and
    * answers `stuck bs` when it is not.

    Termination is by construction: the bound only ever descends, and `LexRun` is built
    from `Nat.rec`. -/
def guardedFix {k : Nat} {α : Type u} {β : Type u} (m : α → NatVec k) (stuck : α → β)
    (step : (α → β) → α → β) (as : α) : β :=
  LexRun k stuck (fun rec _ => step (fun bs => rec (m bs) bs)) (m as) as

/-- The bound a call is measured against is the measure of the arguments of the
    activation it is made from: `guardedFix` runs `step` once, with the guarded self
    reference. -/
theorem guardedFix_unfold {k : Nat} {α β : Type u} (m : α → NatVec k) (stuck : α → β)
    (step : (α → β) → α → β) (as : α) :
    guardedFix m stuck step as =
      step (fun bs => if (m bs).lt (m as) then guardedFix m stuck step bs else stuck bs) as := by
  show LexRun k stuck (fun rec _ => step (fun bs => rec (m bs) bs)) (m as) as = _
  rw [LexRun_unfold k stuck (fun rec _ => step (fun bs => rec (m bs) bs)) (m as)]
  congr 1
  funext bs
  by_cases h : (m bs).lt (m as) = true
  · simp only [h, if_true]
    rfl
  · simp only [h, Bool.false_eq_true, if_false]

/-- A guarded recursion depends on its measure, its `stuck` branch and its body only
    through their values, so pointwise-equal ones give the same function.  This is what a
    substitution lemma about the evaluator needs. -/
theorem guardedFix_congr {k : Nat} {α β : Type u} {m₁ m₂ : α → NatVec k}
    {s₁ s₂ : α → β} {F₁ F₂ : (α → β) → α → β}
    (hm : ∀ a, m₁ a = m₂ a) (hs : ∀ a, s₁ a = s₂ a) (hF : ∀ g a, F₁ g a = F₂ g a) :
    guardedFix m₁ s₁ F₁ = guardedFix m₂ s₂ F₂ := by
  have em : m₁ = m₂ := funext hm
  have es : s₁ = s₂ := funext hs
  have eF : F₁ = F₂ := by
    funext g a
    exact hF g a
  rw [em, es, eF]

/-- **A guarded recursion computes the function it was translated from.**  The only
    hypothesis is the one Lean's `decreasing_by` proves: the body is faithful whenever its
    self-reference is faithful at every *strictly smaller* measure.  There is no bound to
    get right — the guard is the bound. -/
theorem guardedFix_eq {k : Nat} {α β : Type u} (m : α → NatVec k) (stuck : α → β)
    (step : (α → β) → α → β) (f : α → β)
    (hstep : ∀ (g : α → β) (as : α),
      (∀ bs : α, NatVec.Lt (m bs) (m as) → g bs = f bs) → step g as = f as)
    (as : α) : guardedFix m stuck step as = f as := by
  -- well-founded induction on the measure of the arguments
  have main : ∀ (v : NatVec k), Acc (NatVec.Lt (k := k)) v →
      ∀ as : α, m as = v → guardedFix m stuck step as = f as := by
    intro v hv
    induction hv with
    | intro v _ ih =>
      intro as has
      rw [guardedFix_unfold]
      refine hstep _ as (fun bs hbs => ?_)
      have hlt : (m bs).lt (m as) = true := (NatVec.lt_iff _ _).mpr hbs
      rw [hlt]
      simp only [if_true]
      exact ih (m bs) (has ▸ hbs) bs rfl
  exact main (m as) (NatVec.acc _) as rfl

/-! ## The kernel computes it

These are not tests of a library function; they are the property the evaluator of
`LakeJs.Reduce` depends on.  A recursion run by `WellFounded.fix` would leave each of the
following stuck on an `Acc.rec`, and every `rfl` check of a term's value in
`LakeJs.Examples` would have to become a `native_decide`. -/

/-- A one-component measure: count down from `n`, summing. -/
private def sumDown (n : Nat) : Nat :=
  guardedFix (k := 1) (fun n => .cons n .nil) (fun _ => 0)
    (fun self n => match n with | 0 => 0 | m + 1 => (m + 1) + self m) n

example : sumDown 0 = 0 := rfl
example : sumDown 10 = 55 := rfl
example : sumDown 200 = 20100 := by native_decide

/-- A two-component measure: Ackermann, as **one** recursion on `(m, n)`. -/
private def ack2 (m n : Nat) : Nat :=
  guardedFix (k := 2) (fun p => .cons p.1 (.cons p.2 .nil)) (fun _ => 0)
    (fun self p =>
      match p with
      | (0, n) => n + 1
      | (m + 1, 0) => self (m, 1)
      | (m + 1, n + 1) => self (m, self (m + 1, n)))
    (m, n)

example : ack2 0 5 = 6 := rfl
example : ack2 2 3 = 9 := rfl
example : ack2 3 3 = 61 := by native_decide

/-- A call that does **not** descend answers the `stuck` value — it does not hang, and it
    does not answer something else. -/
private def notDescending (n : Nat) : Nat :=
  guardedFix (k := 1) (fun n => .cons n .nil) (fun _ => 99) (fun self n => self (n + 1)) n

example : notDescending 3 = 99 := rfl

end LakeJs.Lex

end
