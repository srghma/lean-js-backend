module

public import LakeJs.Expr

@[expose] public section

set_option autoImplicit false

/-!
# No binder for nothing: the usage discipline

A `Term` may bind a name the rest of it never reads, and nothing in the *type* of `Term`
stops it.  This module says what it means for a term to bind nothing for nothing, and
`WellUsedTerm` is the type of the terms that keep to it.

## The rules

| binder | condition |
| :-- | :-- |
| `Term.lam` | the parameter is read **at least once** |
| `Term.letE`, `Tail.letT` | the bound value is read **at least twice** |
| `Alts.cons`, `AltsT.cons` | every field the alternative binds is read at least once |
| `Tail.join` | it is **jumped to at least once** from the block it is in scope in, and each of its arguments is read at least once in its body |
| `Term.fix` | it **calls itself at least once**, and each of its parameters is read at least once in its body |

The reason a `let` needs *two* readers is that with one reader it shares nothing: the
value belongs where it is read, and the binding is a name for nothing.  With none it is
dead.  A function parameter, by contrast, needs only one reader — its arity is part of
the type `σ ⇒ τ`, and dropping it would change the type.

A `Term.fix` that never calls itself is not a recursion: it is a function whose measure is
computed for nothing, and the rule refuses it, exactly as it refuses a join point nothing
jumps to.

## How the counting works

`Term.occ t i` is the number of times `t` reads the variable whose de Bruijn index is
`i`, counted *from the outside*: a binder that binds `n` variables shifts the index it
asks its body for by `n`.  `Tail.locc b i` does the same for jumps to the label whose
index in `Ω` is `i`, and `Term.rocc t i` for calls to the recursion whose index in `Ρ` is
`i`.  A `Term` contributes nothing to `locc`, since a term holds no labels at all.  All
three are ordinary `Nat`s, so the conditions are decidable and `Term.usesOk` is a `Bool`.

## Why this is a predicate rather than a field of the constructors

The natural wish is to put the condition *inside* `Term`, so that a term that binds a
name for nothing cannot be written at all:

```
| lam : (b : Term Sg (σ :: Γ) Ρ τ) → (h : 1 ≤ b.occ 0) → Term Sg Γ Ρ (σ ⇒ τ)
```

That is **induction–recursion** — `Term` and `Term.occ` defined at the same time — and
Lean 4 has no induction–recursion, so it is not writable.  The two ways to get the
condition into the type proper are to index `Term` by the usage of each variable (a
quantitative type system with the grades `0`, `1`, `2`, `ω`) or to keep this predicate and
work with the subtype; this module is the second, and `WellUsedTerm` is the subtype.

Note the contrast with the *termination* discipline, which is **not** a predicate: there
is no check that a recursion decreases, because `Term.fix` carries its measure and
`Term.selfCall` cannot name one.  Usage is a matter of taste about generated code;
termination is a matter of soundness, and soundness is in the grammar.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Counting the reads of a variable -/

mutual

/-- How many times a term reads the variable of de Bruijn index `i`. -/
def Term.occ : ∀ {Γ : Ctx} {Ρ : RCtx} {τ : Ty}, Term Sg Γ Ρ τ → Nat → Nat
  | _, _, _, .var v, i => if v.index = i then 1 else 0
  | _, _, _, .lam b, i => b.occ (i + 1)
  | _, _, _, .ap f a, i => f.occ i + a.occ i
  | _, _, _, .lit _, _ => 0
  | _, _, _, .global _, _ => 0
  | _, _, _, .extern _, _ => 0
  | _, _, _, .lazyMk e, i => e.occ i
  | _, _, _, .lazyForce e, i => e.occ i
  | _, _, _, .letE e b, i => e.occ i + b.occ (i + 1)
  | _, _, _, .ite c t e, i => c.occ i + t.occ i + e.occ i
  | _, _, _, .ctor _ _ _ args, i => args.occ i
  | _, _, _, .proj e _ _ _ _, i => e.occ i
  | _, _, _, .tagOf e _, i => e.occ i
  | _, _, _, .structSize e, i => e.occ i
  | _, _, _, .caseTag e alts _, i => e.occ i + alts.occ i
  | _, _, _, .block b, i => b.occ i
  | _, _, _, .fix ps _ measure body stuck, i =>
      measure.occ (i + ps.length) + body.occ (i + ps.length) + stuck.occ (i + ps.length)
  | _, _, _, .selfCall _ args, i => args.occ i

/-- The same, over a spine. -/
def Spine.occ : ∀ {Γ : Ctx} {Ρ : RCtx} {σs : List Ty}, Spine Sg Γ Ρ σs → Nat → Nat
  | _, _, _, .nil, _ => 0
  | _, _, _, .cons t rest, i => t.occ i + rest.occ i

/-- The same, over the branches of a case.  An alternative binds the fields of its
    constructor, so the index its body is asked for is shifted by their number. -/
def Alts.occ : ∀ {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ Ρ σ τ tags full → Nat → Nat
  | _, _, _, _, _, _, .deflt t, i => t.occ i
  | _, _, _, _, _, _, .nilFull, _ => 0
  | _, _, _, _, _, _, .cons _ fields _ t rest, i =>
      t.occ (i + fields.length) + rest.occ i

/-- The same, over a tail. -/
def Tail.occ : ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty}, Tail Sg Γ Ω Ρ τ → Nat → Nat
  | _, _, _, _, .ret t, i => t.occ i
  | _, _, _, _, .jmp _ args, i => args.occ i
  | _, _, _, _, .letT e b, i => e.occ i + b.occ (i + 1)
  | _, _, _, _, .iteT c t e, i => c.occ i + t.occ i + e.occ i
  | _, _, _, _, .caseT e alts _, i => e.occ i + alts.occ i
  | _, _, _, _, .join ps body rest, i => body.occ (i + ps.length) + rest.occ i

/-- The same, over the branches of a dispatch inside a block. -/
def AltsT.occ : ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat}
    {full : Bool}, AltsT Sg Γ Ω Ρ σ τ tags full → Nat → Nat
  | _, _, _, _, _, _, _, .deflt b, i => b.occ i
  | _, _, _, _, _, _, _, .nilFull, _ => 0
  | _, _, _, _, _, _, _, .cons _ fields _ b rest, i =>
      b.occ (i + fields.length) + rest.occ i

end

/-! ## Counting the jumps to a label

Only a `Tail` can jump, so this counts nothing inside a `Term` — including inside a
`Term.block`, whose jumps target labels of its own. -/

mutual

/-- How many times a tail jumps to the label of index `i`. -/
def Tail.locc : ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty}, Tail Sg Γ Ω Ρ τ → Nat → Nat
  | _, _, _, _, .ret _, _ => 0
  | _, _, _, _, .jmp l _, i => if l.index = i then 1 else 0
  | _, _, _, _, .letT _ b, i => b.locc i
  | _, _, _, _, .iteT _ t e, i => t.locc i + e.locc i
  | _, _, _, _, .caseT _ alts _, i => alts.locc i
  | _, _, _, _, .join _ body rest, i => body.locc i + rest.locc (i + 1)

/-- The same, over the branches of a dispatch inside a block. -/
def AltsT.locc : ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat}
    {full : Bool}, AltsT Sg Γ Ω Ρ σ τ tags full → Nat → Nat
  | _, _, _, _, _, _, _, .deflt b, i => b.locc i
  | _, _, _, _, _, _, _, .nilFull, _ => 0
  | _, _, _, _, _, _, _, .cons _ _ _ b rest, i => b.locc i + rest.locc i

end

/-! ## Counting the calls to a recursion -/

mutual

/-- How many times a term calls the recursion of index `i`. -/
def Term.rocc : ∀ {Γ : Ctx} {Ρ : RCtx} {τ : Ty}, Term Sg Γ Ρ τ → Nat → Nat
  | _, _, _, .var _, _ => 0
  | _, _, _, .lam b, i => b.rocc i
  | _, _, _, .ap f a, i => f.rocc i + a.rocc i
  | _, _, _, .lit _, _ => 0
  | _, _, _, .global _, _ => 0
  | _, _, _, .extern _, _ => 0
  | _, _, _, .lazyMk e, i => e.rocc i
  | _, _, _, .lazyForce e, i => e.rocc i
  | _, _, _, .letE e b, i => e.rocc i + b.rocc i
  | _, _, _, .ite c t e, i => c.rocc i + t.rocc i + e.rocc i
  | _, _, _, .ctor _ _ _ args, i => args.rocc i
  | _, _, _, .proj e _ _ _ _, i => e.rocc i
  | _, _, _, .tagOf e _, i => e.rocc i
  | _, _, _, .structSize e, i => e.rocc i
  | _, _, _, .caseTag e alts _, i => e.rocc i + alts.rocc i
  | _, _, _, .block b, i => b.rocc i
  | _, _, _, .fix _ _ measure body stuck, i =>
      measure.rocc i + body.rocc (i + 1) + stuck.rocc i
  | _, _, _, .selfCall r args, i => (if r.index = i then 1 else 0) + args.rocc i

/-- The same, over a spine. -/
def Spine.rocc : ∀ {Γ : Ctx} {Ρ : RCtx} {σs : List Ty}, Spine Sg Γ Ρ σs → Nat → Nat
  | _, _, _, .nil, _ => 0
  | _, _, _, .cons t rest, i => t.rocc i + rest.rocc i

/-- The same, over the branches of a case. -/
def Alts.rocc : ∀ {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ Ρ σ τ tags full → Nat → Nat
  | _, _, _, _, _, _, .deflt t, i => t.rocc i
  | _, _, _, _, _, _, .nilFull, _ => 0
  | _, _, _, _, _, _, .cons _ _ _ t rest, i => t.rocc i + rest.rocc i

/-- The same, over a tail. -/
def Tail.rocc : ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty}, Tail Sg Γ Ω Ρ τ → Nat → Nat
  | _, _, _, _, .ret t, i => t.rocc i
  | _, _, _, _, .jmp _ args, i => args.rocc i
  | _, _, _, _, .letT e b, i => e.rocc i + b.rocc i
  | _, _, _, _, .iteT c t e, i => c.rocc i + t.rocc i + e.rocc i
  | _, _, _, _, .caseT e alts _, i => e.rocc i + alts.rocc i
  | _, _, _, _, .join _ body rest, i => body.rocc i + rest.rocc i

/-- The same, over the branches of a dispatch inside a block. -/
def AltsT.rocc : ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat}
    {full : Bool}, AltsT Sg Γ Ω Ρ σ τ tags full → Nat → Nat
  | _, _, _, _, _, _, _, .deflt b, i => b.rocc i
  | _, _, _, _, _, _, _, .nilFull, _ => 0
  | _, _, _, _, _, _, _, .cons _ _ _ b rest, i => b.rocc i + rest.rocc i

end

/-- Are the `n` innermost variables all read, by something that counts reads like
    `Term.occ`? -/
def allRead (n : Nat) (f : Nat → Nat) : Bool :=
  (List.range n).all fun i => 1 ≤ f i

/-! ## The discipline -/

mutual

/-- Does this term bind nothing for nothing?  See this module's header for the rules. -/
def Term.usesOk : ∀ {Γ : Ctx} {Ρ : RCtx} {τ : Ty}, Term Sg Γ Ρ τ → Bool
  | _, _, _, .var _ => true
  | _, _, _, .lit _ => true
  | _, _, _, .global _ => true
  | _, _, _, .extern _ => true
  | _, _, _, .lam b => decide (1 ≤ b.occ 0) && b.usesOk
  | _, _, _, .ap f a => f.usesOk && a.usesOk
  | _, _, _, .lazyMk e => e.usesOk
  | _, _, _, .lazyForce e => e.usesOk
  | _, _, _, .letE e b => decide (2 ≤ b.occ 0) && e.usesOk && b.usesOk
  | _, _, _, .ite c t e => c.usesOk && t.usesOk && e.usesOk
  | _, _, _, .ctor _ _ _ args => args.usesOk
  | _, _, _, .proj e _ _ _ _ => e.usesOk
  | _, _, _, .tagOf e _ => e.usesOk
  | _, _, _, .structSize e => e.usesOk
  | _, _, _, .caseTag e alts _ => e.usesOk && alts.usesOk
  | _, _, _, .block b => b.usesOk
  | _, _, _, .fix ps _ measure body stuck =>
      decide (1 ≤ body.rocc 0) && allRead ps.length body.occ &&
        measure.usesOk && body.usesOk && stuck.usesOk
  | _, _, _, .selfCall _ args => args.usesOk

/-- The same, over a spine. -/
def Spine.usesOk : ∀ {Γ : Ctx} {Ρ : RCtx} {σs : List Ty}, Spine Sg Γ Ρ σs → Bool
  | _, _, _, .nil => true
  | _, _, _, .cons t rest => t.usesOk && rest.usesOk

/-- The same, over the branches of a case. -/
def Alts.usesOk : ∀ {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ Ρ σ τ tags full → Bool
  | _, _, _, _, _, _, .deflt t => t.usesOk
  | _, _, _, _, _, _, .nilFull => true
  | _, _, _, _, _, _, .cons _ fields _ t rest =>
      allRead fields.length t.occ && t.usesOk && rest.usesOk

/-- The same, over a tail. -/
def Tail.usesOk : ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty}, Tail Sg Γ Ω Ρ τ → Bool
  | _, _, _, _, .ret t => t.usesOk
  | _, _, _, _, .jmp _ args => args.usesOk
  | _, _, _, _, .letT e b => decide (2 ≤ b.occ 0) && e.usesOk && b.usesOk
  | _, _, _, _, .iteT c t e => c.usesOk && t.usesOk && e.usesOk
  | _, _, _, _, .caseT e alts _ => e.usesOk && alts.usesOk
  | _, _, _, _, .join ps body rest =>
      decide (1 ≤ rest.locc 0) && allRead ps.length body.occ && body.usesOk &&
        rest.usesOk

/-- The same, over the branches of a dispatch inside a block. -/
def AltsT.usesOk : ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat}
    {full : Bool}, AltsT Sg Γ Ω Ρ σ τ tags full → Bool
  | _, _, _, _, _, _, _, .deflt b => b.usesOk
  | _, _, _, _, _, _, _, .nilFull => true
  | _, _, _, _, _, _, _, .cons _ fields _ b rest =>
      allRead fields.length b.occ && b.usesOk && rest.usesOk

end

/-- A term that binds nothing for nothing: the subtype the discipline cuts out. -/
def WellUsedTerm (Sg : Sig) (Γ : Ctx) (Ρ : RCtx) (τ : Ty) : Type :=
  { t : Term Sg Γ Ρ τ // t.usesOk = true }

/-! ## What the discipline refuses

One theorem per rule: the term the rule is about really is refused. -/

/-- A lambda whose parameter is never read is refused. -/
theorem Term.not_usesOk_lam_of_unused {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty}
    {b : Term Sg (σ :: Γ) Ρ τ} (h : b.occ 0 = 0) : (Term.lam b).usesOk = false := by
  simp [Term.usesOk, h]

/-- A `let` whose variable is never read is refused. -/
theorem Term.not_usesOk_letE_of_dead {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty}
    {e : Term Sg Γ Ρ σ} {b : Term Sg (σ :: Γ) Ρ τ} (h : b.occ 0 = 0) :
    (Term.letE e b).usesOk = false := by
  simp [Term.usesOk, h]

/-- A `let` whose variable is read exactly once is refused: it shares nothing, and the
    value belongs where it is read. -/
theorem Term.not_usesOk_letE_of_readOnce {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty}
    {e : Term Sg Γ Ρ σ} {b : Term Sg (σ :: Γ) Ρ τ} (h : b.occ 0 = 1) :
    (Term.letE e b).usesOk = false := by
  simp [Term.usesOk, h]

/-- A join point nothing jumps to is refused. -/
theorem Tail.not_usesOk_join_of_noJump {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {ps : List Ty}
    {τ : Ty} {body : Tail Sg (ps ++ Γ) Ω Ρ τ} {rest : Tail Sg Γ (ps :: Ω) Ρ τ}
    (h : rest.locc 0 = 0) : (Tail.join ps body rest).usesOk = false := by
  simp [Tail.usesOk, h]

/-- A recursion that never calls itself is refused: its measure is computed for
    nothing. -/
theorem Term.not_usesOk_fix_of_noSelfCall {Γ : Ctx} {Ρ : RCtx} {ps : List Ty} {τ : Ty}
    {k : Nat} {measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k)}
    {body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ} {stuck : Term Sg (ps ++ Γ) Ρ τ}
    (h : body.rocc 0 = 0) : (Term.fix ps k measure body stuck).usesOk = false := by
  simp [Term.usesOk, h]

/-! ## Examples -/

/-- The empty signature. -/
private def sigNone : Sig := ⟨[], rfl⟩

/-- `fun x => x` reads its parameter, so it keeps to the discipline. -/
example : (Term.idTerm (Sg := sigNone) (Ρ := []) (τ := Ty.nat)).usesOk = true := by decide

/-- `fun x y => x` does **not**: `y` is bound for nothing. -/
example :
    (Term.const (Sg := sigNone) (Ρ := []) (τ1 := Ty.nat) (τ2 := Ty.nat)).usesOk = false := by
  decide

/-- The join point of `Term.sharedTail` is jumped to from both arms, and its argument is
    read, so it keeps to the discipline. -/
example : (Term.sharedTail (Sg := sigNone) (Ρ := [])).usesOk = true := by decide

/-- So does the recursion of `Term.tco01`: it calls itself, and its parameter is read. -/
example : (Term.tco01 (Sg := sigNone) (Ρ := [])).usesOk = true := by decide

/-- A `let` read once is refused, here by computation rather than by the theorem. -/
example :
    (Term.letE (Sg := sigNone) (Γ := []) (Ρ := []) (σ := Ty.nat)
      (.lit (.nat 1)) (♯0)).usesOk = false := by
  decide

/-- The same `let`, read twice, is accepted. -/
example :
    (Term.letE (Sg := sigNone) (Γ := []) (Ρ := []) (σ := Ty.nat)
      (.lit (.nat 1))
      (.ap (.ap (.extern (.prim2 .lean_nat_add)) (♯0)) (♯0))).usesOk = true := by
  decide

end LakeJs.Expr

end
