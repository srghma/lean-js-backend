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
| `Tail.label` | it is **jumped to at least once** from the block it is in scope in, and each of its arguments is read at least once in its body |

The reason a `let` needs *two* readers is that with one reader it shares nothing: the
value belongs where it is read, and the binding is a name for nothing.  With none it is
dead.  A function parameter, by contrast, needs only one reader — its arity is part of
the type `σ ⇒ τ`, and dropping it would change the type.

A label — a shared tail or a loop, the two being one construct since the block/label
unification — is counted the same way whichever it is: the jumps that matter are the ones
in `rest`, the part of the block the label is in scope in.  A loop whose body jumps back
to it but which nothing ever *enters* is dead code, and the rule refuses it.

## How the counting works

`Term.occ t i` is the number of times `t` reads the variable whose de Bruijn index is
`i`, counted *from the outside*: a binder that binds `n` variables shifts the index it
asks its body for by `n`.  `Tail.locc b i` does the same for jumps to the label whose
index in `Ω` is `i`; a `Term` contributes nothing to it, since a term holds no labels at
all.  Both are ordinary `Nat`s, so the conditions are decidable and `Term.usesOk` is a
`Bool`.

## Why this is a predicate rather than a field of the constructors

The natural wish is to put the condition *inside* `Term`, so that a term that binds a
name for nothing cannot be written at all:

```
| lam : (b : Term Sg (σ :: Γ) τ) → (h : 1 ≤ b.occ 0) → Term Sg Γ (σ ⇒ τ)
```

That is **induction–recursion** — `Term` and `Term.occ` defined at the same time — and
Lean 4 has no induction–recursion, so it is not writable.  The two ways to get the
condition into the type proper are to index `Term` by the usage of each variable (a
quantitative type system with the grades `0`, `1`, `2`, `ω`) or to keep this predicate and
work with the subtype.  What each costs is written up in `USAGE_ENFORCEMENT.md`; this
module is the second, and `WellUsedTerm` is the subtype.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Counting the reads of a variable -/

mutual

/-- How many times a term reads the variable of de Bruijn index `i`. -/
def Term.occ : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Nat → Nat
  | _, _, .var v, i => if v.index = i then 1 else 0
  | _, _, .lam b, i => b.occ (i + 1)
  | _, _, .ap f a, i => f.occ i + a.occ i
  | _, _, .lit _, _ => 0
  | _, _, .global _, _ => 0
  | _, _, .extern _, _ => 0
  | _, _, .lazyMk e, i => e.occ i
  | _, _, .lazyForce e, i => e.occ i
  | _, _, .letE e b, i => e.occ i + b.occ (i + 1)
  | _, _, .ite c t e, i => c.occ i + t.occ i + e.occ i
  | _, _, .ctor _ _ _ args, i => args.occ i
  | _, _, .proj e _ _ _ _, i => e.occ i
  | _, _, .tagOf e _, i => e.occ i
  | _, _, .caseTag e alts _, i => e.occ i + alts.occ i
  | _, _, .block b, i => b.occ i

/-- The same, over a spine. -/
def Spine.occ : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Nat → Nat
  | _, _, .nil, _ => 0
  | _, _, .cons t rest, i => t.occ i + rest.occ i

/-- The same, over the branches of a case. -/
def Alts.occ : ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ τ tags full → Nat → Nat
  | _, _, _, _, .deflt t, i => t.occ i
  | _, _, _, _, .nilFull, _ => 0
  | _, _, _, _, .cons _ t rest, i => t.occ i + rest.occ i

/-- The same, over a tail. -/
def Tail.occ : ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty}, Tail Sg Γ Ω τ → Nat → Nat
  | _, _, _, .ret t, i => t.occ i
  | _, _, _, .jmp _ args, i => args.occ i
  | _, _, _, .letT e b, i => e.occ i + b.occ (i + 1)
  | _, _, _, .iteT c t e, i => c.occ i + t.occ i + e.occ i
  | _, _, _, .caseT e alts _, i => e.occ i + alts.occ i
  | _, _, _, .label (ps := ps) _ body rest, i => body.occ (i + ps.length) + rest.occ i

/-- The same, over the branches of a dispatch inside a block. -/
def AltsT.occ : ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat} {full : Bool},
    AltsT Sg Γ Ω τ tags full → Nat → Nat
  | _, _, _, _, _, .deflt b, i => b.occ i
  | _, _, _, _, _, .nilFull, _ => 0
  | _, _, _, _, _, .cons _ b rest, i => b.occ i + rest.occ i

end

/-! ## Counting the jumps to a label

Only a `Tail` can jump, so this counts nothing inside a `Term` — including inside a
`Term.block`, whose jumps target labels of its own. -/

mutual

/-- How many times a tail jumps to the label of index `i`. -/
def Tail.locc : ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty}, Tail Sg Γ Ω τ → Nat → Nat
  | _, _, _, .ret _, _ => 0
  | _, _, _, .jmp l _, i => if l.index = i then 1 else 0
  | _, _, _, .letT _ b, i => b.locc i
  | _, _, _, .iteT _ t e, i => t.locc i + e.locc i
  | _, _, _, .caseT _ alts _, i => alts.locc i
  | _, _, _, .label self body rest, i =>
      (if self then body.locc (i + 1) else body.locc i) + rest.locc (i + 1)

/-- The same, over the branches of a dispatch inside a block. -/
def AltsT.locc : ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat} {full : Bool},
    AltsT Sg Γ Ω τ tags full → Nat → Nat
  | _, _, _, _, _, .deflt b, i => b.locc i
  | _, _, _, _, _, .nilFull, _ => 0
  | _, _, _, _, _, .cons _ b rest, i => b.locc i + rest.locc i

end

/-- Are the `n` innermost variables all read, by something that counts reads like
    `Term.occ`? -/
def allRead (n : Nat) (f : Nat → Nat) : Bool :=
  (List.range n).all fun i => 1 ≤ f i

/-! ## The discipline -/

mutual

/-- Does this term bind nothing for nothing?  See this module's header for the rules. -/
def Term.usesOk : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Bool
  | _, _, .var _ => true
  | _, _, .lit _ => true
  | _, _, .global _ => true
  | _, _, .extern _ => true
  | _, _, .lam b => decide (1 ≤ b.occ 0) && b.usesOk
  | _, _, .ap f a => f.usesOk && a.usesOk
  | _, _, .lazyMk e => e.usesOk
  | _, _, .lazyForce e => e.usesOk
  | _, _, .letE e b => decide (2 ≤ b.occ 0) && e.usesOk && b.usesOk
  | _, _, .ite c t e => c.usesOk && t.usesOk && e.usesOk
  | _, _, .ctor _ _ _ args => args.usesOk
  | _, _, .proj e _ _ _ _ => e.usesOk
  | _, _, .tagOf e _ => e.usesOk
  | _, _, .caseTag e alts _ => e.usesOk && alts.usesOk
  | _, _, .block b => b.usesOk

/-- The same, over a spine. -/
def Spine.usesOk : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Bool
  | _, _, .nil => true
  | _, _, .cons t rest => t.usesOk && rest.usesOk

/-- The same, over the branches of a case. -/
def Alts.usesOk : ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ τ tags full → Bool
  | _, _, _, _, .deflt t => t.usesOk
  | _, _, _, _, .nilFull => true
  | _, _, _, _, .cons _ t rest => t.usesOk && rest.usesOk

/-- The same, over a tail. -/
def Tail.usesOk : ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty}, Tail Sg Γ Ω τ → Bool
  | _, _, _, .ret t => t.usesOk
  | _, _, _, .jmp _ args => args.usesOk
  | _, _, _, .letT e b => decide (2 ≤ b.occ 0) && e.usesOk && b.usesOk
  | _, _, _, .iteT c t e => c.usesOk && t.usesOk && e.usesOk
  | _, _, _, .caseT e alts _ => e.usesOk && alts.usesOk
  | _, _, _, .label (ps := ps) _ body rest =>
      decide (1 ≤ rest.locc 0) && allRead ps.length body.occ && body.usesOk &&
        rest.usesOk

/-- The same, over the branches of a dispatch inside a block. -/
def AltsT.usesOk : ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat} {full : Bool},
    AltsT Sg Γ Ω τ tags full → Bool
  | _, _, _, _, _, .deflt b => b.usesOk
  | _, _, _, _, _, .nilFull => true
  | _, _, _, _, _, .cons _ b rest => b.usesOk && rest.usesOk

end

/-- A term that binds nothing for nothing: the subtype the discipline cuts out. -/
def WellUsedTerm (Sg : Sig) (Γ : Ctx) (τ : Ty) : Type :=
  { t : Term Sg Γ τ // t.usesOk = true }

/-! ## What the discipline refuses

One theorem per rule: the term the rule is about really is refused. -/

/-- A lambda whose parameter is never read is refused. -/
theorem Term.not_usesOk_lam_of_unused {Γ : Ctx} {σ τ : Ty}
    {b : Term Sg (σ :: Γ) τ} (h : b.occ 0 = 0) : (Term.lam b).usesOk = false := by
  simp [Term.usesOk, h]

/-- A `let` whose variable is never read is refused. -/
theorem Term.not_usesOk_letE_of_dead {Γ : Ctx} {σ τ : Ty}
    {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} (h : b.occ 0 = 0) :
    (Term.letE e b).usesOk = false := by
  simp [Term.usesOk, h]

/-- A `let` whose variable is read exactly once is refused: it shares nothing, and the
    value belongs where it is read. -/
theorem Term.not_usesOk_letE_of_readOnce {Γ : Ctx} {σ τ : Ty}
    {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} (h : b.occ 0 = 1) :
    (Term.letE e b).usesOk = false := by
  simp [Term.usesOk, h]

/-- A label nothing jumps to is refused — a shared tail no branch shares and a loop
    nothing enters alike. -/
theorem Tail.not_usesOk_label_of_noJump {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    {self : Bool} {body : Tail Sg (ps ++ Γ) (LCtx.ext self ps Ω) τ}
    {rest : Tail Sg Γ (ps :: Ω) τ} (h : rest.locc 0 = 0) :
    (Tail.label self body rest).usesOk = false := by
  simp [Tail.usesOk, h]

/-! ## Examples -/

/-- The empty signature. -/
private def sigNone : Sig := ⟨[], rfl⟩

/-- `fun x => x` reads its parameter, so it keeps to the discipline. -/
example : (Term.idTerm (Sg := sigNone) (τ := Ty.nat)).usesOk = true := by decide

/-- `fun x y => x` does **not**: `y` is bound for nothing. -/
example : (Term.const (Sg := sigNone) (τ1 := Ty.nat) (τ2 := Ty.nat)).usesOk = false := by
  decide

/-- The label of `Term.sharedTail` is jumped to from both arms, and its argument is
    read, so it keeps to the discipline. -/
example : (Term.sharedTail (Sg := sigNone)).usesOk = true := by decide

/-- So does the loop of `Term.tco01`: the block enters it, and its loop variable is
    read. -/
example : (Term.tco01 (Sg := sigNone)).usesOk = true := by decide

/-- A `let` read once is refused, here by computation rather than by the theorem. -/
example :
    (Term.letE (Sg := sigNone) (Γ := []) (σ := Ty.nat)
      (.lit (.nat 1)) (♯0)).usesOk = false := by
  decide

/-- The same `let`, read twice, is accepted. -/
example :
    (Term.letE (Sg := sigNone) (Γ := []) (σ := Ty.nat)
      (.lit (.nat 1))
      (.ap (.ap (.extern (.prim2 .lean_nat_add)) (♯0)) (♯0))).usesOk = true := by
  decide

end LakeJs.Expr

end
