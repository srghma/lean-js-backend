module

public import LakeJs.CertGen

@[expose] public section

/-!
# `CTerm`: a term language that **terminates by construction**

`LakeJs.Terminating` implements design **D2** of `TERMINATING_TERM_ASSESSMENT.md`: the
grammar is left alone and a termination certificate is attached *afterwards*, as the
predicate `Term.Terminating`.  This module implements design **D1**, the intrinsic one:
a grammar in which a term that does not terminate **cannot be written down**, because the
obligation sits on the constructor that needs it.

```lean
theorem CTerm.erase_terminating (t : CTerm Sg Γ τ) : t.erase.Terminating
theorem CTerm.sn (t : CTerm Sg [] τ) : t.erase.SN
theorem CTerm.halts (t : CTerm Sg [] τ) : ∃ v, Steps t.erase v ∧ Value v
```

— no side condition anywhere: *every* closed `CTerm` runs out of steps and answers.

## Why this is a second grammar and not a field of `Term`

The obvious reading of "make `Term` terminating by construction" is to add the
certificate as a field of `Term.block`.  That is **impossible as stated**, and the reason
is not an engineering one: the certificate says that the block *runs out of steps*, so it
mentions `Step`, which is a relation on `Term`.  A constructor of `Term` may not mention
a relation defined on `Term`; the definition would not be well founded.  (The same
objection rules out any certificate phrased with the evaluator, the logical relation, or
`SN`.)

Two ways out, and only one of them keeps completeness:

* make the certificate *syntactic* — a decidable shape condition, which can be checked
  while `Term` is being built.  By the diagonal argument of the assessment (§2) any such
  condition is incomplete: it must reject terminating programs, and a Lean function whose
  termination proof is hard is exactly the kind it rejects.
* keep the semantic certificate and **stratify**: build the plain grammar first, define
  `Step`, `SN` and `Tail.Certified` on it, and then define a second grammar whose
  constructors take the certificate.  This is what is done here.

The stratification costs nothing in expressiveness, and the two grammars are proved to
have exactly the same reach:

```lean
def  CTerm.ofTerminating (t : Term Sg Γ τ) (h : t.Terminating) : CTerm Sg Γ τ
theorem CTerm.erase_ofTerminating : (CTerm.ofTerminating t h).erase = t
```

so `CTerm` is the certified language of `LakeJs.Terminating`, *intrinsically* packaged:
`erase` and `ofTerminating` are mutually inverse up to the proof fields, which are
`Prop`s and therefore irrelevant.

## Where the obligation actually lands

Only two constructors ask for anything beyond what `Term` asks for, and they are the two
places where `Term.Terminating` is not automatic:

* `CTerm.block` takes the block's certificate `b.Certified` (and `Ty.ground` on its answer
  type, the standing restriction of `LakeJs.Fragment` — see below);
* `CTerm.proj` takes `Ty.ground` on the type of the field it reads.

Every other constructor is the constructor of `Term`, unchanged: application, `let`,
branches, constructors, externs and `lazy` are terminating whenever their subterms are,
and their subterms are `CTerm`s.  In particular the **λ-calculus core is free**: there is
no fixed point to be had out of `lam`/`ap` at a `Ty`, and with the strict positivity of
`RTy.wf` there is none out of a recursive type either (`LakeJs.DivergeNeg`).

## How a block is built in practice

Writing a `Tail.Certified` by hand is not the intended route.  `LakeJs.CertGen` produces
certificates mechanically for the shapes that admit one, and this module wraps them as
smart constructors, so the *decidable* part of the language needs no proof at the use
site:

* `CTerm.blockFlat` — a block with no label in it;
* `CTerm.blockLoopFree` — a block all of whose labels are join points, nested ones
  included.

What is left for the general constructor is exactly the **loop**, and there the
certificate is the source function's own termination proof, transported
(`TERMINATING_TERM_ASSESSMENT.md` §4.4).  That is the price of completeness, and by §2 of
the assessment no design avoids it.

## What is deliberately *not* claimed

* The plain `Term` stays, and stays uncertified: `SnapshotsPBOPartial` contains genuinely
  `partial` Lean functions, which must remain expressible.  `CTerm` is what a **program**
  is built out of, not what every intermediate data structure is.
* A certified block answers at a value type (`Ty.ground`), and so does a field read; both
  wait on hereditary reducibility for constructors (`LakeJs.Fragment`,
  `LakeJs.Terminating`).  Every compiled root answers with data, so the corpus is not
  affected.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout)

variable {Sg : Sig}

/-! ## The grammar -/

mutual

/-- **A term that terminates by construction.**  Constructor for constructor this is
    `Term`, with the two side conditions of `Term.Terminating` moved onto the
    constructors that need them: a block carries its termination certificate, and a field
    read is at a value type. -/
inductive CTerm (Sg : Sig) : Ctx → Ty → Type
  /-- A variable of `Γ`. -/
  | var : ∀ {Γ τ}, Γ ∋ τ → CTerm Sg Γ τ
  /-- `fun x => body`. -/
  | lam : ∀ {Γ σ τ}, CTerm Sg (σ :: Γ) τ → CTerm Sg Γ (σ ⇒ τ)
  /-- `f a`. -/
  | ap : ∀ {Γ σ τ}, CTerm Sg Γ (σ ⇒ τ) → CTerm Sg Γ σ → CTerm Sg Γ τ
  /-- A constant of a terminal type. -/
  | lit : ∀ {Γ} {p : LeanPrimTy}, LeanPrimLit p → CTerm Sg Γ (.prim p)
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ τ}, GlobalRef Sg.decls τ → CTerm Sg Γ τ
  /-- A function the runtime implements, at the curried type its argument list gives
      it. -/
  | extern : ∀ {Γ σs τ}, Externs σs τ → CTerm Sg Γ (Ty.arrows σs τ)
  /-- Delay a value. -/
  | lazyMk : ∀ {Γ τ}, CTerm Sg Γ τ → CTerm Sg Γ (.lazy τ)
  /-- Run a delayed value. -/
  | lazyForce : ∀ {Γ τ}, CTerm Sg Γ (.lazy τ) → CTerm Sg Γ τ
  /-- `let x = e; body`. -/
  | letE : ∀ {Γ σ τ}, CTerm Sg Γ σ → CTerm Sg (σ :: Γ) τ → CTerm Sg Γ τ
  /-- `if c then t else e`. -/
  | ite : ∀ {Γ τ}, CTerm Sg Γ (.prim .bool) → CTerm Sg Γ τ → CTerm Sg Γ τ → CTerm Sg Γ τ
  /-- A tagged value, built at a type whose layout says so. -/
  | ctor : ∀ {Γ τ}, (i : Nat) → (fields : FieldLayout) →
      (h : τ.ctorFields? i = some fields) → CSpine Sg Γ fields → CTerm Sg Γ τ
  /-- A field of a tagged value.  `hg` is the one extra obligation: the field is read at
      a **value type**, the standing restriction of `LakeJs.Fragment`. -/
  | proj : ∀ {Γ σ τ}, CTerm Sg Γ σ → (i j : Nat) →
      (hOne : σ.numCtors? = some 1) → (h : σ.fieldTy? i j = some τ) →
      (hg : τ.ground = true) → CTerm Sg Γ τ
  /-- The runtime tag of a value whose type has a layout. -/
  | tagOf : ∀ {Γ σ}, CTerm Sg Γ σ → (h : σ.isTagged = true) → CTerm Sg Γ (.prim .nat)
  /-- A dispatch on the tag of a value. -/
  | caseTag : ∀ {Γ σ τ tags full}, CTerm Sg Γ σ → CAlts Sg Γ τ tags full →
      (h : σ.caseOkAlts full tags = true) → CTerm Sg Γ τ
  /-- **A block, with its termination certificate.**  This is the one constructor that
      could repeat work, and the only one that asks for a proof: `cert` says that
      whatever closed values the enclosing context supplies, the block runs out of steps.
      `LakeJs.CertGen` produces it for the loop-free shapes; see `CTerm.blockLoopFree`. -/
  | block : ∀ {Γ τ}, (b : Tail Sg Γ [] τ) → (hg : τ.ground = true) →
      (cert : b.Certified) → CTerm Sg Γ τ

/-- A list of `CTerm`s, typed by the list of their types. -/
inductive CSpine (Sg : Sig) : Ctx → List Ty → Type
  | nil : ∀ {Γ}, CSpine Sg Γ []
  | cons : ∀ {Γ σ σs}, CTerm Sg Γ σ → CSpine Sg Γ σs → CSpine Sg Γ (σ :: σs)

/-- The branches of a `CTerm.caseTag`. -/
inductive CAlts (Sg : Sig) : Ctx → Ty → List Nat → Bool → Type
  /-- The default branch a dispatch ends with. -/
  | deflt : ∀ {Γ τ}, CTerm Sg Γ τ → CAlts Sg Γ τ [] false
  /-- The end of an exhaustive dispatch. -/
  | nilFull : ∀ {Γ τ}, CAlts Sg Γ τ [] true
  | cons : ∀ {Γ τ tags full}, (tag : Nat) → CTerm Sg Γ τ → CAlts Sg Γ τ tags full →
      CAlts Sg Γ τ (tag :: tags) full

end

/-! ## Erasure: a `CTerm` is a `Term` -/

mutual

/-- **Forget the certificates**: the underlying `Term`.  The proofs are `Prop`s, so
    nothing that runs is lost. -/
def CTerm.erase {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, CTerm Sg Γ τ → Term Sg Γ τ
  | _, _, .var v => .var v
  | _, _, .lam b => .lam b.erase
  | _, _, .ap f a => .ap f.erase a.erase
  | _, _, .lit l => .lit l
  | _, _, .global r => .global r
  | _, _, .extern e => .extern e
  | _, _, .lazyMk e => .lazyMk e.erase
  | _, _, .lazyForce e => .lazyForce e.erase
  | _, _, .letE e b => .letE e.erase b.erase
  | _, _, .ite c t e => .ite c.erase t.erase e.erase
  | _, _, .ctor i fields h args => .ctor i fields h args.erase
  | _, _, .proj e i j hOne h _ => .proj e.erase i j hOne h
  | _, _, .tagOf e h => .tagOf e.erase h
  | _, _, .caseTag e alts h => .caseTag e.erase alts.erase h
  | _, _, .block b _ _ => .block b

/-- `CTerm.erase`, on a spine. -/
def CSpine.erase {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, CSpine Sg Γ σs → Spine Sg Γ σs
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons t.erase rest.erase

/-- `CTerm.erase`, on the branches of a dispatch. -/
def CAlts.erase {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool},
    CAlts Sg Γ τ tags full → Alts Sg Γ τ tags full
  | _, _, _, _, .deflt t => .deflt t.erase
  | _, _, _, _, .nilFull => .nilFull
  | _, _, _, _, .cons tag t rest => .cons tag t.erase rest.erase

end

/-! ## The guarantee -/

mutual

/-- **Every `CTerm` is certified.**  There is no side condition: the obligations
    `Term.Terminating` imposes are exactly the fields the constructors carry. -/
theorem CTerm.erase_terminating {Γ : Ctx} {τ : Ty} (t : CTerm Sg Γ τ) :
    t.erase.Terminating :=
  match t with
  | .var _ => trivial
  | .lam b => by
      simpa [CTerm.erase, Term.Terminating] using CTerm.erase_terminating b
  | .ap f a => by
      simp only [CTerm.erase, Term.Terminating]
      exact ⟨CTerm.erase_terminating f, CTerm.erase_terminating a⟩
  | .lit _ => trivial
  | .global _ => trivial
  | .extern _ => trivial
  | .lazyMk e => by
      simpa [CTerm.erase, Term.Terminating] using CTerm.erase_terminating e
  | .lazyForce e => by
      simpa [CTerm.erase, Term.Terminating] using CTerm.erase_terminating e
  | .letE e b => by
      simp only [CTerm.erase, Term.Terminating]
      exact ⟨CTerm.erase_terminating e, CTerm.erase_terminating b⟩
  | .ite c t e => by
      simp only [CTerm.erase, Term.Terminating]
      exact ⟨CTerm.erase_terminating c, CTerm.erase_terminating t,
        CTerm.erase_terminating e⟩
  | .ctor _ _ _ args => by
      simpa [CTerm.erase, Term.Terminating] using CSpine.erase_terminating args
  | .proj e _ _ _ _ hg => by
      simp only [CTerm.erase, Term.Terminating]
      exact ⟨hg, CTerm.erase_terminating e⟩
  | .tagOf e _ => by
      simpa [CTerm.erase, Term.Terminating] using CTerm.erase_terminating e
  | .caseTag e alts _ => by
      simp only [CTerm.erase, Term.Terminating]
      exact ⟨CTerm.erase_terminating e, CAlts.erase_terminating alts⟩
  | .block _ hg cert => by
      simp only [CTerm.erase, Term.Terminating]
      exact ⟨hg, cert⟩
  termination_by sizeOf t

/-- Every term of a `CSpine` is certified. -/
theorem CSpine.erase_terminating {Γ : Ctx} {σs : List Ty} (s : CSpine Sg Γ σs) :
    s.erase.Terminating :=
  match s with
  | .nil => trivial
  | .cons t rest => by
      simp only [CSpine.erase, Spine.Terminating]
      exact ⟨CTerm.erase_terminating t, CSpine.erase_terminating rest⟩
  termination_by sizeOf s

/-- Every branch of a `CAlts` is certified. -/
theorem CAlts.erase_terminating {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool}
    (alts : CAlts Sg Γ τ tags full) : alts.erase.Terminating :=
  match alts with
  | .deflt t => by
      simpa [CAlts.erase, Alts.Terminating] using CTerm.erase_terminating t
  | .nilFull => trivial
  | .cons _ t rest => by
      simp only [CAlts.erase, Alts.Terminating]
      exact ⟨CTerm.erase_terminating t, CAlts.erase_terminating rest⟩
  termination_by sizeOf alts

end

/-- **A closed `CTerm` runs out of steps.** -/
theorem CTerm.sn {τ : Ty} (t : CTerm Sg [] τ) : t.erase.SN :=
  Term.terminating_sn _ t.erase_terminating

/-- **A closed `CTerm` reaches an answer.** -/
theorem CTerm.halts {τ : Ty} (t : CTerm Sg [] τ) :
    ∃ v : Term Sg [] τ, Steps t.erase v ∧ Value v :=
  t.sn.halts

/-- **The answer a closed `CTerm` evaluates to.**  No fuel, no side condition: the
    certificate is part of the term. -/
noncomputable def CTerm.eval {τ : Ty} (t : CTerm Sg [] τ) : Term Sg [] τ :=
  t.erase.eval t.erase_terminating

/-- **Totality, in one statement**: running a closed `CTerm` answers with a value. -/
theorem CTerm.eval_total {τ : Ty} (t : CTerm Sg [] τ) :
    Steps t.erase t.eval ∧ Value t.eval :=
  t.erase.eval_total t.erase_terminating

/-- A `CTerm` is a `CertifiedTerm` — the D2 packaging — with no work to do. -/
def CTerm.toCertifiedTerm {Γ : Ctx} {τ : Ty} (t : CTerm Sg Γ τ) : CertifiedTerm Sg Γ τ :=
  ⟨t.erase, t.erase_terminating⟩

/-! ## Nothing that terminates is lost

The intrinsic grammar is not a restriction of the certified language: every term the
extrinsic predicate admits is the erasure of a `CTerm`, and the two are inverse. -/

mutual

/-- **A certified term, intrinsically.**  The converse of `CTerm.erase_terminating`: the
    certificate of a `Term.Terminating` term is dismantled into the fields the
    constructors of `CTerm` ask for. -/
def CTerm.ofTerminating {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ),
    t.Terminating → CTerm Sg Γ τ
  | _, _, .var v, _ => .var v
  | _, _, .lam b, h => .lam (CTerm.ofTerminating b h)
  | _, _, .ap f a, h => .ap (CTerm.ofTerminating f h.1) (CTerm.ofTerminating a h.2)
  | _, _, .lit l, _ => .lit l
  | _, _, .global r, _ => .global r
  | _, _, .extern e, _ => .extern e
  | _, _, .lazyMk e, h => .lazyMk (CTerm.ofTerminating e h)
  | _, _, .lazyForce e, h => .lazyForce (CTerm.ofTerminating e h)
  | _, _, .letE e b, h => .letE (CTerm.ofTerminating e h.1) (CTerm.ofTerminating b h.2)
  | _, _, .ite c t e, h =>
      .ite (CTerm.ofTerminating c h.1) (CTerm.ofTerminating t h.2.1)
        (CTerm.ofTerminating e h.2.2)
  | _, _, .ctor i fields hf args, h => .ctor i fields hf (CSpine.ofTerminating args h)
  | _, _, .proj e i j hOne hf, h => .proj (CTerm.ofTerminating e h.2) i j hOne hf h.1
  | _, _, .tagOf e hf, h => .tagOf (CTerm.ofTerminating e h) hf
  | _, _, .caseTag e alts hf, h =>
      .caseTag (CTerm.ofTerminating e h.1) (CAlts.ofTerminating alts h.2) hf
  | _, _, .block b, h => .block b h.1 h.2

/-- `CTerm.ofTerminating`, on a spine. -/
def CSpine.ofTerminating {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs),
    s.Terminating → CSpine Sg Γ σs
  | _, _, .nil, _ => .nil
  | _, _, .cons t rest, h =>
      .cons (CTerm.ofTerminating t h.1) (CSpine.ofTerminating rest h.2)

/-- `CTerm.ofTerminating`, on the branches of a dispatch. -/
def CAlts.ofTerminating {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool} (alts : Alts Sg Γ τ tags full),
      alts.Terminating → CAlts Sg Γ τ tags full
  | _, _, _, _, .deflt t, h => .deflt (CTerm.ofTerminating t h)
  | _, _, _, _, .nilFull, _ => .nilFull
  | _, _, _, _, .cons tag t rest, h =>
      .cons tag (CTerm.ofTerminating t h.1) (CAlts.ofTerminating rest h.2)

end

mutual

/-- **Erasure undoes it**: the intrinsic and the extrinsic certified languages are the
    same language. -/
theorem CTerm.erase_ofTerminating {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ)
    (h : t.Terminating) : (CTerm.ofTerminating t h).erase = t :=
  match t, h with
  | .var _, _ => rfl
  | .lam b, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CTerm.erase_ofTerminating b h]
  | .ap f a, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CTerm.erase_ofTerminating f h.1,
        CTerm.erase_ofTerminating a h.2]
  | .lit _, _ => rfl
  | .global _, _ => rfl
  | .extern _, _ => rfl
  | .lazyMk e, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CTerm.erase_ofTerminating e h]
  | .lazyForce e, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CTerm.erase_ofTerminating e h]
  | .letE e b, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CTerm.erase_ofTerminating e h.1,
        CTerm.erase_ofTerminating b h.2]
  | .ite c t e, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CTerm.erase_ofTerminating c h.1,
        CTerm.erase_ofTerminating t h.2.1, CTerm.erase_ofTerminating e h.2.2]
  | .ctor _ _ _ args, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CSpine.erase_ofTerminating args h]
  | .proj e _ _ _ _, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CTerm.erase_ofTerminating e h.2]
  | .tagOf e _, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CTerm.erase_ofTerminating e h]
  | .caseTag e alts _, h => by
      simp only [CTerm.ofTerminating, CTerm.erase, CTerm.erase_ofTerminating e h.1,
        CAlts.erase_ofTerminating alts h.2]
  | .block _, _ => rfl
  termination_by sizeOf t

/-- `CTerm.erase_ofTerminating`, on a spine. -/
theorem CSpine.erase_ofTerminating {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs)
    (h : s.Terminating) : (CSpine.ofTerminating s h).erase = s :=
  match s, h with
  | .nil, _ => rfl
  | .cons t rest, h => by
      simp only [CSpine.ofTerminating, CSpine.erase, CTerm.erase_ofTerminating t h.1,
        CSpine.erase_ofTerminating rest h.2]
  termination_by sizeOf s

/-- `CTerm.erase_ofTerminating`, on the branches of a dispatch. -/
theorem CAlts.erase_ofTerminating {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool}
    (alts : Alts Sg Γ τ tags full) (h : alts.Terminating) :
    (CAlts.ofTerminating alts h).erase = alts :=
  match alts, h with
  | .deflt t, h => by
      simp only [CAlts.ofTerminating, CAlts.erase, CTerm.erase_ofTerminating t h]
  | .nilFull, _ => rfl
  | .cons _ t rest, h => by
      simp only [CAlts.ofTerminating, CAlts.erase, CTerm.erase_ofTerminating t h.1,
        CAlts.erase_ofTerminating rest h.2]
  termination_by sizeOf alts

end

/-- A `CertifiedTerm` — the D2 packaging — is a `CTerm`, and the same one. -/
def CertifiedTerm.toCTerm {Γ : Ctx} {τ : Ty} (t : CertifiedTerm Sg Γ τ) : CTerm Sg Γ τ :=
  CTerm.ofTerminating t.term t.cert

/-- The round trip through the intrinsic grammar changes nothing. -/
theorem CertifiedTerm.erase_toCTerm {Γ : Ctx} {τ : Ty} (t : CertifiedTerm Sg Γ τ) :
    t.toCTerm.erase = t.term :=
  CTerm.erase_ofTerminating t.term t.cert

/-! ## Smart constructors: the decidable part needs no proof

The two generators of `LakeJs.CertGen`, packaged so that a block of a shape that can be
certified mechanically is built without mentioning a certificate. -/

/-- **A block with no loop in it**, as a `CTerm`: every label it binds is a join point,
    nested ones included, and the certificate comes from `Tail.certified_of_loopFree`. -/
def CTerm.blockLoopFree {Γ : Ctx} {τ : Ty} (b : Tail Sg Γ [] τ) (hg : τ.ground = true)
    (hb : b.LoopFree) : CTerm Sg Γ τ :=
  .block b hg (Tail.certified_of_loopFree b hb)

/-- **A block with no label in it**, as a `CTerm`. -/
def CTerm.blockFlat {Γ : Ctx} {τ : Ty} (b : Tail Sg Γ [] τ) (hg : τ.ground = true)
    (hb : b.Flat) : CTerm Sg Γ τ :=
  .block b hg (Tail.certified_of_flat b hb)

/-- Erasing a loop-free block gives the block back. -/
@[simp] theorem CTerm.erase_blockLoopFree {Γ : Ctx} {τ : Ty} (b : Tail Sg Γ [] τ)
    (hg : τ.ground = true) (hb : b.LoopFree) :
    (CTerm.blockLoopFree b hg hb).erase = .block b := rfl

/-- Erasing a jump-free block gives the block back. -/
@[simp] theorem CTerm.erase_blockFlat {Γ : Ctx} {τ : Ty} (b : Tail Sg Γ [] τ)
    (hg : τ.ground = true) (hb : b.Flat) :
    (CTerm.blockFlat b hg hb).erase = .block b := rfl

/-! ## The guarantee has teeth

Two checks, one either way: the language is not empty, and the diverging block is not in
it. -/

/-- `(fun x => x) 1`, as a `CTerm`: the λ-calculus core asks for nothing. -/
def cIdAp : CTerm Sg [] (.prim .nat) :=
  .ap (.lam (.var .head)) (.lit (.nat 1))

/-- Its erasure is the term of `LakeJs.TermTotal`. -/
theorem cIdAp_erase : (cIdAp (Sg := Sg)).erase = idAp := rfl

/-- And it answers with `1`. -/
theorem cIdAp_steps : Steps (cIdAp (Sg := Sg)).erase (.lit (.nat 1)) :=
  Steps.single (Step.beta (Value.lit _))

/-- `block { let x = 1; return x }`, as a `CTerm`: a jump-free block, built through the
    smart constructor, so no certificate is written at the use site. -/
def cBlockLet : CTerm Sg [] (.prim .nat) :=
  CTerm.blockFlat (.letT (.lit (.nat 1)) (.ret (.var .head))) rfl blockLet_flat

/-- A block with a **join point**, as a `CTerm`, again with no certificate written by
    hand: `l(n) { return n }` jumped to from both arms of a branch. -/
def cSharedTail : CTerm Sg [Ty.bool] Ty.nat :=
  CTerm.blockLoopFree
    (.label (ps := [Ty.nat]) false (.ret (.var .head))
      (.iteT (.var .head)
        (.jmp .head (.cons (.lit (.nat 1)) .nil))
        (.jmp .head (.cons (.lit (.nat 2)) .nil))))
    rfl sharedTail_loopFree

/-- **The diverging block is not a `CTerm`.**  `l: while (true) { continue l }` is a
    perfectly good `Term`; no `CTerm` erases to it, and that is the whole point of the
    grammar. -/
theorem CTerm.erase_ne_loopForever (t : CTerm Sg [] (.prim .nat)) :
    t.erase ≠ loopForever :=
  fun h => loopForever_not_terminating (h ▸ t.erase_terminating)

/-- **No `CTerm` diverges**, in the form the name promises: for every closed `CTerm` there
    is a value it reaches, whatever it is built out of. -/
theorem CTerm.no_divergence {τ : Ty} (t : CTerm Sg [] τ) :
    ∃ v : Term Sg [] τ, Steps t.erase v ∧ Value v :=
  t.halts

end LakeJs.Expr

end
