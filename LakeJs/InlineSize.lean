module

public import LakeJs.Subst

@[expose] public section

/-!
# The measure: the size a block would have if every label were inlined

A shared tail is reduced by *inlining* its body at each jump, which is neither a subterm
step nor one that keeps the number of labels down — a body with labels of its own is
copied once per jump.  What does come down is the size the block would have **after every
label had been inlined**, and that size can be computed without doing the inlining:
carry an environment giving, for every label in scope, the size of the block it names.

`Tail.inlineSize` is that computation.  A jump costs the size of its target (plus one);
binding the arguments of a jump costs nothing, which is why `Tail.letT` is not counted;
and a label costs the rest of the block, read in the environment extended by the size of
its body.  The one fact the generator needs is `Tail.inlineSize_lsubst0_lt`: inlining a
shared tail strictly decreases it. -/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-- The size of the block each label in scope names. -/
structure LEnv (Ω : LCtx) where
  /-- The size recorded for one label. -/
  size : ∀ {ps : List Ty}, Ω ∋ₗ ps → Nat

/-- Nothing is in scope in the empty label context. -/
def LEnv.nil : LEnv [] := ⟨fun l => nomatch l⟩

/-- Extend an environment by the size of the innermost label's block. -/
def LEnv.cons {Ω : LCtx} {ps : List Ty} (n : Nat) (ρ : LEnv Ω) : LEnv (ps :: Ω) :=
  ⟨fun {_} l =>
    match l with
    | .head => n
    | .tail l => ρ.size l⟩

mutual

/-- **The size this tail would have if every label were inlined**, given the size of the
    block each label in scope names. -/
def Tail.inlineSize {Sg : Sig} :
    ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty}, Tail Sg Γ Ω τ → LEnv Ω → Nat
  | _, _, _, .ret _, _ => 1
  | _, _, _, .jmp l _, ρ => ρ.size l + 1
  | _, _, _, .letT _ b, ρ => b.inlineSize ρ
  | _, _, _, .iteT _ t e, ρ => t.inlineSize ρ + e.inlineSize ρ + 1
  | _, _, _, .caseT _ alts _, ρ => alts.inlineSize ρ + 1
  | _, _, _, .label false body rest, ρ =>
      rest.inlineSize (LEnv.cons (body.inlineSize ρ) ρ) + 1
  | _, _, _, .label true _ rest, ρ => rest.inlineSize (LEnv.cons 0 ρ) + 1

/-- The same, for the branches of a dispatch inside a block. -/
def AltsT.inlineSize {Sg : Sig} :
    ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat} {full : Bool},
      AltsT Sg Γ Ω τ tags full → LEnv Ω → Nat
  | _, _, _, _, _, .deflt b, ρ => b.inlineSize ρ
  | _, _, _, _, _, .nilFull, _ => 1
  | _, _, _, _, _, .cons _ b rest, ρ => b.inlineSize ρ + rest.inlineSize ρ

end

mutual

/-- The measure reads its environment pointwise. -/
theorem Tail.inlineSize_congr {Γ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ Ω τ) (ρ ρ' : LEnv Ω),
      (∀ {ps : List Ty} (l : Ω ∋ₗ ps), ρ.size l = ρ'.size l) →
      b.inlineSize ρ = b.inlineSize ρ'
  | .ret _, _, _, _ => rfl
  | .jmp l _, ρ, ρ', h => by
      show ρ.size l + 1 = ρ'.size l + 1
      rw [h l]
  | .letT _ b, ρ, ρ', h => Tail.inlineSize_congr b ρ ρ' h
  | .iteT _ t e, ρ, ρ', h => by
      show t.inlineSize ρ + e.inlineSize ρ + 1 = t.inlineSize ρ' + e.inlineSize ρ' + 1
      rw [Tail.inlineSize_congr t ρ ρ' h, Tail.inlineSize_congr e ρ ρ' h]
  | .caseT _ alts _, ρ, ρ', h => by
      show alts.inlineSize ρ + 1 = alts.inlineSize ρ' + 1
      rw [AltsT.inlineSize_congr alts ρ ρ' h]
  | .label false body rest, ρ, ρ', h => by
      have hb : body.inlineSize ρ = body.inlineSize ρ' :=
        Tail.inlineSize_congr body ρ ρ' h
      have hr : rest.inlineSize (LEnv.cons (body.inlineSize ρ) ρ)
          = rest.inlineSize (LEnv.cons (body.inlineSize ρ') ρ') :=
        Tail.inlineSize_congr rest _ _ (fun l => by
          match l with
          | .head => exact hb
          | .tail l => exact h l)
      show rest.inlineSize (LEnv.cons (body.inlineSize ρ) ρ) + 1
          = rest.inlineSize (LEnv.cons (body.inlineSize ρ') ρ') + 1
      rw [hr]
  | .label true _ rest, ρ, ρ', h => by
      have hr : rest.inlineSize (LEnv.cons 0 ρ) = rest.inlineSize (LEnv.cons 0 ρ') :=
        Tail.inlineSize_congr rest _ _ (fun l => by
          match l with
          | .head => rfl
          | .tail l => exact h l)
      show rest.inlineSize (LEnv.cons 0 ρ) + 1 = rest.inlineSize (LEnv.cons 0 ρ') + 1
      rw [hr]
  termination_by b => sizeOf b

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.inlineSize_congr {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (alts : AltsT Sg Γ Ω τ tags full) (ρ ρ' : LEnv Ω),
      (∀ {ps : List Ty} (l : Ω ∋ₗ ps), ρ.size l = ρ'.size l) →
      alts.inlineSize ρ = alts.inlineSize ρ'
  | .deflt b, ρ, ρ', h => Tail.inlineSize_congr b ρ ρ' h
  | .nilFull, _, _, _ => rfl
  | .cons _ b rest, ρ, ρ', h => by
      show b.inlineSize ρ + rest.inlineSize ρ = b.inlineSize ρ' + rest.inlineSize ρ'
      rw [Tail.inlineSize_congr b ρ ρ' h, AltsT.inlineSize_congr rest ρ ρ' h]
  termination_by alts => sizeOf alts

end

mutual

/-- Renaming does not change the measure: it reads the renamed environment. -/
theorem Tail.inlineSize_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ₁ Ω₁ τ) (ρv : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂) (ρ : LEnv Ω₂),
      (b.rename ρv κ).inlineSize ρ = b.inlineSize ⟨fun l => ρ.size (κ l)⟩
  | .ret _, _, _, _ => rfl
  | .jmp _ _, _, _, _ => rfl
  | .letT _ b, ρv, κ, ρ => Tail.inlineSize_rename b ρv.lift κ ρ
  | .iteT _ t e, ρv, κ, ρ => by
      show (t.rename ρv κ).inlineSize ρ + (e.rename ρv κ).inlineSize ρ + 1
          = t.inlineSize ⟨fun l => ρ.size (κ l)⟩
            + e.inlineSize ⟨fun l => ρ.size (κ l)⟩ + 1
      rw [Tail.inlineSize_rename t ρv κ ρ, Tail.inlineSize_rename e ρv κ ρ]
  | .caseT _ alts _, ρv, κ, ρ => by
      show (alts.rename ρv κ).inlineSize ρ + 1
          = alts.inlineSize ⟨fun l => ρ.size (κ l)⟩ + 1
      rw [AltsT.inlineSize_rename alts ρv κ ρ]
  | .label (ps := ps) false body rest, ρv, κ, ρ => by
      have hb : (body.rename (VRen.liftList ps ρv) κ).inlineSize ρ
          = body.inlineSize ⟨fun l => ρ.size (κ l)⟩ :=
        Tail.inlineSize_rename body (VRen.liftList ps ρv) κ ρ
      have hr : (rest.rename ρv κ.lift).inlineSize
            (LEnv.cons (body.inlineSize ⟨fun l => ρ.size (κ l)⟩) ρ)
          = rest.inlineSize
            ⟨fun l => (LEnv.cons (body.inlineSize ⟨fun l => ρ.size (κ l)⟩) ρ).size
              (κ.lift l)⟩ :=
        Tail.inlineSize_rename rest ρv κ.lift _
      have hc : rest.inlineSize
            ⟨fun l => (LEnv.cons (body.inlineSize ⟨fun l => ρ.size (κ l)⟩) ρ).size
              (κ.lift l)⟩
          = rest.inlineSize
            (LEnv.cons (body.inlineSize ⟨fun l => ρ.size (κ l)⟩)
              ⟨fun l => ρ.size (κ l)⟩) :=
        Tail.inlineSize_congr rest _ _ (fun l => by
          match l with
          | .head => rfl
          | .tail l => rfl)
      show (rest.rename ρv κ.lift).inlineSize
            (LEnv.cons ((body.rename (VRen.liftList ps ρv) κ).inlineSize ρ) ρ) + 1
          = rest.inlineSize
            (LEnv.cons (body.inlineSize ⟨fun l => ρ.size (κ l)⟩)
              ⟨fun l => ρ.size (κ l)⟩) + 1
      rw [hb, hr, hc]
  | .label true _ rest, ρv, κ, ρ => by
      have hr : (rest.rename ρv κ.lift).inlineSize (LEnv.cons 0 ρ)
          = rest.inlineSize ⟨fun l => (LEnv.cons 0 ρ).size (κ.lift l)⟩ :=
        Tail.inlineSize_rename rest ρv κ.lift _
      have hc : rest.inlineSize ⟨fun l => (LEnv.cons 0 ρ).size (κ.lift l)⟩
          = rest.inlineSize (LEnv.cons 0 ⟨fun l => ρ.size (κ l)⟩) :=
        Tail.inlineSize_congr rest _ _ (fun l => by
          match l with
          | .head => rfl
          | .tail l => rfl)
      show (rest.rename ρv κ.lift).inlineSize (LEnv.cons 0 ρ) + 1
          = rest.inlineSize (LEnv.cons 0 ⟨fun l => ρ.size (κ l)⟩) + 1
      rw [hr, hc]
  termination_by b => sizeOf b

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.inlineSize_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (alts : AltsT Sg Γ₁ Ω₁ τ tags full) (ρv : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂)
      (ρ : LEnv Ω₂),
      (alts.rename ρv κ).inlineSize ρ = alts.inlineSize ⟨fun l => ρ.size (κ l)⟩
  | .deflt b, ρv, κ, ρ => Tail.inlineSize_rename b ρv κ ρ
  | .nilFull, _, _, _ => rfl
  | .cons _ b rest, ρv, κ, ρ => by
      show (b.rename ρv κ).inlineSize ρ + (rest.rename ρv κ).inlineSize ρ
          = b.inlineSize ⟨fun l => ρ.size (κ l)⟩
            + rest.inlineSize ⟨fun l => ρ.size (κ l)⟩
      rw [Tail.inlineSize_rename b ρv κ ρ, AltsT.inlineSize_rename rest ρv κ ρ]
  termination_by alts => sizeOf alts

end

/-- **A renamed block is no larger.**  The shape the substitution lemma below needs: the
    blocks a label substitution names are carried under binders by renaming, and that
    does not change what they cost. -/
theorem Tail.inlineSize_rename_id {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {τ : Ty} (b : Tail Sg Γ₁ Ω τ)
    (ρv : VRen Γ₁ Γ₂) (ρ : LEnv Ω) :
    (b.rename ρv LRen.id).inlineSize ρ = b.inlineSize ρ := by
  rw [Tail.inlineSize_rename b ρv LRen.id ρ]
  exact Tail.inlineSize_congr b _ _ (fun _ => rfl)

/-- The same, for weakening by one label. -/
theorem Tail.inlineSize_lweaken {Γ : Ctx} {Ω : LCtx} {qs : List Ty} {τ : Ty}
    (b : Tail Sg Γ Ω τ) (n : Nat) (ρ : LEnv Ω) :
    (Tail.lweaken (ps := qs) b).inlineSize (LEnv.cons n ρ) = b.inlineSize ρ := by
  show (b.rename VRen.id (LRen.weaken (ps := qs))).inlineSize (LEnv.cons n ρ)
      = b.inlineSize ρ
  rw [Tail.inlineSize_rename b VRen.id LRen.weaken (LEnv.cons n ρ)]
  exact Tail.inlineSize_congr b _ _ (fun _ => rfl)

/-- Binding the arguments of a jump costs nothing: a `let` of a term is not counted. -/
theorem Tail.inlineSize_letSpine {Γ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ {σs : List Ty} (args : Spine Sg Γ σs) (jb : Tail Sg (σs ++ Γ) Ω τ) (ρ : LEnv Ω),
      (Tail.letSpine args jb).inlineSize ρ = jb.inlineSize ρ
  | [], .nil, _, _ => rfl
  | _ :: σs, .cons a rest, jb, ρ =>
      Tail.inlineSize_letSpine rest (.letT (a.rename (VRen.weakenList σs)) jb) ρ

mutual

/-- **Inlining does not raise the measure**, as long as every block the substitution
    names is no larger than the environment says its label is. -/
theorem Tail.inlineSize_lsubst_le {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} :
    ∀ (b : Tail Sg Γ Ω₁ τ) (θ : LSub Sg Γ Ω₁ Ω₂ τ) (ρ : LEnv Ω₁) (ρ' : LEnv Ω₂),
      (∀ {ps : List Ty} (l : Ω₁ ∋ₗ ps), (θ l).inlineSize ρ' ≤ ρ.size l + 1) →
      (b.lsubst θ).inlineSize ρ' ≤ b.inlineSize ρ
  | .ret _, _, _, _, _ => Nat.le_refl _
  | .jmp l args, θ, ρ, ρ', hθ => by
      show (Tail.letSpine args (θ l)).inlineSize ρ' ≤ ρ.size l + 1
      rw [Tail.inlineSize_letSpine]
      exact hθ l
  | .letT _ b, θ, ρ, ρ', hθ => by
      show (b.lsubst θ.vlift).inlineSize ρ' ≤ b.inlineSize ρ
      refine Tail.inlineSize_lsubst_le b θ.vlift ρ ρ' (fun l => ?_)
      show ((θ l).rename _ LRen.id).inlineSize ρ' ≤ _
      rw [Tail.inlineSize_rename_id]
      exact hθ l
  | .iteT _ t e, θ, ρ, ρ', hθ => by
      show (t.lsubst θ).inlineSize ρ' + (e.lsubst θ).inlineSize ρ' + 1
          ≤ t.inlineSize ρ + e.inlineSize ρ + 1
      exact Nat.succ_le_succ (Nat.add_le_add (Tail.inlineSize_lsubst_le t θ ρ ρ' hθ)
        (Tail.inlineSize_lsubst_le e θ ρ ρ' hθ))
  | .caseT _ alts _, θ, ρ, ρ', hθ => by
      show (alts.lsubst θ).inlineSize ρ' + 1 ≤ alts.inlineSize ρ + 1
      exact Nat.succ_le_succ (AltsT.inlineSize_lsubst_le alts θ ρ ρ' hθ)
  | .label (ps := ps) false body rest, θ, ρ, ρ', hθ => by
      have hbody : (body.lsubst (LSub.vliftList ps θ)).inlineSize ρ'
          ≤ body.inlineSize ρ := by
        refine Tail.inlineSize_lsubst_le body (LSub.vliftList ps θ) ρ ρ' (fun l => ?_)
        show ((θ l).rename _ LRen.id).inlineSize ρ' ≤ _
        rw [Tail.inlineSize_rename_id]
        exact hθ l
      show (rest.lsubst θ.lift).inlineSize
            (LEnv.cons ((body.lsubst (LSub.vliftList ps θ)).inlineSize ρ') ρ') + 1
          ≤ rest.inlineSize (LEnv.cons (body.inlineSize ρ) ρ) + 1
      refine Nat.succ_le_succ (Tail.inlineSize_lsubst_le rest θ.lift _ _ (fun l => ?_))
      match l with
      | .head =>
          show (Tail.jmp LVar.head (Spine.vars ps)).inlineSize
              (LEnv.cons ((body.lsubst (LSub.vliftList ps θ)).inlineSize ρ') ρ')
            ≤ body.inlineSize ρ + 1
          exact Nat.succ_le_succ hbody
      | .tail l =>
          show (Tail.lweaken (θ l)).inlineSize
              (LEnv.cons ((body.lsubst (LSub.vliftList ps θ)).inlineSize ρ') ρ')
            ≤ ρ.size l + 1
          rw [Tail.inlineSize_lweaken]
          exact hθ l
  | .label (ps := ps) true _ rest, θ, ρ, ρ', hθ => by
      show (rest.lsubst θ.lift).inlineSize (LEnv.cons 0 ρ') + 1
          ≤ rest.inlineSize (LEnv.cons 0 ρ) + 1
      refine Nat.succ_le_succ (Tail.inlineSize_lsubst_le rest θ.lift _ _ (fun l => ?_))
      match l with
      | .head =>
          show (Tail.jmp LVar.head (Spine.vars ps)).inlineSize (LEnv.cons 0 ρ') ≤ 0 + 1
          exact Nat.le_refl _
      | .tail l =>
          show (Tail.lweaken (θ l)).inlineSize (LEnv.cons 0 ρ') ≤ ρ.size l + 1
          rw [Tail.inlineSize_lweaken]
          exact hθ l
  termination_by b => sizeOf b

/-- The same, for the branches of a dispatch inside a block. -/
theorem AltsT.inlineSize_lsubst_le {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} :
    ∀ (alts : AltsT Sg Γ Ω₁ τ tags full) (θ : LSub Sg Γ Ω₁ Ω₂ τ) (ρ : LEnv Ω₁)
      (ρ' : LEnv Ω₂),
      (∀ {ps : List Ty} (l : Ω₁ ∋ₗ ps), (θ l).inlineSize ρ' ≤ ρ.size l + 1) →
      (alts.lsubst θ).inlineSize ρ' ≤ alts.inlineSize ρ
  | .deflt b, θ, ρ, ρ', hθ => Tail.inlineSize_lsubst_le b θ ρ ρ' hθ
  | .nilFull, _, _, _, _ => Nat.le_refl _
  | .cons _ b rest, θ, ρ, ρ', hθ => by
      show (b.lsubst θ).inlineSize ρ' + (rest.lsubst θ).inlineSize ρ'
          ≤ b.inlineSize ρ + rest.inlineSize ρ
      exact Nat.add_le_add (Tail.inlineSize_lsubst_le b θ ρ ρ' hθ)
        (AltsT.inlineSize_lsubst_le rest θ ρ ρ' hθ)
  termination_by alts => sizeOf alts

end

/-- **Inlining a shared tail strictly decreases the measure.**  This is what the
    join-point generator recurses on: the label is gone, and what took its place is the
    block it named, which the measure had already paid for. -/
theorem Tail.inlineSize_lsubst0_lt {Γ : Ctx} {ps : List Ty} {τ : Ty}
    (rest : Tail Sg Γ [ps] τ) (jb : Tail Sg (ps ++ Γ) [] τ) :
    (rest.lsubst0 jb).inlineSize LEnv.nil
      < (Tail.label false jb rest).inlineSize LEnv.nil := by
  have h : (rest.lsubst (LSub.zero jb)).inlineSize LEnv.nil
      ≤ rest.inlineSize (LEnv.cons (jb.inlineSize LEnv.nil) LEnv.nil) := by
    refine Tail.inlineSize_lsubst_le rest (LSub.zero jb) _ _ (fun l => ?_)
    match l with
    | .head => exact Nat.le_succ _
    | .tail l => exact nomatch l
  exact Nat.lt_succ_of_le h

end LakeJs.Expr

end
