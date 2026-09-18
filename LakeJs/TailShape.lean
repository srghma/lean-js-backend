module

public import LakeJs.TerminatingSubst
public import LakeJs.LSubstLemmas

@[expose] public section

/-!
# The shape of a block: label-free, and loop-free

The certificate generators of `LakeJs.CertGen` work on two shapes of block, and this
module is their definition and their stability properties.

* `Tail.Flat` — **no label at all**.  Jumps are allowed (they can only point at a label
  further out), and every *term* in the tail is certified in turn.
* `Tail.LoopFree` — **no `self` label**: a `Tail.label` is allowed as long as it is a
  shared tail (`self = false`), and both its body and the rest of the block are loop-free
  again.  A loop is what repeats work, so this is the largest shape for which a
  certificate can be produced without looking at what the block computes.

The measure the generator recurses on lives next door, in `LakeJs.InlineSize`: a shared
tail is reduced by *inlining* its body at each jump (`StepT.labelJoin`), which is neither
a subterm step nor one that keeps the number of labels down.

The rest of this module is the bookkeeping that makes the two shapes usable:

* both survive renaming, and a flat tail also survives the substitution of an atomic term;
* binding the arguments of a jump in front of a block keeps its shape;
* inlining blocks for labels (`Tail.lsubst`) keeps a flat tail flat and a loop-free tail
  loop-free.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## The two shapes -/

mutual

/-- **A tail with no label in it**, and with every term in it certified.  A jump is
    allowed: it can only name a label bound further out, and inside a `Term.block` — which
    opens its tail in the empty label context — there is no such label, so a flat block
    is straight-line code with branches. -/
def Tail.Flat {Sg : Sig} : ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty}, Tail Sg Γ Ω τ → Prop
  | _, _, _, .ret t => t.Terminating
  | _, _, _, .jmp _ args => args.Terminating
  | _, _, _, .letT e b => e.Terminating ∧ b.Flat
  | _, _, _, .iteT c t e => c.Terminating ∧ t.Flat ∧ e.Flat
  | _, _, _, .caseT e alts _ => e.Terminating ∧ alts.Flat
  | _, _, _, .label _ _ _ => False

/-- `Tail.Flat`, on the branches of a dispatch inside a block. -/
def AltsT.Flat {Sg : Sig} :
    ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat} {full : Bool},
      AltsT Sg Γ Ω τ tags full → Prop
  | _, _, _, _, _, .deflt b => b.Flat
  | _, _, _, _, _, .nilFull => True
  | _, _, _, _, _, .cons _ b rest => b.Flat ∧ rest.Flat

end

mutual

/-- **A tail with no loop in it**: every label it binds is a *shared tail*
    (`self = false`), the body of each is loop-free in turn, and every term in it is
    certified. -/
def Tail.LoopFree {Sg : Sig} : ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty}, Tail Sg Γ Ω τ → Prop
  | _, _, _, .ret t => t.Terminating
  | _, _, _, .jmp _ args => args.Terminating
  | _, _, _, .letT e b => e.Terminating ∧ b.LoopFree
  | _, _, _, .iteT c t e => c.Terminating ∧ t.LoopFree ∧ e.LoopFree
  | _, _, _, .caseT e alts _ => e.Terminating ∧ alts.LoopFree
  | _, _, _, .label self body rest => self = false ∧ body.LoopFree ∧ rest.LoopFree

/-- `Tail.LoopFree`, on the branches of a dispatch inside a block. -/
def AltsT.LoopFree {Sg : Sig} :
    ∀ {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat} {full : Bool},
      AltsT Sg Γ Ω τ tags full → Prop
  | _, _, _, _, _, .deflt b => b.LoopFree
  | _, _, _, _, _, .nilFull => True
  | _, _, _, _, _, .cons _ b rest => b.LoopFree ∧ rest.LoopFree

end

mutual

/-- A flat tail is loop-free: it has no label, so it has no loop. -/
theorem Tail.loopFree_of_flat {Γ : Ctx} {Ω : LCtx} {τ : Ty} (b : Tail Sg Γ Ω τ)
    (h : b.Flat) : b.LoopFree :=
  match b, h with
  | .ret _, h => h
  | .jmp _ _, h => h
  | .letT _ b, h => ⟨h.1, Tail.loopFree_of_flat b h.2⟩
  | .iteT _ t e, h => ⟨h.1, Tail.loopFree_of_flat t h.2.1, Tail.loopFree_of_flat e h.2.2⟩
  | .caseT _ alts _, h => ⟨h.1, AltsT.loopFree_of_flat alts h.2⟩
  | .label _ _ _, h => absurd h (by simp [Tail.Flat])
  termination_by sizeOf b

/-- Flat branches are loop-free. -/
theorem AltsT.loopFree_of_flat {Γ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} (alts : AltsT Sg Γ Ω τ tags full) (h : alts.Flat) : alts.LoopFree :=
  match alts, h with
  | .deflt b, h => Tail.loopFree_of_flat b h
  | .nilFull, _ => trivial
  | .cons _ b rest, h =>
      ⟨Tail.loopFree_of_flat b h.1, AltsT.loopFree_of_flat rest h.2⟩
  termination_by sizeOf alts

end

/-! ## The shapes survive renaming -/

mutual

/-- A flat tail stays flat when its variables and labels are renamed. -/
theorem Tail.flat_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} (b : Tail Sg Γ₁ Ω₁ τ)
    (ρ : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂) (h : b.Flat) : (b.rename ρ κ).Flat :=
  match b, h with
  | .ret t, h => Term.terminating_rename t ρ h
  | .jmp _ args, h => Spine.terminating_rename args ρ h
  | .letT e b, h =>
      ⟨Term.terminating_rename e ρ h.1, Tail.flat_rename b ρ.lift κ h.2⟩
  | .iteT c t e, h =>
      ⟨Term.terminating_rename c ρ h.1, Tail.flat_rename t ρ κ h.2.1,
        Tail.flat_rename e ρ κ h.2.2⟩
  | .caseT e alts _, h =>
      ⟨Term.terminating_rename e ρ h.1, AltsT.flat_rename alts ρ κ h.2⟩
  | .label _ _ _, h => absurd h (by simp [Tail.Flat])
  termination_by sizeOf b

/-- Flat branches stay flat when their variables and labels are renamed. -/
theorem AltsT.flat_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} (alts : AltsT Sg Γ₁ Ω₁ τ tags full) (ρ : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂)
    (h : alts.Flat) : (alts.rename ρ κ).Flat :=
  match alts, h with
  | .deflt b, h => Tail.flat_rename b ρ κ h
  | .nilFull, _ => trivial
  | .cons _ b rest, h =>
      ⟨Tail.flat_rename b ρ κ h.1, AltsT.flat_rename rest ρ κ h.2⟩
  termination_by sizeOf alts

end

mutual

/-- A flat tail stays flat when a variable is replaced by an atomic term. -/
theorem Tail.flat_subst_atomic {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {τ : Ty} (b : Tail Sg Γ₁ Ω τ)
    {θ : VSub Sg Γ₁ Γ₂} (hθ : VSub.Atomic θ) (h : b.Flat) : (b.subst θ).Flat :=
  match b, h with
  | .ret t, h => Term.terminating_subst_atomic t hθ h
  | .jmp _ args, h => Spine.terminating_subst_atomic args hθ h
  | .letT e b, h =>
      ⟨Term.terminating_subst_atomic e hθ h.1,
        Tail.flat_subst_atomic b (VSub.Atomic.lift hθ) h.2⟩
  | .iteT c t e, h =>
      ⟨Term.terminating_subst_atomic c hθ h.1, Tail.flat_subst_atomic t hθ h.2.1,
        Tail.flat_subst_atomic e hθ h.2.2⟩
  | .caseT e alts _, h =>
      ⟨Term.terminating_subst_atomic e hθ h.1, AltsT.flat_subst_atomic alts hθ h.2⟩
  | .label _ _ _, h => absurd h (by simp [Tail.Flat])
  termination_by sizeOf b

/-- Flat branches stay flat when a variable is replaced by an atomic term. -/
theorem AltsT.flat_subst_atomic {Γ₁ Γ₂ : Ctx} {Ω : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} (alts : AltsT Sg Γ₁ Ω τ tags full) {θ : VSub Sg Γ₁ Γ₂}
    (hθ : VSub.Atomic θ) (h : alts.Flat) : (alts.subst θ).Flat :=
  match alts, h with
  | .deflt b, h => Tail.flat_subst_atomic b hθ h
  | .nilFull, _ => trivial
  | .cons _ b rest, h =>
      ⟨Tail.flat_subst_atomic b hθ h.1, AltsT.flat_subst_atomic rest hθ h.2⟩
  termination_by sizeOf alts

end

/-! ## Binding the arguments of a jump -/

/-- The parameters of a list binder are certified: they are variables. -/
theorem Spine.vars_terminating {Γ : Ctx} :
    ∀ (σs : List Ty), (Spine.vars (Sg := Sg) (Γ := Γ) σs).Terminating
  | [] => trivial
  | _ :: σs => ⟨trivial, Spine.terminating_rename _ VRen.weaken (Spine.vars_terminating σs)⟩

/-- **Binding the arguments of a jump in front of a flat block keeps it flat.**  Every
    argument is bound by a `let`, and a `let` of a certified term in front of a flat tail
    is flat. -/
theorem Tail.flat_letSpine {Γ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ {σs : List Ty} (args : Spine Sg Γ σs) (jb : Tail Sg (σs ++ Γ) Ω τ),
      args.Terminating → jb.Flat → (Tail.letSpine args jb).Flat
  | [], .nil, _, _, hjb => hjb
  | _ :: σs, .cons a rest, _, hargs, hjb =>
      Tail.flat_letSpine rest _ hargs.2
        ⟨Term.terminating_rename a (VRen.weakenList σs) hargs.1, hjb⟩

/-! ## Substituting a block for a label -/

/-- **A label substitution all of whose blocks are flat.** -/
def LSub.Flat {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} (θ : LSub Sg Γ Ω₁ Ω₂ τ) : Prop :=
  ∀ {ps : List Ty} (l : Ω₁ ∋ₗ ps), (θ l).Flat

/-- The identity label substitution is flat: every label goes to a jump to itself. -/
theorem LSub.Flat.id {Γ : Ctx} {Ω : LCtx} {τ : Ty} :
    LSub.Flat (Sg := Sg) (Γ := Γ) (Ω₁ := Ω) (Ω₂ := Ω) (τ := τ) LSub.id :=
  fun _ => Spine.vars_terminating _

/-- Carrying a flat label substitution under a variable binder keeps it flat. -/
theorem LSub.Flat.vlift {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {σ τ : Ty} {θ : LSub Sg Γ Ω₁ Ω₂ τ}
    (h : LSub.Flat θ) : LSub.Flat (LSub.vlift (σ := σ) θ) :=
  fun l => Tail.flat_rename _ _ _ (h l)

/-- Carrying a flat label substitution under a list binder keeps it flat. -/
theorem LSub.Flat.vliftList {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {θ : LSub Sg Γ Ω₁ Ω₂ τ}
    (h : LSub.Flat θ) (σs : List Ty) : LSub.Flat (LSub.vliftList σs θ) :=
  fun l => Tail.flat_rename _ _ _ (h l)

/-- Carrying a flat label substitution under a label binder keeps it flat. -/
theorem LSub.Flat.liftL {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {qs : List Ty} {τ : Ty}
    {θ : LSub Sg Γ Ω₁ Ω₂ τ} (h : LSub.Flat θ) : LSub.Flat (LSub.lift (qs := qs) θ) := by
  intro ps l
  match l with
  | .head => exact Spine.vars_terminating _
  | .tail l => exact Tail.flat_rename _ _ _ (h l)

/-- Carrying a flat label substitution into the body of a label keeps it flat. -/
theorem LSub.Flat.ext {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {θ : LSub Sg Γ Ω₁ Ω₂ τ}
    (h : LSub.Flat θ) (self : Bool) (ps : List Ty) :
    LSub.Flat (LSub.ext self ps θ) := by
  cases self with
  | false => exact h.vliftList ps
  | true => exact LSub.Flat.liftL (h.vliftList ps)

/-- The substitution that replaces the innermost label by a flat block is flat. -/
theorem LSub.Flat.zero {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    {jb : Tail Sg (ps ++ Γ) Ω τ} (h : jb.Flat) : LSub.Flat (LSub.zero jb) := by
  intro qs l
  match l with
  | .head => exact h
  | .tail l => exact Spine.vars_terminating _

mutual

/-- **Substituting flat blocks for labels keeps a flat tail flat.** -/
theorem Tail.flat_lsubst {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} (b : Tail Sg Γ Ω₁ τ)
    (h : b.Flat) (θ : LSub Sg Γ Ω₁ Ω₂ τ) (hθ : LSub.Flat θ) : (b.lsubst θ).Flat :=
  match b, h with
  | .ret _, h => h
  | .jmp l args, h => Tail.flat_letSpine args (θ l) h (hθ l)
  | .letT _ b, h => ⟨h.1, Tail.flat_lsubst b h.2 _ hθ.vlift⟩
  | .iteT _ t e, h =>
      ⟨h.1, Tail.flat_lsubst t h.2.1 θ hθ, Tail.flat_lsubst e h.2.2 θ hθ⟩
  | .caseT _ alts _, h => ⟨h.1, AltsT.flat_lsubst alts h.2 θ hθ⟩
  | .label _ _ _, h => absurd h (by simp [Tail.Flat])
  termination_by sizeOf b

/-- **Substituting flat blocks for labels keeps flat branches flat.** -/
theorem AltsT.flat_lsubst {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} (alts : AltsT Sg Γ Ω₁ τ tags full) (h : alts.Flat)
    (θ : LSub Sg Γ Ω₁ Ω₂ τ) (hθ : LSub.Flat θ) : (alts.lsubst θ).Flat :=
  match alts, h with
  | .deflt b, h => Tail.flat_lsubst b h θ hθ
  | .nilFull, _ => trivial
  | .cons _ b rest, h =>
      ⟨Tail.flat_lsubst b h.1 θ hθ, AltsT.flat_lsubst rest h.2 θ hθ⟩
  termination_by sizeOf alts

end

/-! ## Loop-free blocks, and what keeps a tail loop-free -/

mutual

/-- A loop-free tail stays loop-free when its variables and labels are renamed. -/
theorem Tail.loopFree_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} (b : Tail Sg Γ₁ Ω₁ τ)
    (ρ : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂) (h : b.LoopFree) : (b.rename ρ κ).LoopFree :=
  match b, h with
  | .ret t, h => Term.terminating_rename t ρ h
  | .jmp _ args, h => Spine.terminating_rename args ρ h
  | .letT e b, h =>
      ⟨Term.terminating_rename e ρ h.1, Tail.loopFree_rename b ρ.lift κ h.2⟩
  | .iteT c t e, h =>
      ⟨Term.terminating_rename c ρ h.1, Tail.loopFree_rename t ρ κ h.2.1,
        Tail.loopFree_rename e ρ κ h.2.2⟩
  | .caseT e alts _, h =>
      ⟨Term.terminating_rename e ρ h.1, AltsT.loopFree_rename alts ρ κ h.2⟩
  | .label (ps := ps) self body rest, h =>
      ⟨h.1, Tail.loopFree_rename body (VRen.liftList ps ρ) (LRen.ext self ps κ) h.2.1,
        Tail.loopFree_rename rest ρ κ.lift h.2.2⟩
  termination_by sizeOf b

/-- Loop-free branches stay loop-free when their variables and labels are renamed. -/
theorem AltsT.loopFree_rename {Γ₁ Γ₂ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} (alts : AltsT Sg Γ₁ Ω₁ τ tags full) (ρ : VRen Γ₁ Γ₂) (κ : LRen Ω₁ Ω₂)
    (h : alts.LoopFree) : (alts.rename ρ κ).LoopFree :=
  match alts, h with
  | .deflt b, h => Tail.loopFree_rename b ρ κ h
  | .nilFull, _ => trivial
  | .cons _ b rest, h =>
      ⟨Tail.loopFree_rename b ρ κ h.1, AltsT.loopFree_rename rest ρ κ h.2⟩
  termination_by sizeOf alts

end

/-- **Binding the arguments of a jump in front of a loop-free block keeps it
    loop-free**: every argument is bound by a `let`, and a `let` of a certified term in
    front of a loop-free tail is loop-free. -/
theorem Tail.loopFree_letSpine {Γ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ {σs : List Ty} (args : Spine Sg Γ σs) (jb : Tail Sg (σs ++ Γ) Ω τ),
      args.Terminating → jb.LoopFree → (Tail.letSpine args jb).LoopFree
  | [], .nil, _, _, hjb => hjb
  | _ :: σs, .cons a rest, _, hargs, hjb =>
      Tail.loopFree_letSpine rest _ hargs.2
        ⟨Term.terminating_rename a (VRen.weakenList σs) hargs.1, hjb⟩

/-- **A label substitution all of whose blocks are loop-free.**  This is the side
    condition under which inlining a label keeps a block loop-free, and it is weaker than
    `LSub.Flat`. -/
def LSub.LoopFreeS {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} (θ : LSub Sg Γ Ω₁ Ω₂ τ) : Prop :=
  ∀ {ps : List Ty} (l : Ω₁ ∋ₗ ps), (θ l).LoopFree

/-- A flat label substitution is loop-free. -/
theorem LSub.Flat.loopFreeS {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {θ : LSub Sg Γ Ω₁ Ω₂ τ}
    (h : LSub.Flat θ) : LSub.LoopFreeS θ :=
  fun l => Tail.loopFree_of_flat _ (h l)

/-- Carrying a loop-free label substitution under a variable binder keeps it
    loop-free. -/
theorem LSub.LoopFreeS.vlift {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {σ τ : Ty} {θ : LSub Sg Γ Ω₁ Ω₂ τ}
    (h : LSub.LoopFreeS θ) : LSub.LoopFreeS (LSub.vlift (σ := σ) θ) :=
  fun l => Tail.loopFree_rename _ _ _ (h l)

/-- Carrying it under a list binder keeps it loop-free. -/
theorem LSub.LoopFreeS.vliftList {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty}
    {θ : LSub Sg Γ Ω₁ Ω₂ τ} (h : LSub.LoopFreeS θ) (σs : List Ty) :
    LSub.LoopFreeS (LSub.vliftList σs θ) :=
  fun l => Tail.loopFree_rename _ _ _ (h l)

/-- Carrying it under a label binder keeps it loop-free. -/
theorem LSub.LoopFreeS.liftL {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {qs : List Ty} {τ : Ty}
    {θ : LSub Sg Γ Ω₁ Ω₂ τ} (h : LSub.LoopFreeS θ) :
    LSub.LoopFreeS (LSub.lift (qs := qs) θ) := by
  intro ps l
  match l with
  | .head => exact Spine.vars_terminating _
  | .tail l => exact Tail.loopFree_rename _ _ _ (h l)

/-- Carrying it into the body of a label keeps it loop-free. -/
theorem LSub.LoopFreeS.ext {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {θ : LSub Sg Γ Ω₁ Ω₂ τ}
    (h : LSub.LoopFreeS θ) (self : Bool) (ps : List Ty) :
    LSub.LoopFreeS (LSub.ext self ps θ) := by
  cases self with
  | false => exact h.vliftList ps
  | true => exact LSub.LoopFreeS.liftL (LSub.LoopFreeS.vliftList h ps)

/-- The substitution that replaces the innermost label by a loop-free block is
    loop-free. -/
theorem LSub.LoopFreeS.zero {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    {jb : Tail Sg (ps ++ Γ) Ω τ} (h : jb.LoopFree) : LSub.LoopFreeS (LSub.zero jb) := by
  intro qs l
  match l with
  | .head => exact h
  | .tail l => exact Spine.vars_terminating _

mutual

/-- **Inlining loop-free blocks for labels keeps a loop-free tail loop-free.** -/
theorem Tail.loopFree_lsubst {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} (b : Tail Sg Γ Ω₁ τ)
    (h : b.LoopFree) (θ : LSub Sg Γ Ω₁ Ω₂ τ) (hθ : LSub.LoopFreeS θ) :
    (b.lsubst θ).LoopFree :=
  match b, h with
  | .ret _, h => h
  | .jmp l args, h => Tail.loopFree_letSpine args (θ l) h (hθ l)
  | .letT _ b, h => ⟨h.1, Tail.loopFree_lsubst b h.2 _ hθ.vlift⟩
  | .iteT _ t e, h =>
      ⟨h.1, Tail.loopFree_lsubst t h.2.1 θ hθ, Tail.loopFree_lsubst e h.2.2 θ hθ⟩
  | .caseT _ alts _, h => ⟨h.1, AltsT.loopFree_lsubst alts h.2 θ hθ⟩
  | .label self body rest, h =>
      ⟨h.1, Tail.loopFree_lsubst body h.2.1 _ (hθ.ext self _),
        Tail.loopFree_lsubst rest h.2.2 _ hθ.liftL⟩
  termination_by sizeOf b

/-- **Inlining loop-free blocks for labels keeps loop-free branches loop-free.** -/
theorem AltsT.loopFree_lsubst {Γ : Ctx} {Ω₁ Ω₂ : LCtx} {τ : Ty} {tags : List Nat}
    {full : Bool} (alts : AltsT Sg Γ Ω₁ τ tags full) (h : alts.LoopFree)
    (θ : LSub Sg Γ Ω₁ Ω₂ τ) (hθ : LSub.LoopFreeS θ) : (alts.lsubst θ).LoopFree :=
  match alts, h with
  | .deflt b, h => Tail.loopFree_lsubst b h θ hθ
  | .nilFull, _ => trivial
  | .cons _ b rest, h =>
      ⟨Tail.loopFree_lsubst b h.1 θ hθ, AltsT.loopFree_lsubst rest h.2 θ hθ⟩
  termination_by sizeOf alts

end

end LakeJs.Expr

end
