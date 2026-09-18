module

public import LakeJs.TermTotal
public import LakeJs.TailShape
public import LakeJs.InlineSize
public import LakeJs.Diverge
public import LakeJs.DivergeNeg

@[expose] public section

/-!
# Certificate generators

`LakeJs.Terminating` says what a block's termination certificate *is*; by the diagonal
argument of `TERMINATING_TERM_ASSESSMENT.md` §2 it cannot be a decidable check, so
certificates have to be **produced**.  This module is the catalogue of the shapes for
which one can be produced mechanically — item E of the assessment's design space.

Two generators are implemented, and the second subsumes the first:

* **A jump-free block is certified** (`Tail.certified_of_flat`).  A `Tail` with no
  `Tail.label` in it has no `Tail.jmp` in it either — a jump needs a label in scope, and
  a `Term.block` opens its tail in the *empty* label context — so such a block is a
  flowchart with no back edge and no join point: `let`, `if` and `case` in tail position,
  ending in an answer.

* **A block with no loop in it is certified** (`Tail.certified_of_loopFree`): every
  `Tail.label` it binds is a *shared tail* (`self = false`), nested ones included.  This
  is the **join point** generator, and it is the largest shape that can be certified
  without looking at what the block computes: what is left out is exactly the one
  construct that repeats work.

`Tail.Flat` and `Tail.LoopFree` (`LakeJs.TailShape`) are the two side conditions; both
also ask that every *term* the tail contains be certified in turn, so a nested
`Term.block` inside a `let` is admitted as soon as it carries its own certificate.

## How the join-point generator runs

A shared tail is reduced by `StepT.labelJoin`, which **inlines** the label's body at each
jump (`Tail.lsubst0`).  The result is neither a subterm nor a block with fewer labels — a
body with labels of its own is copied once per jump — so the argument runs on
`Tail.inlineSize`, the size the block would have once every label had been inlined, which
the reduction strictly lowers (`Tail.inlineSize_lsubst0_lt`).  Two further facts make that
measure usable:

* the inlined block is loop-free again (`Tail.loopFree_lsubst`), and
* **inlining commutes with closing the block** (`Tail.lsubst0_subst`): the step fires on
  `(.label false body rest).subst γ`, while the induction hypothesis speaks about
  `rest.lsubst0 body`, and the two agree.  That commutation is why `Tail.letSpine` binds
  every argument of a jump with a `let` rather than copying the atomic ones.

So the proof is a recursion on `Tail.labelCount` (`Tail.sn_block_of_loopFree_upto`) whose
body is a structural recursion on the tail (`Tail.sn_block_of_loopFree_step`), the latter
being the logical-relation argument of `LakeJs.Reducibility` run one level down, inside
`Term.block`.

What is not here, and why: a **loop** (`self = true`) is the genuinely hard case, and by
design — there the certificate has to be transported from the source function's
termination proof, which is front-end work (`TERMINATING_TERM_ASSESSMENT.md` §4.4).
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Two steps of the block itself -/

/-- **A block that answers with a term that runs out of steps runs out of steps.**  It
    either hands the term back (`Step.blockRet`) or runs it where it stands. -/
theorem Term.SN.blockRet {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ} (h : t.SN) :
    (Term.block (.ret t)).SN := by
  induction h with
  | intro t hacc ih =>
      refine Term.SN.intro fun u hst => ?_
      cases hst with
      | blockRet => exact Acc.intro t hacc
      | blockStep hstT =>
          cases hstT with
          | retStep hst' => exact ih _ hst'

/-! ## The generator

One level of the recursion: the tail is traversed structurally, and the *only* place the
induction hypothesis `ih` is used is the shared tail, where the block that the step
produces has one label fewer. -/

mutual

/-- **A loop-free block with at most `n` labels runs out of steps**, given that every
    loop-free block with fewer than `n` labels does. -/
theorem Tail.sn_block_of_loopFree_step {τ : Ty} {n : Nat}
    (ih : ∀ {Γ' : Ctx} (b' : Tail Sg Γ' [] τ), b'.LoopFree →
      b'.inlineSize LEnv.nil < n →
      ∀ γ' : VSub Sg Γ' [], RedSub γ' → (Term.block (b'.subst γ')).SN) :
    ∀ {Γ : Ctx} (b : Tail Sg Γ [] τ), b.LoopFree → b.inlineSize LEnv.nil ≤ n →
      ∀ γ : VSub Sg Γ [], RedSub γ → (Term.block (b.subst γ)).SN
  | _, .ret t, hb, _, γ, hγ => Term.SN.blockRet (Term.fundamental t γ hγ hb).sn
  | _, .jmp l _, _, _, _, _ => nomatch l
  | _, .letT e b', hb, hn, γ, hγ => by
      have key : ∀ e' : Term Sg [] _, e'.SN → Red _ e' →
          (Term.block (Tail.letT e' (b'.subst γ.lift))).SN := by
        intro e' hsn
        induction hsn with
        | intro e' _ ihe =>
            intro he'
            refine Term.SN.intro fun u hst => ?_
            cases hst with
            | blockStep hstT =>
                cases hstT with
                | letV hve =>
                    rw [Tail.subst0_subst_lift]
                    exact Tail.sn_block_of_loopFree_step ih b' hb.2 hn (VSub.cons e' γ)
                      (RedSub.cons hve he' hγ)
                | letStep hste => exact ihe _ hste (he'.step hste)
      have he := Term.fundamental e γ hγ hb.1
      exact key _ he.sn he
  | _, .iteT c t e, hb, hn, γ, hγ => by
      have hn' : t.inlineSize LEnv.nil + e.inlineSize LEnv.nil + 1 ≤ n := hn
      have hnt : t.inlineSize LEnv.nil ≤ n := by omega
      have hne : e.inlineSize LEnv.nil ≤ n := by omega
      have key : ∀ c' : Term Sg [] (.prim .bool), c'.SN →
          (Term.block (Tail.iteT c' (t.subst γ) (e.subst γ))).SN := by
        intro c' hsn
        induction hsn with
        | intro c' _ ihc =>
            refine Term.SN.intro fun u hst => ?_
            cases hst with
            | blockStep hstT =>
                cases hstT with
                | iteTrue => exact Tail.sn_block_of_loopFree_step ih t hb.2.1 hnt γ hγ
                | iteFalse => exact Tail.sn_block_of_loopFree_step ih e hb.2.2 hne γ hγ
                | iteCond hstc => exact ihc _ hstc
      exact key _ (Term.fundamental c γ hγ hb.1).sn
  | _, .caseT s alts h, hb, hn, γ, hγ => by
      have hn' : alts.inlineSize LEnv.nil ≤ n := by
        have : alts.inlineSize LEnv.nil + 1 ≤ n := hn
        omega
      have key : ∀ s' : Term Sg [] _, s'.SN →
          (Term.block (Tail.caseT s' (alts.subst γ) h)).SN := by
        intro s' hsn
        induction hsn with
        | intro s' _ ihs =>
            refine Term.SN.intro fun u hst => ?_
            cases hst with
            | blockStep hstT =>
                cases hstT with
                | caseCtor =>
                    exact AltsT.sn_block_of_loopFree_step ih alts hb.2 hn' γ hγ _ _
                | caseBool =>
                    exact AltsT.sn_block_of_loopFree_step ih alts hb.2 hn' γ hγ _ _
                | caseStep hsts => exact ihs _ hsts
      exact key _ (Term.fundamental s γ hγ hb.1).sn
  | _, .label (ps := ps) self body rest, hb, hn, γ, hγ => by
      have hself : self = false := hb.1
      subst hself
      have hbody : body.LoopFree := hb.2.1
      have hrest : rest.LoopFree := hb.2.2
      have hcount : (rest.lsubst0 body).inlineSize LEnv.nil < n :=
        Nat.lt_of_lt_of_le (Tail.inlineSize_lsubst0_lt rest body) hn
      have hlf : (rest.lsubst0 body).LoopFree :=
        Tail.loopFree_lsubst rest hrest _ (LSub.LoopFreeS.zero hbody)
      refine Term.SN.intro fun u hst => ?_
      cases hst with
      | blockStep hstT =>
          cases hstT with
          | labelJoin =>
              rw [← Tail.lsubst0_subst rest body γ]
              exact ih (rest.lsubst0 body) hlf hcount γ hγ
  termination_by _ b => sizeOf b

/-- **Every branch of a loop-free dispatch runs out of steps**, under the same
    hypothesis. -/
theorem AltsT.sn_block_of_loopFree_step {τ : Ty} {n : Nat}
    (ih : ∀ {Γ' : Ctx} (b' : Tail Sg Γ' [] τ), b'.LoopFree →
      b'.inlineSize LEnv.nil < n →
      ∀ γ' : VSub Sg Γ' [], RedSub γ' → (Term.block (b'.subst γ')).SN) :
    ∀ {Γ : Ctx} {tags : List Nat} {full : Bool} (alts : AltsT Sg Γ [] τ tags full),
      alts.LoopFree → alts.inlineSize LEnv.nil ≤ n → ∀ γ : VSub Sg Γ [], RedSub γ →
      ∀ (i : Nat) (hcov : full = true → i ∈ tags),
        (Term.block ((alts.subst γ).select i hcov)).SN
  | _, _, _, .deflt b, ha, hn, γ, hγ, _, _ =>
      Tail.sn_block_of_loopFree_step ih b ha hn γ hγ
  | _, _, _, .nilFull, _, _, _, _, _, hcov => absurd (hcov rfl) (by simp)
  | _, _, _, .cons _ b rest, ha, hn, γ, hγ, i, _ => by
      have hn' : b.inlineSize LEnv.nil + rest.inlineSize LEnv.nil ≤ n := hn
      have hnb : b.inlineSize LEnv.nil ≤ n := by omega
      have hnr : rest.inlineSize LEnv.nil ≤ n := by omega
      simp only [AltsT.subst, AltsT.select]
      split
      · exact Tail.sn_block_of_loopFree_step ih b ha.1 hnb γ hγ
      · exact AltsT.sn_block_of_loopFree_step ih rest ha.2 hnr γ hγ i _
  termination_by _ _ _ alts => sizeOf alts

end

/-- **A loop-free block with at most `n` labels runs out of steps.**  The recursion is on
    `n`; each step of it inlines one shared tail. -/
theorem Tail.sn_block_of_loopFree_upto {τ : Ty} :
    ∀ (n : Nat) {Γ : Ctx} (b : Tail Sg Γ [] τ), b.LoopFree →
      b.inlineSize LEnv.nil ≤ n →
      ∀ γ : VSub Sg Γ [], RedSub γ → (Term.block (b.subst γ)).SN
  | 0, _, b, hb, hn, γ, hγ =>
      Tail.sn_block_of_loopFree_step
        (fun _ _ hlt => absurd hlt (Nat.not_lt_zero _)) b hb hn γ hγ
  | n + 1, _, b, hb, hn, γ, hγ =>
      Tail.sn_block_of_loopFree_step
        (fun b' hb' hlt γ' hγ' =>
          Tail.sn_block_of_loopFree_upto n b' hb' (Nat.le_of_lt_succ hlt) γ' hγ')
        b hb hn γ hγ

/-- **A block with no loop in it is certified.**  This is the join-point generator: every
    label the block binds is a shared tail, and the certificate is derived from that
    shape alone. -/
theorem Tail.certified_of_loopFree {Γ : Ctx} {τ : Ty} (b : Tail Sg Γ [] τ)
    (hb : b.LoopFree) : b.Certified :=
  fun γ hγ =>
    Tail.sn_block_of_loopFree_upto (b.inlineSize LEnv.nil) b hb (Nat.le_refl _) γ hγ

/-- **A jump-free block is certified**, a special case of the above: a block with no
    label at all has no loop in it. -/
theorem Tail.certified_of_flat {Γ : Ctx} {τ : Ty} (b : Tail Sg Γ [] τ) (hb : b.Flat) :
    b.Certified :=
  Tail.certified_of_loopFree b (Tail.loopFree_of_flat b hb)

/-- **A loop-free block at a value type is a certified term.**  This is how a block
    enters `Term.Terminating` — and hence the evaluator — without any appeal to the
    logical relation at the use site. -/
theorem Term.terminating_block_of_loopFree {Γ : Ctx} {τ : Ty} (b : Tail Sg Γ [] τ)
    (hg : τ.ground = true) (hb : b.LoopFree) : (Term.block b).Terminating :=
  ⟨hg, Tail.certified_of_loopFree b hb⟩

/-- The same for a jump-free block. -/
theorem Term.terminating_block_of_flat {Γ : Ctx} {τ : Ty} (b : Tail Sg Γ [] τ)
    (hg : τ.ground = true) (hb : b.Flat) : (Term.block b).Terminating :=
  ⟨hg, Tail.certified_of_flat b hb⟩

/-! ## The generators are not vacuous

`block { let x = 1; return x }` is a jump-free block, and the first generator certifies
it, so the evaluator runs it. -/

/-- `block { let x = 1; return x }`. -/
def blockLet : Term Sg [] (.prim .nat) :=
  .block (.letT (.lit (.nat 1)) (.ret (.var .head)))

/-- Its tail is jump-free. -/
theorem blockLet_flat :
    (Tail.letT (Sg := Sg) (Γ := []) (Ω := []) (τ := .prim .nat)
      (.lit (.nat 1)) (.ret (.var .head))).Flat :=
  ⟨trivial, trivial⟩

/-- So the block is a certified term … -/
theorem blockLet_terminating : (blockLet (Sg := Sg)).Terminating :=
  Term.terminating_block_of_flat _ rfl blockLet_flat

/-- … it runs out of steps … -/
theorem blockLet_sn : (blockLet (Sg := Sg)).SN :=
  Term.terminating_sn _ blockLet_terminating

/-- … and it answers with `1`. -/
theorem blockLet_steps : Steps (blockLet (Sg := Sg)) (.lit (.nat 1)) :=
  .tail (.tail .refl (Step.blockStep (StepT.letV (Value.lit _)))) Step.blockRet

/-! ### A join point, and a join point inside a join point

`Term.sharedTail` is the block the join-point generator exists for: one shared tail,
jumped to from both arms of a branch.  It binds a label, so the first generator says
nothing about it; the second certifies it. -/

/-- The tail of `Term.sharedTail` is loop-free: its one label is a shared tail whose body
    is jump-free. -/
theorem sharedTail_loopFree :
    (Tail.label (Sg := Sg) (Γ := [Ty.bool]) (Ω := []) (τ := Ty.nat) (ps := [Ty.nat])
        false (.ret (♯0))
        (.iteT (♯0)
          (.jmp .head (.cons (.lit (.nat 1)) .nil))
          (.jmp .head (.cons (.lit (.nat 2)) .nil)))).LoopFree :=
  ⟨rfl, trivial, trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- **A block with a join point is a certified term.** -/
theorem sharedTail_terminating : (Term.sharedTail (Sg := Sg)).Terminating :=
  Term.terminating_block_of_loopFree _ rfl sharedTail_loopFree

/-- … so, whatever boolean the enclosing context supplies for its free variable, its
    block runs out of steps. -/
theorem sharedTail_sn_closed (γ : VSub Sg [Ty.bool] []) (hγ : RedSub γ) :
    (Term.block ((Tail.label (ps := [Ty.nat]) false (.ret (♯0))
      (.iteT (♯0)
        (.jmp .head (.cons (.lit (.nat 1)) .nil))
        (.jmp .head (.cons (.lit (.nat 2)) .nil)))).subst γ)).SN :=
  Tail.certified_of_loopFree _ sharedTail_loopFree γ hγ

/-- A **nested** join point: the body of a shared tail binds a shared tail of its own.
    This is the case the measure of `LakeJs.InlineSize` exists for — inlining the outer
    label copies the inner one — and the generator reaches it. -/
def nestedJoin : Term Sg [] Ty.nat :=
  .block
    (.label (ps := [Ty.nat]) false
      (.label (ps := [Ty.nat]) false (.ret (♯0)) (.jmp .head (.cons (♯0) .nil)))
      (.jmp .head (.cons (.lit (.nat 1)) .nil)))

/-- Its tail is loop-free: neither label is a loop. -/
theorem nestedJoin_loopFree :
    (Tail.label (Sg := Sg) (Γ := []) (Ω := []) (τ := Ty.nat) (ps := [Ty.nat]) false
        (.label (ps := [Ty.nat]) false (.ret (♯0)) (.jmp .head (.cons (♯0) .nil)))
        (.jmp .head (.cons (.lit (.nat 1)) .nil))).LoopFree :=
  ⟨rfl, ⟨rfl, trivial, trivial, trivial⟩, trivial, trivial⟩

/-- **So a block with a nested join point is a certified term** … -/
theorem nestedJoin_terminating : (nestedJoin (Sg := Sg)).Terminating :=
  Term.terminating_block_of_loopFree _ rfl nestedJoin_loopFree

/-- … and it runs out of steps. -/
theorem nestedJoin_sn : (nestedJoin (Sg := Sg)).SN :=
  Term.terminating_sn _ nestedJoin_terminating

/-! ## The certificate is not vacuous either

The diverging block of `LakeJs.Diverge` — `l: while (true) { continue l }` — has **no**
certificate, so it is not a certified term and the evaluator is never asked to run it.
That is the other half of the statement that `Term.Terminating` is the right side
condition: it admits blocks (§ above), and it still refuses the one that never answers. -/

/-- The tail of `loopForever`: the one label of the block, a loop that jumps to
    itself. -/
def loopTail {Sg : Sig} {τ : Ty} : Tail Sg [] [] τ :=
  .label (ps := []) true (.jmp .head .nil) (.jmp .head .nil)

/-- `loopForever` does not run out of steps: it steps to itself. -/
theorem loopForever_not_sn {τ : Ty} : ¬ (loopForever (Sg := Sg) (τ := τ)).SN :=
  not_sn_of_cycle loopForever_step_self .refl

/-- **The diverging block has no certificate.**  A certificate at the empty context and
    the empty substitution is exactly the claim that `loopForever` runs out of steps, and
    it does not. -/
theorem loopTail_not_certified {τ : Ty} : ¬ (loopTail (Sg := Sg) (τ := τ)).Certified :=
  fun h => loopForever_not_sn h.sn_closed

/-- **And so it is not a certified term**, at a value type or any other. -/
theorem loopForever_not_terminating :
    ¬ (loopForever (Sg := Sg) (τ := .prim .nat)).Terminating :=
  fun h => loopTail_not_certified h.2

/-- **And the join-point generator does not reach it**: its label is a loop, so the tail
    is not loop-free.  The two generators stop exactly where the certificate does. -/
theorem loopTail_not_loopFree {τ : Ty} : ¬ (loopTail (Sg := Sg) (τ := τ)).LoopFree :=
  fun h => Bool.noConfusion h.1

end LakeJs.Expr

end
