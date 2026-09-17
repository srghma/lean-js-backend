import LakeJs.Reduce
import LakeJs.LinearLet
import LakeJs.Contify

/-!
# The two binding passes are reductions of the relation

`LakeJs/Reduce.lean` writes the optimiser down as the relation `Step` and proves that the
simplifier, the inliner and the scalariser only ever produce terms the *rules* reach.
This file does the same for the two passes that make the emitted module keep to the usage
discipline of `LakeJs.Usage`:

* `LakeJs.LinearLet` moves the value of a `let` with a single reader to that reader.  The
  rewrite is `Step.letCtorInline` — the rule that puts a bound value at the places that
  read it — so the pass needs no rule of its own, only the theorem below that says it
  only ever fires it.
* `LakeJs.DeadSlot` drops a loop slot no iteration reads, which is `Step.dropDeadSlot`.

`LakeJs.OptimiseChain` puts these together with the other three and states it of the
whole pipeline the driver runs.
-/

namespace LakeJs.Reduce

open LakeJs
open LakeJs.Ty
open LakeJs.Expr

/-! ## The single-reader `let` -/

/-- The rule of a `let` whose value is moved to its one reader. -/
theorem inlineLinearLet_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ τ : Ty}
    {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} {t0 : Term Sg Γ τ}
    (base : t0 —↠[tbl] Term.letE e b) :
    t0 —↠[tbl] LinearLet.inlineLinearLet e b := by
  unfold LinearLet.inlineLinearLet
  split
  · split
    · next heq => exact base.tail (.letCtorInline heq)
    · exact base
  · exact base

/-- The same rule, for the `let` of a loop block. -/
theorem inlineLinearLetB_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ : Ty}
    {σs : List Ty} {τ : Ty} {e : Term Sg Γ σ} {b : Body Sg (σ :: Γ) σs τ}
    {t0 : Body Sg Γ σs τ} (base : Chain (BodyStep tbl) t0 (Body.letB e b)) :
    Chain (BodyStep tbl) t0 (LinearLet.inlineLinearLetB e b) := by
  unfold LinearLet.inlineLinearLetB
  split
  · split
    · next heq => exact base.tail (.letCtorInline heq)
    · exact base
  · exact base

mutual

/-- Every term the single-reader `let` pass produces is reachable from the term it was
    given by the rules of `Step tbl`. -/
theorem Term.lineariseLets_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ), t —↠[tbl] LinearLet.Term.lineariseLets t
  | _, _, .var _ => .refl
  | _, _, .lit _ => .refl
  | _, _, .global _ => .refl
  | _, _, .extern _ => .refl
  | _, _, .proj e _ _ _ => Chain.projArg (Term.lineariseLets_chain e)
  | _, _, .tagOf e _ => Chain.tagOfArg (Term.lineariseLets_chain e)
  | _, _, .lazyMk e => Chain.lazyMkBody (Term.lineariseLets_chain e)
  | _, _, .lazyForce e => Chain.lazyForceArg (Term.lineariseLets_chain e)
  | _, _, .ite c t u =>
      ((Chain.iteCond (Term.lineariseLets_chain c)).trans
        (Chain.iteThen (Term.lineariseLets_chain t))).trans
          (Chain.iteElse (Term.lineariseLets_chain u))
  | _, _, .letE e b =>
      inlineLinearLet_chain
        ((Chain.letVal (Term.lineariseLets_chain e)).trans
          (Chain.letBody (Term.lineariseLets_chain b)))
  | _, _, .lamN b => Chain.lamBody (Term.lineariseLets_chain b)
  | _, _, .apN f args =>
      (Chain.apFun (Term.lineariseLets_chain f)).trans
        (Chain.apArgs (Spine.lineariseLets_chain args))
  | _, _, .lamProd rets => Chain.lamProdRets (Spine.lineariseLets_chain rets)
  | _, _, .callProd f args _ =>
      (Chain.callProdFun (Term.lineariseLets_chain f)).trans
        (Chain.callProdArgs (Spine.lineariseLets_chain args))
  | _, _, .jsOp _ args => Chain.jsOpArgs (Spine.lineariseLets_chain args)
  | _, _, .ctor _ _ _ args => Chain.ctorArgs (Spine.lineariseLets_chain args)
  | _, _, .caseTag s alts _ =>
      (Chain.caseScrut (Term.lineariseLets_chain s)).trans
        (Chain.caseAlts (Alts.lineariseLets_chain alts))
  | _, _, .loop init body =>
      (Chain.loopInit (Spine.lineariseLets_chain init)).trans
        (Chain.loopBody (Body.lineariseLets_chain body))
  | _, _, .joinPoint body rest =>
      (Chain.joinBody (Term.lineariseLets_chain body)).trans
        (Chain.joinRest (Term.lineariseLets_chain rest))
  | _, _, .jump _ args => Chain.jumpArgs (Spine.lineariseLets_chain args)

/-- `Term.lineariseLets_chain`, for the arguments of a spine. -/
theorem Spine.lineariseLets_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs),
      Chain (SpineStep tbl) s (LinearLet.Spine.lineariseLets s)
  | _, _, .nil => .refl
  | _, _, .cons t rest =>
      (Chain.spineHead (Term.lineariseLets_chain t)).trans
        (Chain.spineTail (Spine.lineariseLets_chain rest))

/-- `Term.lineariseLets_chain`, for the branches of a case. -/
theorem Alts.lineariseLets_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} (a : Alts Sg Γ τ tags),
      Chain (AltsStep tbl) a (LinearLet.Alts.lineariseLets a)
  | _, _, _, .deflt t => Chain.altsDeflt (Term.lineariseLets_chain t)
  | _, _, _, .cons _ t rest =>
      (Chain.altsHead (Term.lineariseLets_chain t)).trans
        (Chain.altsTail (Alts.lineariseLets_chain rest))

/-- `Term.lineariseLets_chain`, for a loop block. -/
theorem Body.lineariseLets_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty} (b : Body Sg Γ σs τ),
      Chain (BodyStep tbl) b (LinearLet.Body.lineariseLets b)
  | _, _, _, .ret t => Chain.retTerm (Term.lineariseLets_chain t)
  | _, _, _, .cont args => Chain.contArgs (Spine.lineariseLets_chain args)
  | _, _, _, .letB e b =>
      inlineLinearLetB_chain
        ((Chain.letBVal (Term.lineariseLets_chain e)).trans
          (Chain.letBBody (Body.lineariseLets_chain b)))
  | _, _, _, .iteB c t u =>
      ((Chain.iteBCond (Term.lineariseLets_chain c)).trans
        (Chain.iteBThen (Body.lineariseLets_chain t))).trans
          (Chain.iteBElse (Body.lineariseLets_chain u))
  | _, _, _, .joinPointB body rest =>
      (Chain.joinBBody (Term.lineariseLets_chain body)).trans
        (Chain.joinBRest (Body.lineariseLets_chain rest))

end

/-! ## The loop slot nothing reads -/

/-- Dropping one dead slot is one rewrite. -/
theorem dropAt_step {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty}
    {t t' : Term Sg Γ τ} {p : Nat} (h : DeadSlot.dropAt? t p = some t') :
    t —→[tbl] t' := by
  unfold DeadSlot.dropAt? at h
  split at h
  · exact .dropDeadSlot h
  · exact absurd h (by simp)

/-- Every loop the pass produces is reachable from the loop it was given. -/
theorem dropSlotsGo_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty} :
    ∀ (p : Nat) (t : Term Sg Γ τ), t —↠[tbl] DeadSlot.dropSlotsGo p t
  | 0, t => by rw [DeadSlot.dropSlotsGo]; exact .refl
  | p + 1, t => by
      rw [DeadSlot.dropSlotsGo]
      split
      · next heq => exact .head (dropAt_step heq) (dropSlotsGo_chain p _)
      · exact dropSlotsGo_chain p t

/-- The dead slots of one loop, dropped. -/
theorem dropDeadSlots_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty}
    (t : Term Sg Γ τ) : t —↠[tbl] DeadSlot.dropDeadSlots t := by
  unfold DeadSlot.dropDeadSlots
  split
  · exact dropSlotsGo_chain _ _
  · exact .refl

mutual

/-- Every term the dead-slot pass produces is reachable from the term it was given by the
    rules of `Step tbl`. -/
theorem Term.dropDead_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ), t —↠[tbl] DeadSlot.Term.dropDead t
  | _, _, .var _ => .refl
  | _, _, .lit _ => .refl
  | _, _, .global _ => .refl
  | _, _, .extern _ => .refl
  | _, _, .proj e _ _ _ => Chain.projArg (Term.dropDead_chain e)
  | _, _, .tagOf e _ => Chain.tagOfArg (Term.dropDead_chain e)
  | _, _, .lazyMk e => Chain.lazyMkBody (Term.dropDead_chain e)
  | _, _, .lazyForce e => Chain.lazyForceArg (Term.dropDead_chain e)
  | _, _, .ite c t u =>
      ((Chain.iteCond (Term.dropDead_chain c)).trans
        (Chain.iteThen (Term.dropDead_chain t))).trans
          (Chain.iteElse (Term.dropDead_chain u))
  | _, _, .letE e b =>
      (Chain.letVal (Term.dropDead_chain e)).trans (Chain.letBody (Term.dropDead_chain b))
  | _, _, .lamN b => Chain.lamBody (Term.dropDead_chain b)
  | _, _, .apN f args =>
      (Chain.apFun (Term.dropDead_chain f)).trans (Chain.apArgs (Spine.dropDead_chain args))
  | _, _, .lamProd rets => Chain.lamProdRets (Spine.dropDead_chain rets)
  | _, _, .callProd f args _ =>
      (Chain.callProdFun (Term.dropDead_chain f)).trans
        (Chain.callProdArgs (Spine.dropDead_chain args))
  | _, _, .jsOp _ args => Chain.jsOpArgs (Spine.dropDead_chain args)
  | _, _, .ctor _ _ _ args => Chain.ctorArgs (Spine.dropDead_chain args)
  | _, _, .caseTag s alts _ =>
      (Chain.caseScrut (Term.dropDead_chain s)).trans
        (Chain.caseAlts (Alts.dropDead_chain alts))
  | _, _, .loop init body =>
      ((Chain.loopInit (Spine.dropDead_chain init)).trans
        (Chain.loopBody (Body.dropDead_chain body))).trans (dropDeadSlots_chain _)
  | _, _, .joinPoint body rest =>
      (Chain.joinBody (Term.dropDead_chain body)).trans
        (Chain.joinRest (Term.dropDead_chain rest))
  | _, _, .jump _ args => Chain.jumpArgs (Spine.dropDead_chain args)

/-- `Term.dropDead_chain`, for the arguments of a spine. -/
theorem Spine.dropDead_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs),
      Chain (SpineStep tbl) s (DeadSlot.Spine.dropDead s)
  | _, _, .nil => .refl
  | _, _, .cons t rest =>
      (Chain.spineHead (Term.dropDead_chain t)).trans
        (Chain.spineTail (Spine.dropDead_chain rest))

/-- `Term.dropDead_chain`, for the branches of a case. -/
theorem Alts.dropDead_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} (a : Alts Sg Γ τ tags),
      Chain (AltsStep tbl) a (DeadSlot.Alts.dropDead a)
  | _, _, _, .deflt t => Chain.altsDeflt (Term.dropDead_chain t)
  | _, _, _, .cons _ t rest =>
      (Chain.altsHead (Term.dropDead_chain t)).trans
        (Chain.altsTail (Alts.dropDead_chain rest))

/-- `Term.dropDead_chain`, for a loop block. -/
theorem Body.dropDead_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty} (b : Body Sg Γ σs τ),
      Chain (BodyStep tbl) b (DeadSlot.Body.dropDead b)
  | _, _, _, .ret t => Chain.retTerm (Term.dropDead_chain t)
  | _, _, _, .cont args => Chain.contArgs (Spine.dropDead_chain args)
  | _, _, _, .letB e b =>
      (Chain.letBVal (Term.dropDead_chain e)).trans
        (Chain.letBBody (Body.dropDead_chain b))
  | _, _, _, .iteB c t u =>
      ((Chain.iteBCond (Term.dropDead_chain c)).trans
        (Chain.iteBThen (Body.dropDead_chain t))).trans
          (Chain.iteBElse (Body.dropDead_chain u))
  | _, _, _, .joinPointB body rest =>
      (Chain.joinBBody (Term.dropDead_chain body)).trans
        (Chain.joinBRest (Body.dropDead_chain rest))

end

/-! ## The local function that is only ever called -/

/-- The rule of a `let` of a lambda read as the join point it is. -/
theorem contifyLet_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ τ : Ty}
    {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} {t0 : Term Sg Γ τ}
    (base : t0 —↠[tbl] Term.letE e b) :
    t0 —↠[tbl] Contify.contifyLet e b := by
  unfold Contify.contifyLet
  split
  · split
    · next heq => exact base.tail (.contify heq)
    · exact base
  · exact base

/-- The rule of a block's `let` of a lambda read as the join point it is. -/
theorem contifyLetB_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ τ : Ty}
    {σs : List Ty} {e : Term Sg Γ σ} {b : Body Sg (σ :: Γ) σs τ}
    {b0 : Body Sg Γ σs τ} (base : Chain (BodyStep tbl) b0 (Body.letB e b)) :
    Chain (BodyStep tbl) b0 (Contify.contifyLetB e b) := by
  unfold Contify.contifyLetB
  split
  · split
    · next heq => exact base.tail (.contifyB heq)
    · exact base
  · exact base

mutual

/-- Every term the contification pass produces is reachable from the term it was given by
    the rules of `Step tbl`. -/
theorem Term.contify_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ), t —↠[tbl] Contify.Term.contify t
  | _, _, .var _ => .refl
  | _, _, .lit _ => .refl
  | _, _, .global _ => .refl
  | _, _, .extern _ => .refl
  | _, _, .proj e _ _ _ => Chain.projArg (Term.contify_chain e)
  | _, _, .tagOf e _ => Chain.tagOfArg (Term.contify_chain e)
  | _, _, .lazyMk e => Chain.lazyMkBody (Term.contify_chain e)
  | _, _, .lazyForce e => Chain.lazyForceArg (Term.contify_chain e)
  | _, _, .ite c t u =>
      ((Chain.iteCond (Term.contify_chain c)).trans
        (Chain.iteThen (Term.contify_chain t))).trans
          (Chain.iteElse (Term.contify_chain u))
  | _, _, .letE e b =>
      contifyLet_chain
        ((Chain.letVal (Term.contify_chain e)).trans
          (Chain.letBody (Term.contify_chain b)))
  | _, _, .lamN b => Chain.lamBody (Term.contify_chain b)
  | _, _, .apN f args =>
      (Chain.apFun (Term.contify_chain f)).trans
        (Chain.apArgs (Spine.contify_chain args))
  | _, _, .lamProd rets => Chain.lamProdRets (Spine.contify_chain rets)
  | _, _, .callProd f args _ =>
      (Chain.callProdFun (Term.contify_chain f)).trans
        (Chain.callProdArgs (Spine.contify_chain args))
  | _, _, .jsOp _ args => Chain.jsOpArgs (Spine.contify_chain args)
  | _, _, .ctor _ _ _ args => Chain.ctorArgs (Spine.contify_chain args)
  | _, _, .caseTag s alts _ =>
      (Chain.caseScrut (Term.contify_chain s)).trans
        (Chain.caseAlts (Alts.contify_chain alts))
  | _, _, .loop init body =>
      (Chain.loopInit (Spine.contify_chain init)).trans
        (Chain.loopBody (Body.contify_chain body))
  | _, _, .joinPoint body rest =>
      (Chain.joinBody (Term.contify_chain body)).trans
        (Chain.joinRest (Term.contify_chain rest))
  | _, _, .jump _ args => Chain.jumpArgs (Spine.contify_chain args)

/-- `Term.contify_chain`, for the arguments of a spine. -/
theorem Spine.contify_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs),
      Chain (SpineStep tbl) s (Contify.Spine.contify s)
  | _, _, .nil => .refl
  | _, _, .cons t rest =>
      (Chain.spineHead (Term.contify_chain t)).trans
        (Chain.spineTail (Spine.contify_chain rest))

/-- `Term.contify_chain`, for the branches of a case. -/
theorem Alts.contify_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} (a : Alts Sg Γ τ tags),
      Chain (AltsStep tbl) a (Contify.Alts.contify a)
  | _, _, _, .deflt t => Chain.altsDeflt (Term.contify_chain t)
  | _, _, _, .cons _ t rest =>
      (Chain.altsHead (Term.contify_chain t)).trans
        (Chain.altsTail (Alts.contify_chain rest))

/-- `Term.contify_chain`, for a loop block. -/
theorem Body.contify_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty} (b : Body Sg Γ σs τ),
      Chain (BodyStep tbl) b (Contify.Body.contify b)
  | _, _, _, .ret t => Chain.retTerm (Term.contify_chain t)
  | _, _, _, .cont args => Chain.contArgs (Spine.contify_chain args)
  | _, _, _, .letB e b =>
      contifyLetB_chain
        ((Chain.letBVal (Term.contify_chain e)).trans
          (Chain.letBBody (Body.contify_chain b)))
  | _, _, _, .iteB c t u =>
      ((Chain.iteBCond (Term.contify_chain c)).trans
        (Chain.iteBThen (Body.contify_chain t))).trans
          (Chain.iteBElse (Body.contify_chain u))
  | _, _, _, .joinPointB body rest =>
      (Chain.joinBBody (Term.contify_chain body)).trans
        (Chain.joinBRest (Body.contify_chain rest))

end

end LakeJs.Reduce
