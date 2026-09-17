import LakeJs.Scalarise
import LakeJs.Usage

/-!
# The loop slot no iteration reads

A `Term.loop` carries one variable per slot: the slots start at the values of `init` and
every `Body.cont` hands the next iteration a new value for each of them.  A slot the body
never *reads* is work and a declaration for nothing — `let v5 = v2;` at the top of the
loop and `v5 = 2;` before every `continue` — and it is the last kind of unread binding
the emitted JavaScript still had.

`dropSlot?` removes one such slot.  It is exactly the same rebuild as
`LakeJs.Scalarise.scalariseSlot?`: the list of slots is *not* part of the type of the
term a loop is, so a loop with one slot fewer is a term of the same type, in the same
context, of the same signature.  What changes is

* `init` loses its `p`-th value,
* every `Body.cont` loses its `p`-th argument — the value the next iteration would have
  been handed — and
* the body is rebuilt in the smaller context, which is possible precisely because
  nothing in it reads the slot (`LakeJs.Usage.Body.occSlotAt` of the slot is zero — the
  value each jump hands the slot itself is not a read of it, since it goes with the
  slot).

The parameters of a *function* are a different matter and are not touched here: they are
part of its type, hence of its calling convention, so a parameter nothing reads is
reported rather than removed.  A loop slot belongs to no type: the backend chose it, and
the backend can drop it.
-/

namespace LakeJs.DeadSlot

open LakeJs
open LakeJs.Ty
open LakeJs.Expr
open LakeJs.Lookup (SomeTerm)
open LakeJs.Scalarise (Env varAtIndex? spineList slotIndex mapTerm)

/-- Rebuild a loop block over one slot fewer: every variable becomes what `e` gives for
    it, and the `p`-th argument of every `Body.cont` goes. -/
def mapBodyDrop {Sg : Sig} {Δ : Ctx} (e : Env Sg Δ) (p : Nat) (σs' : List Ty) :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Option (Body Sg Δ σs' τ)
  | _, _, _, .ret t => (mapTerm e t).map .ret
  | _, _, _, .cont args => do
      -- the value this jump gives the slot goes with the slot, and is dropped *before*
      -- the rest is rebuilt: it is the one place the slot may still be mentioned
      let ts := spineList args
      let kept := ts.take p ++ ts.drop (p + 1)
      let ts' ← kept.mapM fun t => (mapTerm e t.2).map fun t' => (⟨t.1, t'⟩ : SomeTerm Sg Δ)
      (Lookup.Spine.ofList? σs' ts').map .cont
  | _, _, _, .letB (σ := σ) v b => do
      let v' ← mapTerm e v
      let b' ← mapBodyDrop (Scalarise.Env.liftList [σ] e) p σs' b
      pure (.letB v' b')
  | _, _, _, .iteB c t u => do
      let c' ← mapTerm e c
      let t' ← mapBodyDrop e p σs' t
      let u' ← mapBodyDrop e p σs' u
      pure (.iteB c' t' u')
  | _, _, _, .joinPointB (params := ps) (σ := σ) body rest => do
      let body' ← mapTerm (Scalarise.Env.liftList ps.reverse e) body
      let rest' ← mapBodyDrop (Scalarise.Env.liftList [Ty.fn ps σ] e) p σs' rest
      pure (.joinPointB body' rest')

/-- The loop with slot `p` removed, when no iteration reads that slot. -/
def dropSlot? {Sg : Sig} {Γ : Ctx} {τ : Ty} {σs : List Ty}
    (init : Spine Sg Γ σs) (body : Body Sg (σs.reverse ++ Γ) σs τ) (p : Nat) :
    Option (Term Sg Γ τ) := do
  guard (p < σs.length)
  -- nothing in the block reads the slot — the value each jump hands *it* is not a read,
  -- since that value goes when the slot goes
  guard (Usage.Body.occSlotAt p (slotIndex σs.length p) body == 0)
  let n := σs.length
  let σs' := σs.eraseIdx p
  let n' := σs'.length
  let Γn : Ctx := σs'.reverse ++ Γ
  let env : Env Sg Γn := fun i =>
    if i < n then
      let s := n - 1 - i
      if s == p then none
      else varAtIndex? Γn (n' - 1 - (if s < p then s else s - 1))
    else varAtIndex? Γn (i - n + n')
  let body' ← mapBodyDrop env p σs' body
  let its := spineList init
  let init' ← Lookup.Spine.ofList? σs' (its.take p ++ its.drop (p + 1))
  pure (.loop init' body')

/-- The term with slot `p` of *its own* loop dropped, when it is a loop and that slot is
    dead. -/
def dropAt? {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) (p : Nat) :
    Option (Term Sg Γ τ) :=
  match t with
  | .loop init body => dropSlot? init body p
  | _ => none

/-- Drop the dead slots of one loop, from the last slot to the first: dropping slot `p`
    renumbers the slots after it, so going downwards keeps the numbering of the slots
    still to be looked at. -/
def dropSlotsGo {Sg : Sig} {Γ : Ctx} {τ : Ty} : Nat → Term Sg Γ τ → Term Sg Γ τ
  | 0, t => t
  | p + 1, t =>
    match dropAt? t p with
    | some t' => dropSlotsGo p t'
    | none => dropSlotsGo p t

/-- Drop every slot of this term's own loop that no iteration reads. -/
def dropDeadSlots {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Term Sg Γ τ :=
  match t with
  | .loop (σs := σs) _ _ => dropSlotsGo σs.length t
  | _ => t

mutual

/-- Drop the slots no iteration reads, from every loop of a term. -/
def Term.dropDead {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Term Sg Γ τ
  | _, _, .loop init body => dropDeadSlots (.loop (Spine.dropDead init) (Body.dropDead body))
  | _, _, .lamN b => .lamN (Term.dropDead b)
  | _, _, .apN f args => .apN (Term.dropDead f) (Spine.dropDead args)
  | _, _, .lamProd rets => .lamProd (Spine.dropDead rets)
  | _, _, .callProd f args i => .callProd (Term.dropDead f) (Spine.dropDead args) i
  | _, _, .jsOp op args => .jsOp op (Spine.dropDead args)
  | _, _, .lazyMk t => .lazyMk (Term.dropDead t)
  | _, _, .lazyForce t => .lazyForce (Term.dropDead t)
  | _, _, .letE e b => .letE (Term.dropDead e) (Term.dropDead b)
  | _, _, .ite c t u => .ite (Term.dropDead c) (Term.dropDead t) (Term.dropDead u)
  | _, _, .ctor i fs h args => .ctor i fs h (Spine.dropDead args)
  | _, _, .proj v i j h => .proj (Term.dropDead v) i j h
  | _, _, .tagOf v h => .tagOf (Term.dropDead v) h
  | _, _, .caseTag s alts h => .caseTag (Term.dropDead s) (Alts.dropDead alts) h
  | _, _, .joinPoint body rest => .joinPoint (Term.dropDead body) (Term.dropDead rest)
  | _, _, .jump v args => .jump v (Spine.dropDead args)
  | _, _, t => t

/-- `Term.dropDead`, on every term of a spine. -/
def Spine.dropDead {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Spine Sg Γ σs
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons (Term.dropDead t) (Spine.dropDead rest)

/-- `Term.dropDead`, on every branch of a case. -/
def Alts.dropDead {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Alts Sg Γ τ tags
  | _, _, _, .deflt t => .deflt (Term.dropDead t)
  | _, _, _, .cons tag t rest => .cons tag (Term.dropDead t) (Alts.dropDead rest)

/-- `Term.dropDead`, inside a loop block. -/
def Body.dropDead {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Body Sg Γ σs τ
  | _, _, _, .ret t => .ret (Term.dropDead t)
  | _, _, _, .cont args => .cont (Spine.dropDead args)
  | _, _, _, .letB e b => .letB (Term.dropDead e) (Body.dropDead b)
  | _, _, _, .iteB c t u => .iteB (Term.dropDead c) (Body.dropDead t) (Body.dropDead u)
  | _, _, _, .joinPointB body rest =>
      .joinPointB (Term.dropDead body) (Body.dropDead rest)

end

/-! ## A worked example -/

/-- A loop of two slots, of which the body reads only the second: it answers the second
    slot straight away and never looks at the first. -/
def deadSlotExample : Term [] [] Ty.nat :=
  .loop (σs := [Ty.nat, Ty.nat])
    (.cons (.lit (.nat 0)) (.cons (.lit (.nat 7)) .nil))
    (.ret (♯0))

/-- The compiler refuses the loop with the dead slot … -/
example : Usage.Term.usesOkDecl deadSlotExample = false := by decide +kernel

/-- … and the pass is what makes it acceptable. -/
example : Usage.Term.usesOkDecl (Term.dropDead deadSlotExample) = true := by decide +kernel

end LakeJs.DeadSlot
