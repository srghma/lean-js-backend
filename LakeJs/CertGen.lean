module

public import LakeJs.TermTotal
public import LakeJs.TailShape
public import LakeJs.InlineSize
public import LakeJs.Diverge
public import LakeJs.DivergeNeg

@[expose] public section

set_option autoImplicit false

/-!
# The measure *is* the certificate

This module used to *generate* certificates: given a block whose labels were all shared
tails, it built, by recursion on an inlining measure, the object that licensed running the
block, and it gave up on anything containing a loop.  With the one grammar there is
nothing to generate — every term terminates (`LakeJs.Terminating`) — because the thing a
certificate used to supply is now a **field of the term**: `Term.fix`'s measure, checked
by the evaluator at every self call.

So what a front end needs from this module is no longer a proof search, and no longer an
*iteration bound* either.  It is two measure builders, one per admitted kind of Lean
recursion, together with the lemma that each satisfies the hypothesis of
`Term.fix_implements`:

| Lean's kind | measure term | builder |
| :-- | :-- | :-- |
| structurally recursive | size of the recursion subject | `Term.structMeasure` |
| well-founded recursive | transcribed `termination_by` components | `Term.measure1`, or a spine of them |

Neither is "plus one" any more.  Under the guarded semantics the obligation is that the
measure **strictly descends** at each self call — exactly what Lean's `decreasing_by`
proves — and not that some counter outlast the recursion.  `Term.fix_implements_measure`
is the resulting one-step recipe for a single-component measure, and
`Term.fix_implements_structural` its specialisation to a one-argument structural
recursion.

The four kinds of definition this grammar refuses need no gate here at all: there is no
constructor to write them with (see `LakeJs.Expr`), and `LakeJs.Totality` is where the
front end turns a `partial`, `unsafe` or `IO` declaration away.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {ps : List Ty} {σ τ : Ty}

/-! ## The two measure builders -/

/-- **A one-component measure**: the common case, and what a transcribed `termination_by`
    with a single expression becomes. -/
def Term.measure1 (m : Term Sg Γ Ρ (.prim .nat)) : Spine Sg Γ Ρ (Ty.nats 1) :=
  .cons m .nil

/-- **A measure from the recursion subject**: the structural case.  The size of the
    value's runtime tree strictly decreases along every strict sub-component, so it is a
    measure — and, unlike a counted rank, it needs no `+ 1`, because nothing counts
    iterations. -/
def Term.structMeasure (e : Term Sg Γ Ρ σ) : Spine Sg Γ Ρ (Ty.nats 1) :=
  Term.measure1 (.structSize e)

/-- The value of a one-component measure. -/
@[simp] theorem Term.measureVal_measure1 {k : Nat} (m : Term Sg (ps ++ Γ) Ρ (.prim .nat))
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (as : Env ps) (_hk : k = 1) :
    Term.measureVal (Term.measure1 m) δ γ ρ as
      = .cons (show Nat from m.eval δ (as.append γ) ρ) .nil := rfl

/-! ## What the builders buy: the descent hypothesis, in `Nat` -/

/-- **The well-founded recipe.**  A recursion with a single-component measure computes the
    Lean function it came from as soon as the measure term computes the measure and every
    recursive call is at a smaller measure.  The hypothesis of `Term.fix_implements` is
    discharged here, once and for all — and there is no iteration-bound hypothesis left to
    discharge. -/
theorem Term.fix_implements_measure (measure : Term Sg (ps ++ Γ) Ρ (.prim .nat))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)
    (f : Env ps → τ.den) (m : Env ps → Nat)
    (hm : ∀ as : Env ps, measure.eval δ (as.append γ) ρ = m as)
    (hstep : ∀ (g : Env ps → τ.den) (as : Env ps),
      (∀ bs : Env ps, m bs < m as → g bs = f bs) →
      body.eval δ (as.append γ) (.cons g ρ) = f as)
    (args : Env ps) :
    Env.apply ((Term.fix ps 1 (Term.measure1 measure) body stuck).eval δ γ ρ) args
      = f args := by
  refine Term.fix_implements _ body stuck δ γ ρ f (fun as => .cons (m as) .nil)
    (fun as => ?_) (fun g as hg => hstep g as (fun bs hbs => hg bs ?_)) args
  · show Lex.NatVec.cons (show Nat from measure.eval δ (as.append γ) ρ) .nil = _
    rw [hm as]
  · exact (Lex.NatVec.lt_one_iff _ _).mpr hbs

/-- The value of the sole argument of a one-argument recursion, read out of the extended
    environment. -/
theorem Env.eval_var_head_append (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)
    (as : Env [σ]) :
    (Term.var (Sg := Sg) (Ρ := Ρ) (Var.head (Γ := Γ))).eval δ (as.append γ) ρ
      = as.get .head := by
  cases as with
  | cons v rest => rfl

/-- **The structural recipe**, for a recursion on one argument.  The measure is the size
    of that argument's runtime tree. -/
theorem Term.fix_implements_structural
    (body : Term Sg ([σ] ++ Γ) (⟨[σ], τ⟩ :: Ρ) τ) (stuck : Term Sg ([σ] ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (f : Env [σ] → τ.den)
    (hstep : ∀ (g : Env [σ] → τ.den) (as : Env [σ]),
      (∀ bs : Env [σ],
        Data.size (σ.toData (bs.get .head)) < Data.size (σ.toData (as.get .head)) →
        g bs = f bs) →
      body.eval δ (as.append γ) (.cons g ρ) = f as)
    (args : Env [σ]) :
    Env.apply
        ((Term.fix [σ] 1 (Term.structMeasure (.var Var.head)) body stuck).eval δ γ ρ)
        args
      = f args := by
  refine Term.fix_implements_measure (.structSize (.var Var.head)) body stuck δ γ ρ f
    (fun as => Data.size (σ.toData (as.get .head))) (fun as => ?_) hstep args
  show Data.size (σ.toData ((Term.var (Var.head (Γ := Γ))).eval δ (as.append γ) ρ))
      = Data.size (σ.toData (as.get .head))
  rw [Env.eval_var_head_append δ γ ρ as]

/-! ## What used to need a certificate

The two shapes the old generator worked on are still here, and both are now trivial:

* a flat block (`Tail.Flat`) has no label, so it terminates because everything does;
* a block with join points terminates too — the grammar has no other kind of label.

The one thing that could not be certified, a loop, cannot be written: see
`LakeJs.Diverge` for what became of the term that used to witness it. -/

/-- The certificate a caller used to have to produce, for any block whatever. -/
theorem Tail.cert {Ω : LCtx} (b : Tail Sg Γ Ω Ρ τ) : b.Terminating := b.terminating

/-- And for a flat block, where the old generator succeeded. -/
theorem Tail.cert_of_flat {Ω : LCtx} (b : Tail Sg Γ Ω Ρ τ) (_h : b.Flat) :
    b.Terminating := b.terminating

end LakeJs.Expr

end
