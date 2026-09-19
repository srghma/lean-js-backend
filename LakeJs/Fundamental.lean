module

public import LakeJs.Terminating

@[expose] public section

set_option autoImplicit false

/-!
# The fundamental theorem: a guarded recursion is the function it was translated from

This file used to carry the induction of a Tait-style logical relation: *a certified term
is reducible under any reducible substitution*, from which one read off that a certified
closed term runs out of steps.  Termination is no longer the open question — every term
of the one grammar has a value (`LakeJs.Terminating`) — so the induction has nothing left
to prove.

What has taken its place is the theorem the front end actually needs.  `Term.fix` answers
with its `stuck` branch at a self call whose measure does not descend, so a translated
recursion is faithful to the Lean function it came from exactly when **every call it makes
descends**.  That is `Term.fix_implements`:

> if every recursive call is at a lexicographically **smaller measure** — the hypothesis
> `decreasing_by` discharges on the Lean side — then applying the recursion to any
> arguments gives the Lean function's value at those arguments.

Note what is *not* a hypothesis any more.  The rank-based design also required the term's
rank to *outlast* the recursion at every argument list, an iteration bound that no one
verified and that the front end had to invent; here the measure is compared afresh at each
call, so the only obligation is the one Lean has already proved.

The hypothesis is about the *reachable* calls only, which is what makes the erased proof
arguments of `Tco04`-style definitions harmless — with one honest caveat, recorded in
`LakeJs.Examples.WellFounded`: a branch that erasure made reachable and that does **not**
descend now answers `stuck`, visibly, instead of answering a wrong number quietly.

`Term.fix_implements_closed` is the same statement for a closed term, phrased with
`Term.Implements`, and is the lemma every faithfulness proof in `LakeJs.Examples` ends
with.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {ps : List Ty} {τ : Ty} {k : Nat}

/-- **The fundamental theorem of the guarded recursion.**  A `Term.fix` whose body is
    faithful given a self-reference faithful at smaller measure computes the function it
    was translated from. -/
theorem Term.fix_implements (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)
    (f : Env ps → τ.den) (m : Env ps → Lex.NatVec k)
    (hm : ∀ as : Env ps, Term.measureVal measure δ γ ρ as = m as)
    (hstep : ∀ (g : Env ps → τ.den) (as : Env ps),
      (∀ bs : Env ps, Lex.NatVec.Lt (m bs) (m as) → g bs = f bs) →
      body.eval δ (as.append γ) (.cons g ρ) = f as)
    (args : Env ps) :
    Env.apply ((Term.fix ps k measure body stuck).eval δ γ ρ) args = f args := by
  rw [Term.apply_eval_fix]
  exact Term.fixFun_eq_of_descends measure body stuck δ γ ρ f m hm hstep args

/-- The closed case, packaged as `Term.Implements`: this is what a faithfulness proof of
    a translated top-level function states. -/
theorem Term.fix_implements_closed (measure : Spine Sg (ps ++ []) [] (Ty.nats k))
    (body : Term Sg (ps ++ []) [⟨ps, τ⟩] τ) (stuck : Term Sg (ps ++ []) [] τ)
    (δ : GEnv Sg.decls) (f : Env ps → τ.den) (m : Env ps → Lex.NatVec k)
    (hm : ∀ as : Env ps, Term.measureVal measure δ .nil .nil as = m as)
    (hstep : ∀ (g : Env ps → τ.den) (as : Env ps),
      (∀ bs : Env ps, Lex.NatVec.Lt (m bs) (m as) → g bs = f bs) →
      body.eval δ (as.append .nil) (.cons g .nil) = f as) :
    (Term.fix (Γ := []) ps k measure body stuck).Implements δ f := by
  intro args
  exact Term.fix_implements measure body stuck δ .nil .nil f m hm hstep args

end LakeJs.Expr

end
