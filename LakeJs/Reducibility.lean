module

public import LakeJs.SN

@[expose] public section

set_option autoImplicit false

/-!
# What replaced the logical relation: the descent lemma

This module used to hold the Tait-style logical relation — `Red τ t`, *`t` is reducible at
`τ`* — with which the totality of the evaluator was proved for a certified fragment of the
grammar.  A logical relation is what one needs when the question is *does this term
stop?*, and that question has no content any more: `Term.eval` is a Lean function, so
every term stops.

The question that *does* have content is the next one: **does this term compute the Lean
function it was translated from?**  A guarded recursion answers `stuck` at a self call
whose measure does not descend, so the answer is: yes, provided every call the body makes
descends.  The lemma that says so is `Term.fixFun_eq_of_descends`, and it is the workhorse
of every faithfulness proof in `LakeJs.Examples`:

> Let `f` be a Lean function of the arguments and `m` the value of the term's measure.  If
> the body, given a self-reference that already agrees with `f` on every argument of
> lexicographically **smaller** measure, agrees with `f`, then the recursion agrees with
> `f` — at every argument.

The hypothesis is exactly what `decreasing_by` proves on the Lean side, and nothing else
is required: there is no iteration bound to dominate, no `+ 1`, and no bound on the number of
iterations.  That is the whole point of the guarded design — the front end is asked only
for what Lean already proved.

`Term.Implements` names the conclusion for a closed term.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {ps : List Ty} {τ : Ty}

/-- **The descent lemma.**  If one unrolling of the body is faithful whenever its
    self-reference is faithful at every strictly smaller measure, then the recursion is
    faithful — everywhere, with no side condition on how many iterations it takes. -/
theorem Term.fixFun_eq_of_descends {k : Nat} (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)
    (f : Env ps → τ.den) (m : Env ps → Lex.NatVec k)
    (hm : ∀ as : Env ps, Term.measureVal measure δ γ ρ as = m as)
    (hstep : ∀ (g : Env ps → τ.den) (as : Env ps),
      (∀ bs : Env ps, Lex.NatVec.Lt (m bs) (m as) → g bs = f bs) →
      body.eval δ (as.append γ) (.cons g ρ) = f as)
    (as : Env ps) :
    Term.fixFun measure body stuck δ γ ρ as = f as := by
  have hfun : Term.measureVal measure δ γ ρ = m := funext hm
  show Lex.guardedFix (Term.measureVal measure δ γ ρ) _ _ as = f as
  rw [hfun]
  exact Lex.guardedFix_eq m _ _ f hstep as

/-- A closed term of a function type **implements** a Lean function when it answers with
    that function's value on every argument list. -/
def Term.Implements (t : Term Sg [] [] (Ty.arrows ps τ)) (δ : GEnv Sg.decls)
    (f : Env ps → τ.den) : Prop :=
  ∀ args : Env ps, Env.apply (t.evalClosed δ) args = f args

/-- The definition, unfolded: this is what a faithfulness proof ends with. -/
theorem Term.implements_iff (t : Term Sg [] [] (Ty.arrows ps τ)) (δ : GEnv Sg.decls)
    (f : Env ps → τ.den) :
    t.Implements δ f ↔ ∀ args : Env ps, Env.apply (t.evalClosed δ) args = f args :=
  Iff.rfl

end LakeJs.Expr

end
