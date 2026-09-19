module

public import LakeJs.Progress

@[expose] public section

set_option autoImplicit false

/-!
# The term that used to diverge, and what it is now

This file used to hold the smallest witness that the language had **no** total evaluator.
The grammar of the time had a loop — a `Tail.label` with `self = true` — and the block
whose one label is a loop that jumps straight back to itself,

```
l: while (true) { continue l }
```

was a closed term of *any* type that stepped only to itself, so no evaluator of the whole
language could be a function: it had to take a fuel or answer `Option`.

**That term cannot be written any more.**  The one label of the grammar is
`Tail.join`, a join point whose body is typed in the *outer* label context, so a jump
back to the label being bound has no index to use:

```lean
-- does not elaborate: in the body of the join, `.head` is a label bound further out,
-- and here there is none
-- def loopForever {Sg : Sig} {τ : Ty} : Term Sg [] [] τ :=
--   .block (.join [] (.jmp .head .nil) (.jmp .head .nil))
```

Repeating work is `Term.fix`, and a `Term.fix` carries its measure.  The nearest
counterpart of the old `loopForever` — a recursion whose body does nothing but call itself
on the *same* arguments — is therefore a perfectly ordinary term, and it **answers** at
once: the call does not descend, so the guard refuses it and the `stuck` branch is taken.
That is the content of this file now.

Where the old scope statement said "totality holds only on a certified fragment", the new
one says: totality holds for every term, and `LakeJs.Reduce` is the proof, being a Lean
function.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

/-- **What `loopForever` became.**  A recursion of one `Nat` argument whose body does
    nothing but call itself at the same argument: the shape that used to diverge.  Its
    measure is that argument, so the call does not descend and the `stuck` branch answers
    `7` — at once, and at every input. -/
def spinTerm {Sg : Sig} : Term Sg [] [] (.nat ⇒ .nat) :=
  .fix [Ty.nat] 1 (.cons (♯0) .nil) (.selfCall .head (.cons (♯0) .nil)) (Term.natL 7)

/-- **It answers.**  There is no fuel here and no `Option`: this is the value of a closed
    term of the language, computed by `Term.eval` and checked by the kernel. -/
example : Term.runNat1 spinTerm 0 = 7 := rfl

/-- The same at any other argument: the guard refuses the call whatever the measure's
    value is, because it does not descend. -/
example : Term.runNat1 spinTerm 100 = 7 := rfl

/-- **Every closed term of the language has a value**, `spinTerm` included.  The old file
    proved the opposite for the grammar of the time; this is what replaced it. -/
theorem exists_value {Sg : Sig} {τ : Ty} (t : Term Sg [] [] τ) (δ : GEnv Sg.decls) :
    ∃ v : τ.den, t.evalClosed δ = v :=
  ⟨t.evalClosed δ, rfl⟩

/-- **A self call at the same measure answers `stuck`.**  This is why a body that only
    calls itself cannot spin, stated for an arbitrary recursion: a call whose measure does
    not descend never reaches the body. -/
theorem fix_same_measure_answers_stuck {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {ps : List Ty}
    {τ : Ty} {k : Nat} (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (args bs : Env ps)
    (h : Term.measureVal measure δ γ ρ bs = Term.measureVal measure δ γ ρ args) :
    (if (Term.measureVal measure δ γ ρ bs).lt (Term.measureVal measure δ γ ρ args)
     then Term.fixFun measure body stuck δ γ ρ bs
     else stuck.eval δ (bs.append γ) ρ) = stuck.eval δ (bs.append γ) ρ := by
  refine Term.fixFun_stuck_of_not_lt measure body stuck δ γ ρ args bs ?_
  rw [h]
  exact Lex.NatVec.lt_irrefl _

end LakeJs.Expr

end
