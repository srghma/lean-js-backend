module

public import Lean
public meta import LakeJs.DescentSimp
public import LakeJs.DescentTactic

@[expose] public section

set_option autoImplicit false

/-!
# `faithful_eq`: the equation half of a translation-validation proof

`TERM_RANK_FLAKINESS_AND_ALTERNATIVES.md` §8 step 7 asks for the other half of (F): not a
sample of inputs on which the emitted term and the Lean declaration agree, but a **proof**
that they agree at every input.  `LakeJs.Descends` reduced that to two obligations, and
`LakeJs.DescentTactic` automated the first:

| obligation | discharged by |
| :-- | :-- |
| the recursion descends (`Term.Descends`) | `descent_auto` — `<Module>Descends.lean` |
| the body, run with the **Lean function** as its self-reference, answers what the Lean function answers | `faithful_eq` — this module, `<Module>Faithful.lean` |

`Term.fix_implements_of_equation` combines them into `Term.Implements`, and nothing in
between needs an induction: the induction is inside the generic theorem, once and for all.

The second obligation is an equation between

* the emitted body, evaluated — which `descent_reduce` turns into ordinary arithmetic,
  because the body is concrete syntax and the interpreter is a definition; and
* the Lean function at the same arguments — which its own equation lemmas unfold.

So the tactic is: run the interpreter, then split on whatever the body branched on, and
match each branch against the Lean equation.  `faithful_eq` is that pipeline, and it is
what a generated `<Module>Faithful.lean` calls once per declaration.
-/

namespace LakeJs.Expr

open Lean Elab Tactic Meta in
/-- Case-split every `Nat` in the context, once each.  The emitted body of a recursion on
    a number branches on a test like `n = 0` and calls itself at `n - 1`; the Lean
    function it came from matches on `0` and `n + 1`.  Splitting the argument is what
    brings the two into the same shape, and it is the one step `simp` cannot take. -/
elab "faithful_scalar_cases" : tactic => do
  let fvs ← (← getMainGoal).withContext do
    let mut acc : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || d.isAuxDecl then continue
      if (← whnfR d.type).isConstOf ``Nat then acc := acc.push d.fvarId
    pure acc
  if fvs.isEmpty then throwError "faithful_scalar_cases: no scalar argument to split"
  let mut goals := [← getMainGoal]
  for fv in fvs do
    let mut next : List MVarId := []
    for g in goals do
      let subs : List MVarId ←
        try
          let cs ← g.cases fv
          pure (cs.toList.map (·.mvarId))
        catch _ => pure [g]
      next := next ++ subs
    goals := next
  replaceMainGoal goals

/-- Close one branch of the equation: what is left after the interpreter has run and the
    branches have been split is an identity between arithmetic and the Lean function's own
    unfolding. -/
syntax "faithful_leaf" (ppSpace colGt ident) : tactic

macro_rules
  | `(tactic| faithful_leaf $f:ident) => `(tactic|
      first
        | rfl
        | (simp only [$f:ident]; done)
        | (simp_all [$f:ident]; done)
        | (simp +arith only [$f:ident]; done)
        | omega
        | (simp_all [$f:ident] <;> omega)
        | (simp_all [$f:ident] <;> rfl))

/-- Run the interpreter over the emitted body: the result is a Lean expression in the
    argument components, with the self-reference standing for the Lean function itself. -/
syntax "faithful_reduce" (ppSpace colGt ident) : tactic

macro_rules
  | `(tactic| faithful_reduce $fv:ident) => `(tactic|
      (try simp only [$fv:ident]
       try descent_reduce
       try descent_denote
       try simp only [descent_eval, REnv.get, $fv:ident, Bool.cond_decide,
         decide_eq_true_eq, cond_true, cond_false]))

/-- **The equation half of faithfulness.**  `faithful_eq fun_f f` proves

    ```
    body.eval δ (as.append .nil) (.cons fun_f .nil) = fun_f as
    ```

    where `fun_f` is the Lean function `f` read as a function of an argument environment.
    It runs the interpreter and then matches the branches of the emitted body against the
    branches of `f`'s own equation. -/
syntax "faithful_eq" (ppSpace colGt ident) (ppSpace colGt ident) : tactic

macro_rules
  | `(tactic| faithful_eq $fv:ident $f:ident) => `(tactic|
      (faithful_reduce $fv
       first
         | faithful_leaf $f
         | (split <;> faithful_leaf $f)
         | (faithful_scalar_cases <;>
             first
               | faithful_leaf $f
               | (split <;> faithful_leaf $f))
         | (split <;> faithful_scalar_cases <;> faithful_leaf $f)
         | (split <;> split <;> faithful_leaf $f)))

end LakeJs.Expr

end
