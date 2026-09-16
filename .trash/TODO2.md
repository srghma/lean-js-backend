2. how can we improve ObjProps to not have duplicate keys? Does it make sense to restrict it?

3.

inductive EffectOp : Nat → Finset NEString → Type where
  | call (fn : NEString) (args : ExprVec n g k) : EffectOp n g
  -- e.g., console.log, mutation, etc.

inductive Stmt : Nat → Finset NEString → Type where
  | effect (eff : EffectOp n g)                  : Stmt n g  -- only allow side effects here
  | ret    (e : Expr n g)                        : Stmt n g
  | ifElse (c : BExpr n g) (thn els : Block n g) : Stmt n g

4. prove `Expr.cse_idempotent`:

A formal proof requires proving a characterisation invariant on the output—specifically, proving that `Expr.cseTop` leaves behind no repeated subterms that meet the candidate threshold, meaning a subsequent pass finds no candidates to rewrite.

5. functions should be uncurried, but if do `def foo_uncurried := uncurry foo` then .... how to `def foo_uncurried := uncurry_and_inline foo`?

```
import Lean

open Lean Meta Elab Command

syntax (name := uncurryInlineCmd) "def " ident " := uncurry_and_inline " ident : command

@[command_elab uncurryInlineCmd]
def elabUncurryAndInline : CommandElab := fun stx => do
  let newId := stx[1].getId
  let origId := stx[3].getId
  liftTermElabM do
    let env ← getEnv
    let some info := env.find? origId
      | throwError "Unknown identifier: {origId}"

    -- info.value is: fun a b => <body of foo>
    let val := info.value!

    -- Unfold/beta-reduce into a single pair parameter `p`
    forallTelescopeReducing info.type fun args _ => do
      if args.size < 2 then
        throwError "{origId} must take at least 2 arguments"
      let aType := (← inferType args[0]!)
      let bType := (← inferType args[1]!)
      let pairType ← mkAppM ``Prod #[aType, bType]

      -- Construct `fun p => val p.1 p.2`
      let body ← withLocalDeclD `p pairType fun p => do
        let p1 ← mkAppM ``Prod.fst #[p]
        let p2 ← mkAppM ``Prod.snd #[p]
        let applied := mkAppN val #[p1, p2]
        -- Beta-reduce so foo's lambda vanishes into its body
        let inlined ← whnfCore applied
        mkLambdaFVars #[p] inlined

      let type ← inferType body
      addDecl <| Declaration.defnDecl {
        name := newId
        levelParams := info.levelParams
        type := type
        value := body
        hints := ReducibilityHints.regular 1
        safety := DefinitionSafety.safe
      }
```

???

5. .toString() is faster that String(x) and "" + x
