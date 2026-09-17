# Proposals for further optimisation

What the backend already does, and what it does not do yet.  Each proposal below says
what the emitted JavaScript looks like now, what it could look like, what it would take,
and how it would be checked.  The examples are all taken from the snapshots in this
repository, so each one can be reproduced with

```
lake build lean-to-js-backend
lake env ./.lake/build/bin/lean-to-js-backend --stdout SnapshotsPBOPure/Fusion02.lean
```

and the `<Module>-Expr.txt` beside each snapshot shows the same declarations *before* the
optimiser ran, which is the input each proposal is about.

## Where the optimiser stands today

| Pass | File | What it does |
| :--- | :--- | :--- |
| Simplifier | `LakeJs/Simp.lean` | dead `let`, `let` of a copy, `let x = e; x`, reading a field of a constructor built right here, eta-contraction, the guarded (non-truncating) predecessor |
| Inliner | `LakeJs/Inline.lean` | a saturated call of an `@[inline]` declaration, or of a small straight-line one, becomes that declaration's body |
| Scalariser | `LakeJs/Scalarise.lean` | a constructor a loop carries round travels as its fields |
| Specialiser | `LakeJs/Specialise.lean` | a mutually tail-recursive cycle whose jumps name their target loses its dispatch tag |
| Dead declarations | `LakeJs/Compile.lean` | a declaration nothing exports and nothing calls is not printed |
| The rules as a relation | `LakeJs/Reduce.lean` | the simplifier's and the inliner's rules as an inductive `Prop`, with `Term.simpAll_chain` and `Term.inlineCalls_chain` |

Everything there is a function `Term Sg Γ τ → Term Sg Γ τ`: the type of a term is its
specification, so no pass can produce an ill-typed or ill-scoped program.  Every proposal
below keeps that property — none of them needs a new kind of term, except where it says
so.

## 1. Lower a block into statements instead of an arrow function

**Now.**  The printer turns a `Term` into a JavaScript *expression*, and flattens a chain
of `let`s into statements only where the context is already a statement.  Inlining a
declaration whose body is a chain of `let`s into a position that is an expression
therefore prints an immediately-invoked arrow function:

```js
const v24 = (() => {
  const v25 = v19.length;
  const v26 = v25 * 2;
  return $lean_mk_array(v26, { tag: 0 });
})();
```

(`SnapshotsMy/HashContainers.js`, from inlining `Raw.expand`.)

**Proposal.**  Give `LakeJs/EmitJs.lean` a statement-position lowering: a function
`stmtsOf : Term Sg Γ τ → (MiniStatement list, MiniExpr)` that emits `const` statements for
the `let`s it meets and `if`/`else` statements for the branches, and falls back to the
present expression printer only where the context really is an expression (an argument, a
field of an object literal).  Every `let` the term holds already has a name and a
depth, so no gensym is needed and the names cannot collide.

**Why.**  It removes every IIFE from the output, it makes the inliner strictly profitable
(the arrow function is the only reason the inliner currently refuses a branching body:
`Inline.hasControlFlowTerm`), and it shortens the output of the passes that already run.

**Check.**  `LakeJsTest` asserts `absent := ["(() =>"]` over the corpus, and the Node
suites keep passing.

## 2. Bind an argument that is a computation, and inline anyway

**Now.**  `LakeJs/Inline.lean` substitutes an argument for a parameter only when the
argument is a *value* — a variable, a literal, a global, an extern.  Anything else leaves
the call alone, because substituting it could duplicate the work (a parameter the body
reads twice) or drop it (a parameter the body never reads).

**Proposal.**  Where an argument is not a value, wrap the inlined body in a `let`:
`f(g(x))` with `f = fun a => …a…a…` becomes `let a = g(x); …a…a…`.  The `let` evaluates
the argument exactly once whatever the body does with it, and the simplifier's dead-`let`
and copy rules then remove the binding where it turns out to be a copy or unread.  The
construction is the one `subOfSpine` already performs, with `Term.letE` in front of the
body and the arguments weakened by one binder each.

**Why.**  The terms the translation produces are in administrative normal form, so today's
restriction costs little — but it is the reason a call inside a call is left alone, which
is exactly where a `@[inline]` declaration is most often used.

## 3. Fold constants and identities

**Now.**  Nothing in `Term` is evaluated: `1 + 2` prints as `1 + 2`.  The literals that do
get folded are folded by Lean, before the backend sees the declaration.

**Proposal.**  A rule per primitive, on a spine all of whose terms are literals:
`Externs.lean_nat_add` on two `Lit.nat`s is the `Lit.nat` of their sum, and so on for the
comparisons, the boolean connectives and `lean_string_append`.  The types make this safe
to write: `Externs σs τ` fixes the type of the answer, so folding cannot change the type
of the term.
Add the identities at the same time — `x + 0`, `x * 1`, `x - 0`, `s ++ ""`, `if true`,
`if false` — each of which is a rewrite the inliner now produces regularly, since an
inlined body meets the literal its caller passed.

**Why.**  This is what makes inlining pay: `foo 1 2` is only `3` if something folds
`1 * 2 + 1`.  Today Lean happens to do it; the backend should not depend on that.

**Check.**  Each fold is a `Step` constructor in `LakeJs/Reduce.lean` and a `#guard` on a
closed term.

## 4. Inline a call whose argument is a lambda, by specialising the callee

**Now.**  A function that takes a function is called with a closure:

```js
export const test3 = (v0, v1, v2) => {
  const v3 = (v3, v4, v5) => mkSum3(v0, v3, v4, v5);
  return applyThree(v3, v1, v2);
};
```

(`SnapshotsMy/AppArity.lean`.)  The closure is built once per call of `test3` and called
twice inside `applyThree`.

**Proposal.**  Where a call passes a lambda to a declaration the module also emits,
generate a specialised copy of the callee with that parameter substituted, and call the
copy.  This is the same substitution the inliner does, applied to one argument rather than
to all of them, and it needs the same side condition (the parameter must be used linearly,
or the lambda must be small).  Lean's own `@[specialize]` marks the declarations that want
it.

**Why.**  It removes a closure allocation per call and turns an indirect call into a
direct one, which is what the `Fusion01`/`Fusion02` style of code is full of.

## 5. Hoist a constant constructor

**Now.**  A nullary constructor is built where it is used: `const v1 = { tag: 0 };`
appears inside `useHigher`, inside every loop that ends a list, and so on.  Each execution
allocates a fresh object.

**Proposal.**  Hoist every `Term.ctor` with no arguments to a module-level `const`, and
refer to it — one object per constructor per module, allocated when the module loads.
The terms are closed, so the hoisting is `Term.rename?` with the empty renaming, and the
signature grows by one entry per hoisted constructor.

**Why.**  Lean's own runtime does exactly this (a nullary constructor is a boxed scalar).
It removes an allocation from the inner loop of every list- or option-producing function.

**Caveat.**  The emitted objects are shared, so the hoisting is only sound while nothing
mutates them — which is true today (`Term` has no assignment) and would have to stay true
if proposal 7 is taken up.

## 6. Move work out of a loop

**Now.**  `Term.loop` carries its body as written.  A `letB` whose value mentions no loop
variable is recomputed on every iteration:

```js
while (true) {
  const v6 = v3._2;       // v3 never changes
  const v7 = v6(v4);
  …
}
```

(`SnapshotsPBOPure/Fusion02.js`.)

**Proposal.**  Loop-invariant code motion: a `Body.letB e b` whose `e` can be
strengthened out of the loop variables — `Term.rename?` through the renaming that drops
them, which succeeds exactly when `e` does not mention them — is lifted in front of the
`Term.loop`.  The machinery is `LakeJs/Rename.lean`, unchanged; what is new is the
traversal that walks a `Body` collecting liftable bindings.

**Why.**  It is the classic loop optimisation, and the scalariser has already made the
loop variables explicit, so "does this mention a loop variable" is exactly a
strengthening.

## 7. Push onto an array instead of copying it

**Now.**  `Array.push` (`lean_array_push`) prints as `[...v5, v10]`, which allocates a new array and
copies it: a loop that builds an array of `n` elements is quadratic.

**Proposal.**  Where the array being pushed onto is *dead after the push* — its only use
is the push, which is what a loop accumulator looks like after scalarisation — emit
`v5.push(v10)` and reuse the array.  The condition is a linearity check on the term, in
the style of `Scalarise.lean`'s use counting.  `SnapshotsMy/ArrayInPlace.lean` is the
module that exercises it.

**Why.**  It is the difference between a quadratic and a linear `Array.map`, and it is the
largest constant-factor win left in the corpus.

**Caveat.**  It is the one proposal here that makes an emitted value mutable, so it has to
be stated carefully: the check is that no other term holds the old array.

## 8. A `switch` for a dense dispatch

**Now.**  `Term.caseTag` prints as a chain of ternaries or of `if`s on `e.tag`.

**Proposal.**  Where the tags are `0 … n - 1` and `n` is large enough, print
`switch (e.tag) { case 0: … }`.  `Ty.caseOk` already guarantees the tags are distinct
constructors of the scrutinee's type, so the branches cannot overlap and the default is
always there.

**Why.**  An engine compiles a dense `switch` to a jump table; a chain of ternaries it
compiles to a chain of comparisons.  The win grows with the number of constructors, and
`SnapshotsPBOPure/CaseJacobs.lean` and the `Repr` instances are the cases with many.

## 9. Drop a parameter nothing reads

**Now.**  The compiler *reports* them — `note … never reads its parameter(s) [1, 3, 4]` in
the test run — and prints them, because a parameter belongs to the calling convention.

**Proposal.**  For a declaration the module does not export, rewrite the declaration and
every call of it together: drop the parameter from the lambda and the argument from each
call.  Both edits are the same kind of rewrite the merged-loop passes already make, and
the signature check (`Sig.namesUnique`) keeps the two in step.

**Why.**  `VanLaarhovenTraversals01` passes three arguments nothing reads through every
level of a traversal.

## 10. Cover the rest of the optimiser by the relation

**Now.**  `LakeJs/Reduce.lean` states the simplifier's rules as an inductive `Step` and
proves `Term.simpAll_chain : t —↠ Term.simpAll t`.  The inliner, the scalariser and the
specialiser are not covered.

**Proposal, in the order of difficulty.**

* **The inliner — done.**  `Step` takes the table of the module's inlinable declarations
  (`LakeJs.Inline.Table`) and has the two constructors `delta`, for a saturated call
  (`betaGlobal? tbl r args = some t → Step tbl (.apN (.global r) args) t`), and
  `deltaLit`, for a reference to a declaration whose body is a literal;
  `Term.inlineCalls_chain : t —↠[tbl] LakeJs.Inline.Term.inlineCalls tbl t` is proved by
  the same induction as `simp_chain`, and `Term.simp_inline_simp_chain` covers the three
  passes the driver runs in front of the scalariser.
* **The loop-slot passes.**  Scalarising and specialising change the *slots* of a loop, so
  they do not keep the type of its body: they relate a `Term Sg Γ τ` to a term whose loop
  has different `σs`.  Covering them needs a relation between terms of two slot types,
  which is a different statement, not a bigger one.
* **Confluence.**  Answered, in the negative, by `LakeJs/ReduceConfluence.lean`: eta and
  the inliner's `delta` rewrite one wrapper to two different normal forms, so `Step` is
  not Church-Rosser and not even locally confluent.  What a new rule therefore has to
  respect is not confluence but the *order* the backend applies its rules in — a rule
  that only fires after another must be placed after it in the sweep.

## 11. Tail-call another declaration without growing the stack

**Now.**  A self tail call is a `continue` (`Term.loop`), and a mutually recursive group
that tail-calls inside itself becomes one loop (`LakeJs/Specialise.lean`).  A tail call to
a declaration *outside* the group is an ordinary call, and the stack grows.

**Proposal.**  Where a declaration's answer is a call of another declaration the module
emits, and that other declaration is itself a loop, inline the loop (proposal 2's
machinery) rather than call it — one loop, entered with the arguments of the call.  This
is exactly what `Specialise.enterTerm?` does for a group member, applied across groups.

**Why.**  It is the only remaining way the emitted code can run out of stack on input
Lean proved terminating.

## Order of work

1. §1 (statement lowering) — it unblocks §2 and removes the one shape the inliner now
   refuses.
2. §3 (constant folding) — it is what makes inlining pay, and it is a handful of `Step`
   constructors.
3. §7 (array push) — the largest constant factor in the corpus.
4. The rest, in the order the corpus asks for them.
