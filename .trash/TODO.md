## 6. Object spread and computed keys

Property lists have no spread, so `{...o, k: v}`, `Object.assign`, `Object.fromEntries` and `groupBy` remain out of reach; the array side has had spread all along. Add both to the property list, with the last-key-wins, first-position-wins order the property lookup already implements, and give the deep object type the corresponding merge. Smaller blast radius than a new expression node, and it closes the list of genuinely underivable methods.

# What the proposal is

Today an object literal is a flat list of `key: value` pairs (`ObjProps`), with no way to splice another object into it. Arrays already have this: `ExprList` has both a `cons` (one element) and a `spread` (splice all elements of another array). The proposal is to give `ObjProps` the same two-shape treatment, plus computed keys:

* **spread**: `{...o, k: v}` — copy `o`'s own enumerable properties into the literal at that position;
* **computed keys**: `{[e]: v}` — the key is an expression, converted to a string at evaluation time, rather than a fixed non-empty string.

The pay-off is that several methods that are currently *not derivable* inside the language become ordinary sugar rather than new primitives: `Object.assign(a, b)` is `{...a, ...b}`, `Object.fromEntries(es)` is a fold building `{...acc, [k]: v}`, and `groupBy` is the same shape. So it buys a chunk of the remaining wish list at the cost of one constructor and one key-form, instead of a new expression node per method.

The semantics it asks for are already implemented on the lookup side: property lookup scans and lets the **last** matching key win the value, while `Object.keys` lets the **first** occurrence win the *position*. Spread has to be defined to agree with that: merging is left-to-right, a later key overwrites an earlier one's value but not its position.

# What changes

**Yes, `Expr` changes** — specifically the `ObjProps` member of the mutual block: a `spread (src : Expr n g) (tail : ObjProps n g)` constructor, and the fixed `NEString` key of `cons` generalised to a key that may be an expression. That is one new constructor and one field-type change inside the existing mutual block, so no new `Expr` node and no new binder.

**`BExpr` is not affected.** Nothing about spread or computed keys is boolean-valued; `truthy`, `isTag`, `isArray` and the comparison operators are untouched.

Everything that traverses `ObjProps` has to gain the new case. That is mechanical but wide, because `ObjProps` is traversed by every pass. The main files:

* `Expr.lean` — the datatype, `mono`, `size`, and the generic traversals defined with it
* `Run.lean` / `RunStrict.lean` — the reference interpreters, plus the value-level merge on `Value.obj`
* `Eval.lean`, `EvalCore.lean`, `Rewrite.lean`, `Normal*.lean` (`NormalNodes`, `NormalBasic`) — the optimizer and its normal-form predicates
* `JSVal.lean`, `EngineValue*.lean` — the optimizer's value layer and its object operations
* `Subst.lean`, `Stage.lean`, `Rename*.lean`, `Globals.lean` — the structural passes and their invariance lemmas
* `Render.lean`, `Elab.lean` — emitting `{...o, [k]: v}` and parsing it
* the typing layer: `TyCheck.lean`, `TyOps.lean`, plus the deep object type in `Deep/` (`Rules.lean`, `Join.lean`, `Sub.lean`, `Lattice.lean`) — where the merge of two deep object types is the real new content
* the proof obligations that are stated over all nodes: `Sound.lean`, `Diamond.lean`, `Idempotent.lean`, `Terminating.lean`, `PreserveEnv.lean`, `TyPreserve.lean`, and the corresponding test tables

# Does `Expr.optimize` behave differently?

Its *type* and its contract do not change; its behaviour does, in two ways.

1. On terms that use the new forms, it gains rules: a spread of a known object literal is flattened into the enclosing literal (dropping earlier duplicates of a key), a spread of a known-empty object disappears, a computed key with a known string value collapses to a static key, and `Object.keys/values/entries` of a literal whose spreads are all resolved becomes an array literal. A spread whose source is opaque stays residual, exactly as an array spread of an unknown value does.
2. On terms that do *not* use the new forms, the output is unchanged — the new rules are guarded by the new constructor. So existing tests keep their expected output.

The obligations that come with those rules are the usual ones: each new rule must be shown terminating (flattening a spread of a literal strictly decreases the measure), must not break local confluence, and must preserve the value under `run`.

# Does `Expr.run` behave differently?

Same answer: unchanged on today's terms, extended on the new ones. Its type stays `Expr n g → ValEnv n → Value`. Evaluating an object literal becomes a left-to-right merge over the property list: a `cons` appends one pair, a `spread` appends the pairs of the source value when it is an object (an array or a string spreads its indices as keys; `null` and `undefined` spread to nothing, which is what JavaScript does), and anything else — an opaque global, a stuck computation — makes the whole literal stuck, since we cannot know which keys it contributes. A computed key evaluates its key expression and converts it with the existing string conversion; if that conversion has nothing to say, the literal is stuck.

The one thing worth pinning with tests before anything else is the ordering rule, because it is the part that is easy to get subtly wrong: `{a: 1, ...{a: 2, b: 3}}` must have `a` at position 0 with value 2, not `a` at the end — first-position-wins, last-value-wins, which is what the current lookup and key enumeration already do.

------------------------------
## 7. Parity properties for the fold rule, and more type-driven rewrites

Two loose ends worth tying:

* **Preservation.** The flat checker's type only improves under an optimization step. The same should hold for the extended checker, together with the statement that the tree analysis is stable under the rewrite relation — that is what lets a later pass trust an earlier one.
* **Rules that consume what is already proved.** Static string concatenation when either operand is known to be a string, and pruning a fold's *branches* whose tags the scrutinee's type excludes (the dual of the default elimination just added) are both justified by theorems that exist or are one step away; they just are not wired into the pass yet.

**What the proposal is**

It has two independent halves.

*Half one — parity properties (proof-only).* The flat checker already has a preservation theorem: optimizing a term never makes its inferred type worse. The extended checker (the one with the tree/fold rule) has renaming invariance but not yet preservation, and the tree analysis itself has no stability statement under the rewrite relation. Adding both is what makes passes composable: a later pass may rely on a type or a "this evaluates to a well-formed tree" fact established before an earlier pass ran, instead of re-deriving it. Nothing executable changes here — it is new theorems about existing functions.

*Half two — two new rewrite rules (behavioural).* Both are type-driven and both are already backed, or nearly backed, by existing theorems:
- fold `a + b` into a string concatenation when either operand's inferred type says "string", since then `+` is concatenation and cannot be numeric addition;
- delete a fold's *branches* whose constructor tags the scrutinee's type rules out — the dual of the already-implemented deletion of the default branch when the branches are exhaustive.

**Will `Expr`/`BExpr` change?** No. No constructor is added or removed and no index changes; both halves are statements and rules over the existing term algebra. This is precisely why it is cheap compared with a value-level change.

**Main files targeted (short list)**
- `LakeJs/TyFold.lean`, `LakeJs/TreeVal.lean` — the tree analysis and the extended checker being reasoned about.
- a new preservation module beside `LakeJs/TyPreserve.lean` / `LakeJs/TyOptStep.lean` — the extended-checker preservation and tree-stability proofs.
- `LakeJs/Rewrite.lean`, `LakeJs/EvalCore.lean`, `LakeJs/Eval.lean` — where the two new rules are wired in.
- `LakeJs/Normal*.lean`, `LakeJs/Diamond.lean`, `LakeJs/Terminating.lean`, `LakeJs/Idempotent.lean`, `LakeJs/Sound.lean` — the obligations any new rule re-opens: normal forms, local confluence, the termination measure, idempotence, and soundness against the interpreter.
- `LakeJs/TyFoldTests.lean`, `LakeJs/Tests.lean` — the test tables.

**Does `Expr.optimize` change behaviour?** The proof half, no. The rules half, yes — deliberately: on programs where the new rules fire, the optimizer returns a *different, further-reduced* term (a string literal instead of a residual `+`, a fold with fewer branches). It is only ever replaced by a term with the same meaning, so the soundness theorem against the interpreter keeps its statement; what changes is the output text and, mechanically, the termination and confluence proofs, which must be re-established for the enlarged rule set. Programs whose types are unknown are unaffected.

**Does `Expr.run` change behaviour?** No. The reference interpreter is the fixed specification here; both halves are stated *relative* to it and neither touches its definition. If the port ever forced a change to `Expr.run`, that would be the signal that a rule is not meaning-preserving.

------------------------------
## 8. Housekeeping

add A roll-up module importing the whole library, so a consumer has one import and the build has one target; splitting the few files that have grown past a thousand lines; and a small residual-size benchmark over the demo programs, checked in as guards, so the optimizer's actual goal — smaller output — is measured rather than assumed.

-----------------

## 3. Typed globals, via a global *value* environment

Today an opaque global evaluates to an opaque value, which inhabits only `unknown`, so the analysis is blindest precisely at the boundary where a backend knows most. Rather than bolting types onto the opaque value, I would make the interpreters take an assignment for the declared names, exactly as they take one for the holes. Then:

* a global typing is just an environment typing, and soundness is the theorem already proved, with one more hypothesis;
* the current behaviour is the special case where the assignment is unconstrained;
* `??`, `===` and property access on globals stop being stuck.

Carry: `run`/`runS` parameterized by the global assignment, the refinement and renaming theorems restated (they are pointwise in the assignment, so this is largely re-plumbing), and a soundness statement saying a program is safe *given* that the host respects the declared types.

Here's how I'd expect typed globals to land in this codebase. This is a design sketch, not something I've built or checked in Lean — the details below follow from how the language, the interpreters and the optimizer are currently structured.

## The shape of the change

Today a global carries only a *name*: the type index `g` is a finite set of declared names, and the single constructor that mentions one demands a proof that the name is declared. At runtime the reference interpreter answers `opaque name`, and in the type lattice an opaque value inhabits `unknown` and nothing else — which is exactly why every `unsafeGlobal` is `unknown` today, and why type-directed rules never fire on one.

Typed globals means adding two things beside each other:

1. **A global type environment** — for each declared name, a type. Call it `Σ`.
2. **A global value environment** — for each declared name, the runtime value it actually has. Call it `σ`.

and one predicate connecting them: `σ` respects `Σ` when each global's value is in its declared type. That predicate is the exact analogue of the "the assignment models the environment typing" hypothesis the hole-typing already uses; the whole development then reuses that pattern.

The interpreter side is where the real work is. `Expr.run` currently *builds in* the choice "every global evaluates to its own opaque value". I'd add a `σ`-parameterised interpreter and prove the existing one is the instance where `σ` maps each name to its opaque value; then the current interpreter, the strict interpreter, and the refinement between them are all still true as stated, and the new soundness theorem — a term of type `t` runs to a value in `t`, for every `σ` respecting `Σ` — is proved against the parameterised one. Doing it the other way round (keeping only `Expr.run` and weakening the meaning of `opaque` in the lattice) would break the clean fact that `opaque` inhabits `unknown` only, which several lattice proofs lean on.

## Do `Expr` and `BExpr` change?

**In the design above: no.** Neither gains or loses a constructor, and neither changes its indices. The name-indexed discipline already carries everything the term needs; the type assignment lives outside the term, in `Σ`, threaded through the checker, the optimizer and the interpreter as a parameter. `BExpr` in particular has no global constructor at all — globals only occur inside its `Expr` subterms — so it is untouched either way.

**The alternative — putting the types into the index** (declaring a set of name/type pairs and having the constructor demand membership of the pair) *does* change `Expr`: the constructor's signature changes, and `BExpr` changes mechanically too, since it shares the index even though none of its constructors mention a global. That ripples into weakening, renaming, substitution, both interpreters, the renderer, the rewrite relation and its confluence/termination/idempotence proofs, the engine-value results and the surface syntax. The payoff is that a term becomes self-describing — you can't apply the optimizer under the wrong `Σ`, because the term's own type says what the globals are — and the existing "the optimizer cannot invent a global" property, which holds today purely by typing, would extend for free to "cannot invent a global *of a different type*". It is the more principled version and by far the more invasive one. I'd start with the parameterised environment and only migrate the index if the mismatch risk turns out to bite.

Either way, the two existing globals-discipline theorems survive unchanged: a program whose type declares no global mentions none, and optimization stays within the declared set.

## Does `Expr.optimize`'s behaviour change?

Its *signature* has to, if it is to use the information: it needs `Σ` as an extra argument (or a version specialised to a given `Σ`, with today's function being the all-`unknown` instance). The theorem worth proving alongside is that at the all-`unknown` environment the new optimizer is the old one, so nothing regresses for programs that declare no types.

At a non-trivial `Σ`, the behaviour changes in three ways:

* **More folding.** All the existing type-directed rules start firing on globals: `typeof g` becomes a known string, `Array.isArray(g)` decides, a strict comparison between a global and a literal of a different type folds to `false`, `g == null` decides when `g` is known non-nullish, `g ?? x` collapses, `g + 1` picks numeric addition or string concatenation, a tag test on something that cannot be a constructor object folds, and a global of the empty type marks its context unreachable. Spreading a global becomes acceptable rather than rejected when it is declared iterable. This is the point of the exercise: the analysis is starved precisely at the boundary where a backend needs it.
* **More rejection.** The checker currently answers "no static guarantee" for anything involving a global, and the optimizer's error selection treats that as a limitation. With declared types, some of those become *provable* type errors, so programs that are accepted today would be reported as bugs. That is a genuine behavioural change and worth deciding deliberately — it may want to be a separate, opt-in checking pass rather than a change to the default path.
* **A conditional correctness statement.** Today the optimizer preserves meaning unconditionally. With typed globals it preserves meaning *for every assignment of globals respecting their declarations* — the guarantee becomes conditional on the declarations being truthful, which is the honest statement for an FFI boundary, but it does mean every rule-soundness lemma that consumes a global's type gains that hypothesis, and it propagates up to the top-level theorem.

The confluence, termination and idempotence results are the part I'd expect to survive best: if no *new shapes* of rewrite are introduced — only the existing type-directed ones firing more often through a sharper oracle — their structure is unchanged, and what has to be reproved is the oracle-soundness lemma, now relative to `Σ`. Any genuinely new rule would have to be shown locally confluent with the others and decreasing for the existing measure, as the current rules are.
