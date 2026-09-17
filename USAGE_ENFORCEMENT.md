# No binding for nothing: the usage discipline, and how the backend now keeps to it

`LakeJs/Usage.lean` says what it means for a term to bind no name for nothing.  Until
now that was a condition nothing in the compiler read.  It is now **enforced**: the
optimiser has two more passes whose job is to establish it, `LakeJs.Compile.compileSpec`
checks every declaration it is about to print and *refuses* the module if one fails, and
`lake test` re-checks it over the whole corpus.

## The rules

| binder | condition | why |
| :-- | :-- | :-- |
| a `let` (`Term.letE`, `Body.letB`) | read **twice or more**, or read once **under a binder** | read twice it shares a value; read once out in the open it shares nothing, and the value belongs where it is read; read once inside a lambda, a loop body, a join point or a thunk it is what keeps the work *out* of that lambda or loop, so it stays |
| a loop slot (`Term.loop`) | every slot is **read**, and the value each jump round the loop hands *that* slot is not a read of it (`Usage.Body.occSlotAt`) | the slots are the backend's own choice and belong to no type; a slot that only carries itself round is one nothing reads |
| a join point (`Term.joinPoint`) | its parameters are read, it is **jumped to at least once**, and its name appears **only** as the target of a jump | that is what makes it a join point rather than a `let` of a lambda: it never escapes, so it needs no closure |
| a function parameter (`Term.lamN`, `Term.lamProd`) | **reported, not refused** | the arity is part of the type `.fn params ret`: an exported declaration is called from outside with that many arguments, and a callback is called by the function it was handed to.  Dropping a parameter would change a type, which an optimiser of one module may not do |

`Term.usesOk` is the full discipline, function parameters included, and `WfTerm` the
subtype of the terms that pass it; `Term.usesOkDecl` is the part the compiler enforces,
and `Term.declIssues` its diagnosis, one message per violation.  The refutation theorems
— `Term.not_usesOk_letE_of_dead`, `Term.not_usesOk_letE_of_readOnce`,
`Term.not_usesOk_joinPoint_of_noJump`, `Term.not_usesOk_var_of_join`,
`Term.not_usesOk_jump_of_notJoin`, `Term.not_usesOk_lamN_of_unusedParam` — are the proofs
that each rule really does refuse the term it is about.

## The two passes that establish it

* **`LakeJs/LinearLet.lean`** moves the value of a `let` with a single reader to that
  reader.  It fires when the variable is read exactly once (`Usage.Term.occ`), that read
  is not under a binder (`Usage.Term.occUnder`), and the value is one that prints as a
  JavaScript expression (`exprSafe`) — so nothing is duplicated, no work moves into a
  loop or a closure, and no immediately-invoked arrow is introduced.  The substitution is
  `Scalarise.mapTerm (Scalarise.substHead …)`, the same one the constructor-inlining rule
  uses, so the result is a term of the same context, type and signature by construction.
* **`LakeJs/DeadSlot.lean`** drops a loop slot no iteration reads: `init` loses a value,
  every `Body.cont` loses an argument — the value it was handing the slot, which goes
  with the slot — and the body is rebuilt over the smaller list of slots.  The slots are
  not part of the type of the term a loop is, so the smaller loop is a term of the same
  type.

Both are rules of the relation of `LakeJs/Reduce.lean` — the single-reader `let` is
`Step.letCtorInline`, the dead slot the new `Step.dropDeadSlot` — and
`LakeJs/ReducePasses.lean` proves that each pass only ever produces terms the rules
reach (`Term.lineariseLets_chain`, `Term.dropDead_chain`).
`LakeJs.OptimiseChain.optimise_chain` now covers the whole pipeline, these two included.

## What it did to the output

Measured with `lake env lean scripts/check-usage.lean`, which compiles every snapshot
module and runs `Term.declIssues` over every declaration it prints:

| | declarations with a binding that breaks the discipline |
| :-- | --: |
| before | 746 of 1257 |
| with the single-reader `let` pass | 30 |
| with the "read under a binder" exception stated | 16 |
| with values that print as expressions moved too | 4 |
| with the dead loop slots dropped | 2 |
| with a function parameter reported rather than refused | **0** |

And in the generated JavaScript itself, counted by `node scripts/count-unused-bindings.mjs`:
`169 const bindings, 0 never mentioned again` — every `const` and every loop slot the
emitted modules declare is read.  The 41 unread things that remain are all *parameters*,
most of them written `_ignored` or `_unit` in the Lean source.

The two declarations left before the last row were a callback lambda ignoring a parameter
its caller's type fixes — the one case the table above reports rather than refuses.

`lake test` passes (125 modules compiled, 6 refused), and the Node suites over the
generated modules pass 2237 assertions.

## Join points, as the backend now produces them

Two things changed since the paragraph that used to stand here.

* **A loop block has a join-point binder of its own.**  `Body.joinPointB` is the
  counterpart of `Term.joinPoint` for the blocks a `Term.loop` runs: its body is a
  `Term`, so a jump to it cannot continue the loop, and the rest of the block may only
  jump to the name it binds.  It is threaded through every pass, printer, parser,
  delaborator and check of the backend, the surface language writes it `(joinB j […] : τ
  body rest)`, and `LakeJs.Usage` holds it to the same rule as a term-level join point
  (`Body.not_usesOk_joinPointB_of_noJump`).
* **The contification pass runs.**  `LakeJs.Contify` — which reads a `let` of a lambda
  that is only ever *called* as the join point it is — is now the last step of
  `LakeJs.Compile.optimise`, inside a loop block as well as outside one, and
  `LakeJs.OptimiseChain.optimise_chain` still says the whole pipeline is a reduction of
  the rules (the new rules being `Step.contify` and `BodyStep.contifyB`).

Measured with `lake env lean scripts/count-join-points.lean`, the corpus now compiles to
**46 join points across 29 declarations** of 1257 — bindings the emitted module never
lets escape, and which the term itself says so of.  The generated JavaScript is
unchanged, byte for byte: a join point prints as the same local arrow, and a jump as the
same call.  What changed is what the term *says*, and therefore what `LakeJs.Usage` can
hold the backend to.

What the translation itself still does is bind a shared LCNF join point with
`Body.letB`/`Term.letE` and leave the recognition to the pass; a translation that
produced the form directly would save the recognition, not change the output.

## Building a term that cannot break the discipline

`LakeJs/UsageBuild.lean` is the discipline as an *interface* rather than a check:
`WfTermAt Sg Γ m τ` is a term with the proof that it passes, and there is one builder
per constructor of `Term`, the binders asking for their condition as an argument —
`WfTermAt.lamN` for "the body reads every parameter", `WfTermAt.letE` for "the binding
shares something", `WfTermAt.loop` for "every slot is read", `WfTermAt.joinPoint` for
"the rest jumps to it", `WfTermAt.var` for "this variable is not a join point".  Each is
a decidable `Bool`, discharged by `by decide` at a closed term.

So `ƛ ƛ ♯1`, the function that ignores its parameter, has no counterpart there: the
argument `WfTermAt.lamN` asks for is `false`.  And what the interface *does* build, the
compiler accepts: `WfTermIn.usesOkDecl` is the proof, resting on
`Term.issues_eq_nil_of_usesOk` — every message the diagnosis would report is one of the
conditions the check tests.
