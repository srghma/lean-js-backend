# One grammar, terminating by construction — assessment and plan

**Scope of this document.**  It assesses the request (drop `LakeJs/TermC.lean`; make `Term`
itself admit only structurally recursive and well-founded-recursive Lean functions, and
nothing else; keep the evaluator fuel-free; make the tree builder from LCNF a whitelist;
make the test run write a `-Expr.txt` per snapshot), reviews the design proposal quoted in
the request, and gives a plan of record.  Statements are marked **[verified]** when I
checked them against the tree or the Lean 4.28.0 sources in this sandbox, and
**[proposed]** when they are design.

Two things were changed in the tree while writing it, both recorded in §2.

**See also** `TERM_TCO04_WALKTHROUGH.md`: `Tco04.test1` worked end to end under this plan
(Lean → `Term` → the `Reduce.lean` evaluator, on an input inside and an input outside the
function's domain).  Its §9 amends F3 and adds four plan items.

**See also** `TERM_VALID_DATA_WALKTHROUGH.md`: the same exercise when the argument is
*data* — a guarded mutual pair over a mutual inductive, with a precondition that is partly
a statement about the shape of the argument (`ExamplesValidData/`).  Its §7 adds six plan
items, of which the first three (F2 is a blocker, the measure is subject to the whitelist,
F4 is on the critical path for kind W as well) change the phase-1 scope.

**See also** `TERM_PROOF_FIELDS.md`: user-defined types whose *fields* are proofs — seven
specimens, one per shape, plus seven variants of each (`ExamplesProofFields/`).  Its §5
adds three clarifications to the whitelist of §6 below (the kind-S argument must survive
erasure; a body eliminating an erased argument must be refused; field positions are
counted twice), and its §6 is a catalogue of the further data cases to support.

---

## 1. What is being asked, restated as obligations

| # | Obligation |
| :-- | :-- |
| O1 | One grammar.  `LakeJs/TermC.lean` (the second, certificate-carrying grammar `CTerm`) goes away. |
| O2 | The one grammar admits, **by construction**, exactly Lean's *structurally recursive* and *well-founded recursive* definitions.  Partial fixpoints, coinductive/inductive fixpoints, `partial`, and `unsafe` must be **unrepresentable**, not merely rejected. |
| O3 | No `IO`.  An effectful declaration must fail to translate. |
| O4 | The evaluator is total: no fuel argument, no `Option` answer, no `partial def`. |
| O5 | The LCNF→`Term` builder is a **positive whitelist**: it produces a term only for a declaration whose recursion Lean itself classified as structural or well-founded, and fails loudly otherwise. |
| O6 | `lake test` writes, per snapshot module, a `-Expr.txt` holding the term tree, public entry points flagged with a target marker, in a form that can be pasted back into an elaborator. |

O2 is the substance; O1, O4, O5 follow from it; O3 and O6 are largely independent work.

---

## 2. The state of the tree today  **[verified]**

### 2.1 What exists and builds

* The core theory builds and is `sorry`-free: `Ty`/`RTy`/`RTyWf`/`Layout`/`Schema` (types,
  layouts, strict positivity, inhabitation), `Expr` (the grammar), `Subst`/`SubstLemmas`/
  `LSubstLemmas` (renaming and substitution algebra), `Reduce` (small-step), `Progress`,
  `Reducibility`/`Fundamental`/`SN`/`TermTotal` (the logical relation and the fuel-free
  evaluator for the certified fragment), `TailShape`/`InlineSize`/`CertGen` (mechanical
  certificates for blocks whose labels are all join points), `Terminating`/`TerminatingSubst`
  (the extrinsic certificate) and `TermC` (the intrinsic grammar `CTerm`).
* **The build was red when I started.**  `LakeJs/ExternEval2.lean` still evaluated
  `.lean_nat_gcd`, whose catalogue entry in `LakeJs/LeanInitPureExterns.lean:410` is
  commented out — with a TODO that says exactly what the request says, that `Nat.gcd` must
  be treated as an ordinary well-founded recursive function rather than an extern.  Every
  module downstream of `ExternEval2` therefore failed to compile, i.e. the whole
  termination development.  I deleted the stale evaluator line; `LakeJs.TermC`,
  `LakeJs.Progress` and `LakeJs.TermTotal` now build again (36 jobs, no `sorry`).
* **`LakeJs/TermC.lean` is deleted** in this commit, per O1.  Nothing imported it (only prose
  referred to it), so the removal is inert; the file remains in git history, and
  `TERMINATING_BY_CONSTRUCTION.md` now carries a note pointing here.

### 2.2 What does not exist

`LakeJs.lean` imports `LakeJs.Compile`, `Config`, `EmitJs`, `ExternTable`, `ExternsMeta`,
`Lookup`, `Simp`, `LeanPureExtern`, `LeanImpureExtern`, `FloatDecideTests` — **none of these
files is in the tree**, so the `LakeJs` library root, the `lean-to-js-backend` executable and
`lake test` cannot build at all.  `LakeJs/Program.lean` is commented out for the same reason,
and `LakeJs/FromLcnf.lean` (1949 lines) is live code that imports four of the missing modules
and is written against a `Term` that no longer exists (`Term.loop`, `Body.cont`, `Term.jsOp`).

**Consequence for planning:** O5 and O6 are not "adjust the classifier in `FromLcnf`".  The
front end, the emitter and the test driver have to be rebuilt; `FromLcnf.lean` is a reference
document for the LCNF traversal, not a patch target.  I would move it to `.trash/` beside the
other legacy modules and write the new translator against the new grammar.

### 2.3 What the grammar can and cannot say

* `Term` has no label context; the only use of labels is `Term.block`, opening `Tail`, whose
  one binder is `Tail.label (self : Bool) body rest`: `self = false` is a join point,
  `self = true` is a loop, reduced by inlining (`Tail.lsubst0`, `Tail.loopEntry`).
* A loop is the **only** repeating construct inside a `Term`, and `LakeJs/Diverge.lean`
  exhibits `l: while (true) { continue l }` as a closed diverging term.
* `Term.proj` carries `hOne : σ.numCtors? = some 1`, and a `caseTag`/`caseT` branch **binds
  nothing**.  So a field of a value of a multi-constructor type cannot be read at all.
* `Sig` gives globals types, not bodies, and does not forbid cycles.

---

## 3. Four findings that change the design

### F1.  Half of the corpus does not recurse in tail position, and today that recursion lives in the *program*, not in the `Term`  **[verified]**

`SnapshotsPBOPure/CaseJacobs.js`, generated by the backend, is:

```js
export const renderExpr = (v0) => {
  if (v0.tag === 0) { return "Add(" + renderExpr(v0._1) + " " + renderExpr(v0._2) + ")"; }
  ...
```

a **self-calling global**, not a loop — and `LakeJsTest/JsShape.lean` knows it
(`recursiveNames`: "the places where the Lean recursion was not a tail call and so did not
become a loop").  The same holds for `cata`/`cataMap` (`RecursionSchemes01`),
`traverseFun1`/`Fun.size` (`VanLaarhovenTraversals01`) and `Nat.gcd`'s non-tail siblings.

This is decisive, and the proposal in the request misses it:

* A loop construct — Claude's `Tail.loop`, or today's `Tail.label true` — can only express
  **tail** recursion.  It cannot represent `renderExpr`.
* Worse, making every `Term` terminate **does not make a program terminate**, because
  `Term.global` may name a declaration whose body calls back.  A grammar-level guarantee that
  ignores the call graph is not the guarantee the request asks for.

So the recursion construct has to be a construct of `Term` that allows recursive calls in
**any** position, and the program must be forbidden to close a cycle through globals.  The
`while`-shaped loop then becomes an *emission* property (a `fix` all of whose self-calls are
tail calls prints as `while (true)`), not a grammar property.

### F2.  Reading a field of a multi-constructor value is not representable  **[verified]**

`Term.proj` requires a single-constructor type and branches bind nothing, yet LCNF binds the
fields in the alternative:

```
def renderExpr x.1 : String :=
  cases x.1 : String
  | Expr.add a.2 b.3 => ... renderExpr a.2 ... renderExpr b.3 ...
```

(dumped with `scripts/dump-lcnf-saveBase.lean`).  So the entire structural-on-data part of the
corpus is blocked before termination is even discussed.  The fix is the LCNF shape itself:
**alternatives bind the fields of their constructor**, i.e. `AltsT.cons` takes
`Tail Sg (fields ++ Γ) Ω τ`.  That change also hands us, for free, the syntactic fact a
structural descent check needs: inside branch `i`, the new binders *are* the immediate
sub-values of the scrutinee.

### F3.  The termination measure is not in the environment where the proposal assumes, and it is not always arithmetic  **[verified]**

* `Lean.Elab.WF.EqnInfo` (`Lean/Elab/PreDefinition/WF/Eqns.lean`) stores `declName`,
  `levelParams`, `type`, `value` (the *recursive* pre-definition body), `declNames`,
  `declNameNonRec`, `argsPacker`, `fixedParamPerms` — **no `TerminationMeasure`**.  The measure
  survives only inside the packed definition `declNameNonRec`, as the `f` of
  `invImage f inst` under the `WellFounded.fix` (`WF/Rel.lean:68`, `WF/Fix.lean:242`).  Reading
  it therefore means matching that application and unpacking `argsPacker`/`fixedParamPerms`.
* `Lean.Elab.Structural.EqnInfo` *does* store what we need for kind S: `recArgPos`.
* The relation's carrier is not always `Nat`.  Lean's default for several arguments, and for a
  mutual clique, is a **lexicographic** measure (`Prod.Lex`/`PSigma`), and no single `Nat`
  computed at entry bounds an ω²-descent.  A rank must therefore be a *list* of slots compared
  lexicographically, even if today's corpus only needs one or two.
* The measure may mention **closures and captured variables**, not just arithmetic:
  `Fusion02.toArrayLoop` has `termination_by u.measure s`, where `u.measure` is a *field of a
  structure argument*; `Tco05.go` has `arr.size - i` with `arr` captured by a `let rec`.  The
  translation of a measure is thus a translation of an arbitrary Lean expression, which the
  LCNF front end can only do for something it compiles.  The clean route is to **synthesise an
  auxiliary declaration** for the measure (`f.__rank := fun <fixed prefix> <args> => <measure>`),
  push it through the same LCNF pipeline as any other declaration, and let the rank of the `fix`
  be a call to it.
* `WF.eqnInfoExt`'s export filter drops declarations that have no exported value, so for
  imported modules the classification must degrade to inspecting the constant itself rather
  than silently treating "no info" as "not recursive".

### F4.  A structural size cannot be computed inside the language  **[verified as a circularity, proposed as a fix]**

Step 4 of the proposal ("compute `fuel0` as a generic `Ty`-indexed structural size of the
recursed-on argument") is circular: computing the size of a value of a recursive type *is* a
structural recursion, so it needs the very construct whose rank it is supposed to supply.
Nothing in `RTyWf` avoids this — strict positivity and inhabitation are checks on types, not
size functions on values.  Two honest ways out:

* **B1 — a trusted runtime primitive.**  Add a `sizeOf`-style entry to the extern catalogue,
  implemented in `runtime/` as an object walk.  The language already assumes every extern is
  total, so this costs no new kind of trust; it costs one O(size) walk at each entry to a
  structural recursion.
* **B2 — a tracked sub-value descent.**  With F2's field-binding alternatives, a recursive call
  whose argument is a binder of a `case` on the recursion subject is *syntactically* a descent.
  No runtime cost and no new trusted primitive, but the grammar must carry a small "descent
  context" recording, per variable, whether it is a strict sub-value of the subject, and the
  substitution/renaming algebra has to carry it too.

Recommendation: ship B1 first (it unblocks the corpus in phase 1), design the rank so that B2
is a second constructor of the same `Descent` type, and move the structural cases over to B2
when it lands.

---

## 4. Assessment of the proposed design, point by point

| Proposal | Verdict |
| :-- | :-- |
| Delete `TermC`, one grammar | **Adopt.**  Done in this commit. |
| One recursion constructor, `Nat.rec`-shaped, rather than separate S and W constructors | **Adopt the idea, move it from `Tail` to `Term`.**  As a `Tail` constructor it covers only tail recursion (F1). |
| The measure is a field of the construct, computed once at entry from the enclosing context | **Adopt.**  This is the right answer to "should the measure be part of `Term`?" |
| The measure is *sealed*: an iteration's rank is produced by the semantics, never named by a jump | **Adopt, and it is the key soundness idea.**  It is the same move the language already makes for labels: a label is not a value, so it cannot be smuggled; a rank is not a value either. |
| Kind S and kind W stop being a grammar distinction | **Adopt.** |
| `fuel0` for kind S = a generic structural size | **Reject as stated** (F4); use a trusted primitive or a tracked descent. |
| The rank is a single `Nat` | **Reject as stated** (F3): make it a lexicographic list of slots. |
| Mutual cliques become one loop with a tag argument and a shared rank | **Adopt** — with the caveat that the shared measure often needs a second, "which member is running" slot, which is precisely why the rank must be lexicographic. |
| `Tco07`-style dead branches need no re-derivation because `Prop`s are erased | **Adopt, with a sharper statement.**  The transcribed rank is *not* "a looser bound"; on inputs that the erased precondition excludes, the emitted function is not the Lean function at all — it stops at the rank-exhausted branch and answers with a default.  That is sound (those inputs are uncallable in Lean) but it must be written down as the faithfulness scope, not glossed over. |
| "CertGen's per-function certificate machinery disappears entirely" | **Half true.**  The extrinsic `Terminating`/`CertifiedTerm`/`CTerm` layer goes.  `LSubstLemmas`, `InlineSize`, `TailShape` and `CertGen`'s loop-free result stay: with the self-label removed, "a block of join points terminates" is exactly the theorem those modules already prove, and it becomes the block case of the new intrinsic proof instead of a certificate the user supplies. |
| `FromLcnf` as a whitelist classifier | **Adopt**, but see F3 for where the data actually lives and §2.2 for the fact that this is a rewrite. |
| "Anything from `SnapshotsPBOPartial` should now fail to translate" | **Adopt** — and note `SnapshotsPBOIO` too.  `LakeJsTest/Main.lean` already expects refusal with a reason for both, so the corpus does not have to change. |

Two further points the proposal does not cover, both mandatory:

* **The exhausted branch needs a value.**  Whatever ranks the recursion, the semantics must
  answer *something* when the rank cannot descend.  Either a canonical inhabitant per `Ty`
  (plausible: `RTy.wf` already demands inhabitation via `famAllInhabited`, but a
  `Ty.defaultTerm : (τ : Ty) → Term Sg Γ τ` still has to be defined and proved total), or a
  throwing primitive — which would give up O4.  Recommend the inhabitant.
* **Program-level acyclicity.**  Per-`Term` termination plus a cycle through `Term.global` is
  still a divergent program (F1).  The `Program` layer must check the call graph is acyclic and
  the termination theorem must be stated for the linked program.

---

## 5. Recommended design  **[proposed]**

### 5.1 Ranks

```lean
/-- One slot of a rank: how this component gets smaller at a recursive call. -/
inductive Descent where
  | counter                 -- a `Nat`; the semantics itself decrements it
  | subvalue (σ : Ty)       -- phase 2 (F4/B2): a value, replaced by a field of itself

/-- A rank: descent slots compared lexicographically, leftmost most significant. -/
abbrev Rank := List Descent
```

### 5.2 Self-reference lives in a context of its own

Exactly as labels do today: `self` is not a value, so it cannot be stored in a closure, passed
to another function or returned, and the only thing that can be done with it is to call it.

```lean
abbrev RCtx := List (Rank × List Ty × Ty)          -- the recursions in scope

inductive Term (Sg : Sig) : Ctx → RCtx → Ty → Type
  ...
  /-- A ranked recursive function.  `body` may call itself anywhere — tail position is not
      required — but only through `selfCall`, and only with a strictly smaller rank. -/
  | fix : (rk : Rank) → (ps : List Ty) →
      (body      : Term Sg (rk.tys ++ ps ++ Γ) ((rk, ps, τ) :: Ρ) τ) →
      (exhausted : Term Sg (ps ++ Γ) Ρ τ) →
      Term Sg Γ Ρ (Ty.arrows (rk.tys ++ ps) τ)
  /-- The one way to recurse.  `d` says which slot descends; the slots above it keep the
      value they have, the slot itself is decremented **by the semantics**, and only the
      slots below it are re-supplied.  There is no syntax for naming the new rank. -/
  | selfCall : (r : Ρ ∋ᵣ (rk, ps, τ)) → (d : Descends Sg Γ Ρ rk) → Spine Sg Γ Ρ ps →
      Term Sg Γ Ρ τ

/-- Which slot descends, and the values the slots below it are reset to. -/
inductive Descends (Sg) (Γ) (Ρ) : Rank → Type
  | here  : Spine Sg Γ Ρ rest.tys → Descends (d :: rest)   -- this slot −1, reset the rest
  | there : Descends rest → Descends (d :: rest)            -- this slot unchanged
```

**Why this is sealed.**  The rank is supplied once, at `fix`, from the enclosing context.  From
then on, no constructor lets a term *name* the current rank or produce a new value for the slot
it descends on: `Descends.here` says "this slot goes down by one" and says nothing else.  A
`Term` that runs forever is therefore not "rejected"; there is no way to write it down.  This is
the same discipline that already makes a jump unable to escape its block.

**Exhaustion.**  When the descending slot is `0`, the call answers with `exhausted` at the
supplied arguments.  For a faithfully translated Lean function this branch is unreachable, and
the front end fills it with the canonical inhabitant of `τ`.

### 5.3 Blocks lose their loop

`Tail.label (self : Bool)` becomes `Tail.join` (the `self = false` case).  With no self-label,
a block is a finite nest of join points and is intrinsically terminating — which is exactly the
theorem `CertGen.Tail.certified_of_loopFree` already proves, so that development is reused as
the block case rather than deleted.  `LakeJs/Diverge.lean` loses its subject matter (there is no
`loopForever` any more) and becomes a short note; `LakeJs/DivergeNeg.lean` is already a note.

### 5.4 Alternatives bind their fields

Per F2: `Alts.cons`/`AltsT.cons` take a body in `fields ++ Γ`.  `Term.proj` can keep its
`numCtors? = 1` restriction for records, and multi-constructor access goes through the case, as
in LCNF.  This is a prerequisite for the corpus and the enabler for the phase-2 descent.

### 5.5 Semantics and the theorems to prove

* `Step`: `fix` is a value; applying it to its full argument list substitutes `body`, with the
  rank slots instantiated to the evaluated rank arguments and the self-reference bound.
  `selfCall` on a rank whose descending slot is a positive literal steps to the body again with
  that slot decremented and the lower slots reset; on `0` it steps to `exhausted`.
* Rank arguments must be evaluated to literals before the first unrolling — one congruence rule.
* **SN**: extend the existing logical relation (`Reducibility`, `Fundamental`, `SN`) with a `fix`
  case proved by well-founded induction on the rank value in the lexicographic order on
  `Nat^k`; the block case is the reused loop-free result; everything else is unchanged.
* **Totality of the evaluator**: `Term.eval`/`eval_total` in `TermTotal` then hold for *all*
  closed terms, with no fragment restriction and no fuel — which is O4.
* **Program**: `Program.terminates`, from per-term SN plus acyclicity of the global call graph.
* Keep the teeth: a theorem that the translation of a `partial` declaration cannot exist, and a
  worked example that the old diverging block has no counterpart.

### 5.6 What this costs at run time

A counter slot is one integer decrement and one zero test per recursive call, plus the initial
rank computation (O(1) for arithmetic measures, O(size) if B1's `sizeOf` primitive is used).
The emitter may drop the counter when it can see the loop is a plain tail loop, at the price of
the emitted code diverging where the term would have taken the exhausted branch — so this should
be a flag, off by default.  Phase-2 sub-value descent costs nothing at run time.

### 5.7 The worked cases from the request

* **`Tco03` (`go`/`k`, mutual, `termination_by n` / `m`).**  One `fix`, `ps = [tag, n]` where the
  tag picks the member, rank `[counter]` initialised to `n`.  Each cross-call is a `selfCall`
  with the tag flipped; the erased `h : m ≥ 100` never appears (LCNF shows it as `◾`).
* **`Tco04` (`test1`/`test2` on `Int`, `termination_by n.toNat`).**  Same shape; the rank
  argument is the compiled auxiliary `fun n => n.toNat`.
* **`Tco07` (`boom`, terminating only because `h : Safe n` kills the divergent branch).**  Rank
  `[counter]` initialised to `n`.  The `3 * n` call is an ordinary `selfCall`; the grammar
  bounds it whatever Lean's reason was.  On `n = 1` — the only callable input — the answer is
  Lean's; on other inputs the term stops at `exhausted`.  That scope statement is the honest
  version of "we do not need to re-derive the contradiction".
* **`Fusion02.toArrayLoop` (`termination_by u.measure s`).**  Rank argument = a call to the
  synthesised auxiliary `toArrayLoop.__rank u s acc = u.measure s`, compiled like any other
  declaration (F3).
* **`renderExpr`, `cata`/`cataMap`, `traverseFun1`.**  Non-tail `fix` (F1): recursive calls sit
  inside `String.append` arguments.  Rank `[counter]` from B1's `sizeOf` in phase 1, or a
  `subvalue` slot with B2 in phase 2.  Emission stays a self-calling arrow, as today.
* **`Nat.gcd`.**  Ordinary well-founded function once the stale `lean_nat_gcd` extern is gone
  (§2.1); rank `[counter]` initialised to the second argument.

---

## 6. The front end as a whitelist  **[proposed, with the APIs verified]**

For each declaration, in order, and failing loudly at the first mismatch:

1. **Safety.**  `ConstantInfo`/`Declaration` safety must be `.safe`.  `partial` (an opaque
   constant with an unsafe implementation) and `unsafe` are refused here — kinds 5 and 6.
2. **Effects.**  The result type must translate to a `Ty`.  There is no `IO` former, so an
   `IO`/`EIO`/`EStateM` result fails to translate; make the failure message say *why*.  Open
   question: `Ty`'s covariant primitives include `task` and `promise`, which sit uneasily with
   "no IO" — decide whether to drop them or keep them as opaque values with no operations.
3. **Fixpoint kinds.**  Presence in `Lean.Elab.PartialFixpoint.eqnInfoExt` refuses kinds 3 and 4
   (`partial_fixpoint`, `inductive_fixpoint`, `coinductive_fixpoint`).
4. **Recursion kind, positive match only.**
   * `Lean.Elab.Structural.eqnInfoExt` present → kind S; `recArgPos` names the argument; rank =
     `subvalue` on it (phase 2) or `sizeOf` of it (phase 1).
   * `Lean.Elab.WF.eqnInfoExt` present → kind W; recover `invImage f inst` from
     `declNameNonRec`'s value, unpack with `argsPacker`/`fixedParamPerms`, and emit `f` as a
     synthesised auxiliary declaration; map the carrier to a rank (`Nat` → one slot,
     `Prod.Lex`/`PSigma` of `Nat`s → one slot each, anything else → compose with `sizeOf` or
     refuse).
   * Neither, and the declaration is not self- or mutually recursive → no `fix` at all.
   * Neither, but it *is* recursive → refuse.  Never fall through to "assume fine"; note the
     `eqnInfoExt` export filter (F3), so "no info" must be distinguished from "not recursive"
     by inspecting the constant.
5. **Mutual cliques** (`declNames`) are translated as one `fix` with a tag parameter and a
   shared rank.
6. **Globals.**  After translation, the call graph of the module must be acyclic; a cycle that
   survived means a recursion the classifier did not turn into a `fix`, and is a bug, not a
   warning.

A self-reference that is used as a *value* rather than called — `xs.map f` inside `f` — is not
representable under §5.2.  Lean accepts such definitions (its `brecOn` passes a memo table, not
the function).  Phase 1 must refuse them with a clear message; the mitigation is
specialisation/inlining of the higher-order callee at the call site, which the legacy pipeline
had (`.trash/LeanJs/Specialise.lean`).

---

## 7. `-Expr.txt` and the test run  **[proposed]**

* The dump format already exists in `scripts/dump-lcnf-saveBase.lean`, markers included
  (`════ 🎯 go` for a root, `════ 📦 Nat.decEq` for a pulled-in dependency).  Keep those markers
  for `-Expr.txt`, with 🎯 on the module's public entry points.
* The body must be the `Term` tree in *source* syntax — i.e. what the term's own pretty printer
  emits, using the notation of `LakeJs.Expr` (`ƛ`, `⬝`, `♯n`, the spine and rank sugar) — so it
  can be pasted into the elaborator.
* Milestone worth having, because it is falsifiable: a **round trip** — print a term, re-elaborate
  the printed text, and check the result is syntactically the same term.  Run it over the whole
  corpus in `lake test`.
* The refusal expectations already in `LakeJsTest/Main.lean` (partial and IO modules must be
  rejected with a reason) become the negative half of O2.

---

## 8. The corpus, and what each function becomes  **[proposed; classification from the request, files verified present]**

| File | Function(s) | Kind | Representation |
| :-- | :-- | :-- | :-- |
| `SnapshotsPBOPure/CaptureDerefRegression01` | `testEven`/`testOdd` | S (`n+1`) | one `fix`, tag + `[counter]` = `n` |
| `SnapshotsPBOPure/CaseJacobs` | `renderExpr` | S (tree) | **non-tail** `fix`, rank from `sizeOf` (ph.1) / `subvalue` (ph.2) |
| `SnapshotsPBOPure/CaseLeafTco` | `test1Fuel` | S (`n+1`) | tail `fix` → `while` |
| `SnapshotsPBOPure/Fusion02` | `toArrayLoop`, `filterMapStep` | W (`u.measure s`) | rank = synthesised auxiliary (F3) |
| `SnapshotsPBOPure/RecursionSchemes01` | `cata`/`cataMap` | S (tree, mutual) | **non-tail** merged `fix` |
| `SnapshotsPBOPure/Tco01` | `test` | S (`n+1`) | tail `fix` |
| `SnapshotsPBOPure/Tco03` | `go`/`k` | W (`n`, `m`) | merged `fix`, tag + `[counter]` |
| `SnapshotsPBOPure/Tco04` | `test1`/`test2` | W (`n.toNat`) | merged `fix`, rank auxiliary `Int.toNat` |
| `SnapshotsPBOPure/Tco05` | `span.go` | W (`arr.size - i`, inferred) | `fix`; rank auxiliary captures `arr` |
| `SnapshotsPBOPure/Tco06` | `f`/`g` | S (`fuel+1`, mutual) | merged tail `fix` |
| `SnapshotsPBOPure/VanLaarhovenTraversals01` | `traverseFun1`, `Fun.size`, `rewriteBottomUpM` | S, S, W | first two **non-tail**; third rank `t.size` |
| `SnapshotsMy/GcdEntry` | `Nat.gcd` | W | `fix`; stale extern removed (§2.1) |
| `SnapshotsMy/MutualTail` | `test1`/`test2`, `test3`/`test4`/`test5` | S | two merged tail `fix`es |
| `SnapshotsMy/StringWalk` | three `go`s | W (byte index) | `fix`, rank auxiliary |
| `SnapshotsMy/AssignSteps` | `test1`–`test4` | S (`fuel+1`) | tail `fix` |
| `SnapshotsMy/LoopEntry` | `countUp` | S (`n+1`) | tail `fix` |
| `SnapshotsMy/MutualSlots` | `walkStr`/`walkNat` | S (`n+1`) | merged tail `fix` |
| `SnapshotsMy/ScalarRepl` | `clampSum` | S (`n+1`) | tail `fix` |
| `SnapshotsMy/Tco07` | `boom` | W (`n`, dead branch) | `fix`; see §5.7 |

Note: the request's table lists `SnapshotsPBOPure/Tco06` with a link to `Tco07`; in the tree
`Tco06.lean` holds the mutual `f`/`g`, and the only `Tco07.lean` is `SnapshotsMy/Tco07.lean`
(`boom`).  `HashContainers` has no recursion, as the table says.

---

## 9. Plan of record

Phases are ordered by dependency; within a phase the items are independent.

**Phase 0 — unblock (done in this commit).**
`ExternEval2` build fix; `TermC.lean` removed; this document.

**Phase 1 — the grammar.**
1. `Alts`/`AltsT` alternatives bind their constructor's fields (F2); update `Subst`,
   `SubstLemmas`, `Reduce`, `Progress` and the examples.
2. `Tail.label self` → `Tail.join`; delete `Tail.loopEntry` and the `labelLoop` step; retire
   `Diverge.lean` to a note.
3. Add `Rank`, `Descent`, `RCtx`, `Descends`, `Term.fix`, `Term.selfCall`; thread the recursion
   context through `Subst`/`SubstLemmas` the way the label context already is.
4. `Ty.defaultTerm` — the canonical inhabitant, from `RTyWf`'s inhabitation check — for the
   exhausted branch.
*Exit check:* the grammar builds; `Tco03`, `renderExpr` and `boom` are written out **by hand** as
`Term`s and evaluated on sample inputs with `#eval`; the old diverging block is unwritable.

**Phase 2 — the metatheory.**
5. `Reduce`: rank evaluation, unrolling, exhaustion; `Progress` extended.
6. `Reducibility`/`Fundamental`/`SN`: the `fix` case by lexicographic well-founded induction on
   the rank; the block case from the reused loop-free result.
7. `TermTotal`: `Term.eval` total for every closed term, no fragment condition, no fuel (O4).
8. Delete `Terminating`, `TerminatingSubst` and the certificate plumbing; keep `LSubstLemmas`,
   `InlineSize`, `TailShape`, `CertGen`.
*Exit check:* `theorem Term.sn (t : Term Sg [] [] τ) : t.SN` with no hypothesis, `sorry`-free, and
the axiom list unchanged.

**Phase 3 — the front end.**
9. Move `FromLcnf.lean` to `.trash/`; write the new translator: LCNF traversal → `Tail`/`Term`,
   with the §6 whitelist in front of it and the measure-auxiliary synthesis of F3.
10. The runtime `sizeOf` primitive (B1) plus its extern-catalogue entry and evaluator case.
11. `Program`: acyclicity of the global call graph, and the program-level termination theorem.
*Exit check:* every function in §8 translates; every `SnapshotsPBOPartial` and `SnapshotsPBOIO`
module is refused with a reason.

**Phase 4 — output and tests.**
12. Term pretty printer + `-Expr.txt` writer with the 🎯/📦 markers; `#lean_to_lean_term` restored
    on top of it.
13. Round-trip test (print → elaborate → compare) over the corpus, wired into `lake test`.
14. Emitter: tail `fix` → `while`, non-tail `fix` → self-calling arrow; keep the rank counter by
    default.
*Exit check:* `lake test` green, snapshots regenerated, `JsShape` unchanged in intent.

**Phase 5 — optional.**
15. B2: tracked sub-value descent, replacing `sizeOf` for kind S.
16. Specialisation of higher-order callees so that a self-reference passed as a value becomes a
    direct call.

---

## 10. Risks, and the decisions I would like from you

1. **Non-tail recursion is the crux** (F1).  The plan puts recursion in `Term` as `fix` rather
   than in `Tail` as a loop.  If you would rather keep recursion tail-only, then `renderExpr`,
   `cata`/`cataMap`, `traverseFun1` and `Fun.size` must be CPS-converted or defunctionalised into
   loops with an explicit stack, which is a much larger change to the emitter and to the proofs.
2. **The exhausted branch.**  Canonical inhabitant (keeps O4) or a throwing primitive (gives up
   O4)?  I assume the inhabitant.
3. **Structural rank in phase 1.**  A trusted runtime `sizeOf` (B1) is one more total-extern
   assumption.  Acceptable, or should phase 1 wait for B2?
4. **`task`/`promise` in `Ty`** versus "no IO functions" (§6.2).
5. **Faithfulness scope.**  The translated function agrees with the Lean function on inputs that
   satisfy the erased preconditions; elsewhere it answers with the exhausted branch instead of
   diverging.  Confirm that this is the contract you want written into the theorem statements.
6. **Cost.**  One decrement and one test per recursive call, plus O(size) at entry where B1 is
   used.  Confirm this is acceptable, or that the "drop the counter" emitter flag should exist.
