# The total `Term` and its evaluator: what is implemented

This document records the implementation of the plan of record of
`TERM_ONE_GRAMMAR_ASSESSMENT.md` §9, as amended by `TERM_TCO04_WALKTHROUGH.md` §9,
`TERM_VALID_DATA_WALKTHROUGH.md` §7 and `TERM_PROOF_FIELDS.md` §5.  Everything described
here builds and is `sorry`-free; the evaluator and every theorem use only `propext`,
`Quot.sound` and `Classical.choice`.

There is **one** implementation, `LakeJs`.  Build it with `lake build LakeJs`; write the
`-Expr.txt` dump with `lake exe lakejs-expr-dump`.

---

## 1. The modules

| module | what it holds |
| :-- | :-- |
| `LakeJs/Ty.lean`, `RTy.lean`, `Schema.lean`, `Layout.lean` | the type language, the recursive-type schemas and the layouts a `ctor`, a `proj` and a `case` are checked against |
| `LakeJs/Den.lean` | the runtime trees `Data`, the denotation `Ty.den` and the canonical inhabitant `Ty.dflt` |
| `LakeJs/Externs.lean`, `ExternDen.lean`, `ExternEval*.lean` | the pure `@[extern]` catalogue of Lean's `Init`, and what each entry means |
| `LakeJs/Expr.lean` | **the one grammar**: `Term`, `Spine`, `Alts`, `Tail`, `AltsT`, with `Term.fix`/`Term.selfCall` the only recursion and `Tail.join` the only label; scopes and the signature are one typed de Bruijn family, `DeBruijnProj` |
| `LakeJs/Reduce.lean` | the **total evaluator** `Term.eval`, the iteration `Term.fixIter` and the equations of the recursion |
| `LakeJs/CertGen.lean` | the two rank builders (`Term.rankSucc`, `Term.structRank`) and the faithfulness recipes `Term.fix_implements_measure` / `Term.fix_implements_structural` |
| `LakeJs/Program.lean` | a module as a telescope of declarations, so the call graph is acyclic by construction |
| `LakeJs/TermTotal.lean`, `Terminating.lean`, `SN.lean`, `Progress.lean`, `Fragment.lean`, `Reducibility.lean`, `Fundamental.lean` | the guarantee, stated — and the record of what the old certificate machinery became now that there is nothing to certify |
| `LakeJs/Diverge.lean`, `DivergeNeg.lean` | the two terms that used to diverge, and why neither can be written |
| `LakeJs/Totality.lean` | the front end's **classifier**: the safety, IO and recursion-kind gates |
| `LakeJs/ExprPretty.lean`, `LakeJs/Examples/Dump.lean` | the `Term` printer and the `-Expr.txt` writer (🎯 public, 📦 private) |
| `LakeJs/Examples/*.lean` | the worked examples, each checked against the Lean function it came from |

---

## 2. The design, as realised

### 2.1 Recursion is one constructor, and it carries its measure

```lean
| fix : (ps : List Ty) →
    (rank      : Term Sg (ps ++ Γ) Ρ .nat) →
    (body      : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) →
    (exhausted : Term Sg (ps ++ Γ) Ρ τ) →
    Term Sg Γ Ρ (Ty.arrows ps τ)
| selfCall : (Ρ ∋ᵣ ⟨ps, τ⟩) → Spine Sg Γ Ρ ps → Term Sg Γ Ρ τ
```

* The rank is computed **once, at entry**, from the arguments and the enclosing
  environment, and from nothing else.
* The body's context is `ps ++ Γ`: the rank is invisible to the body (amendment 2 of
  `TERM_TCO04_WALKTHROUGH.md` §9).
* `RSig` records the argument types and the result type.  There is **no rank slot**, so
  `selfCall` has no syntax for naming, inspecting, restoring or raising a rank.  The
  semantics decrements it; the term cannot speak about it.  That is the seal.
* A self call may appear in **any** position, not only a tail one (finding F1).

### 2.2 The evaluator is total because it is a Lean function

`Term.eval : Term Sg Γ Ρ τ → GEnv Sg.decls → Env Γ → REnv Ρ → τ.den` is **structurally
recursive on the term**.  The object language's recursion is run by `Nat.rec` on the rank
(`Term.fixIter`): at `0` the body is not consulted, at `k + 1` it runs with the iteration
at `k` as its self-reference.  No fuel argument, no `Option`, no `partial`, no new axiom —
obligation O4, discharged by construction.  Terms therefore also reduce in the kernel, so
the example checks are `rfl`.

### 2.3 Everything else the plan asked for

* **Join points only.**  `Tail.join`'s body is typed in the *outer* label context, so it
  cannot jump back to itself.  There is no loop construct; `LakeJs/Diverge.lean` records
  what became of the term that used to be one.
* **Alternatives bind their fields** (F2), against the layout of the scrutinee's type.
* **The exhausted branch answers a value** (`Ty.dflt` exists for every type), so totality
  survives without an error monad.
* **Acyclicity by construction**: a `Program` is a telescope; a cycle through a global is
  not a program that fails a check — it is not a program.
* **The structural rank** is the size of the value's runtime tree plus one
  (`Term.structRank`), computed by an ordinary total Lean function, so it adds no trusted
  primitive.
* **No `IO`**: `Ty` has no effectful former and the extern catalogue is pure (O3).
* **Kinds 3–6 are unrepresentable** (O2): each would need an unranked fixpoint, and the
  grammar has no such constructor.  Nothing has to be checked, because nothing can be
  written.

### 2.4 The rank is the measure **plus one**

The rank counts iterations, and a chain of `m` recursive calls performs `m + 1` of them.
A front end transcribing a measure `m` emits `m + 1`, which is what `Term.rankSucc` does.

### 2.5 Scopes are one family

`Var`, `LVar` and `RVar` are abbreviations for one inductive, `DeBruijn xs x`, at the
entry types `Ty`, `List Ty` and `RSig`, and `DeBruijn` is itself
`DeBruijnProj id`: one family of typed de Bruijn indices whose index is a *projection*
`f` of the entry.  `GlobalRef` is the same family at `f := GlobalDecl.ty`, since a
reference to a declaration is indexed by the declaration's type.  See
`TERM_RANK_VS_ACC.md` §4.

---

## 3. Deliberate departures from the plan

| plan item | what was done instead, and why |
| :-- | :-- |
| Phase 2: extend `Step`/`Progress` and the logical relation with a `fix` case, then derive a fuel-free evaluator | A **denotational** evaluator, structurally recursive on the term.  It discharges O4 with no logical relation at all, and for *every* closed term rather than a certified fragment.  The modules that held the old development now record what happened to it. |
| §5.1: a rank is a lexicographic **list** of `Descent` slots | A **single counter** per `fix`.  Every function of the corpus is ranked by one `Nat`, a merged clique by a tag parameter plus one counter — and a genuinely lexicographic recursion is written as one `fix` per component, which `LakeJs/Examples/Ackermann.lean` does for `ack`, proved faithful at every pair of arguments.  A lexicographic rank slot remains a possible extension; it is not needed. |
| Phase 5: sub-value descent (B2) | Not needed for soundness — the structural size is a total Lean function, not a trusted extern — and so deferred. |

---

## 4. What each example demonstrates

| example | kind | what it is there for |
| :-- | :-- | :-- |
| `sumTo` (`Examples/Structural.lean`) | S | a **non-tail** recursion; `sumToTerm_implements` proves the term is the Lean function on every input |
| `testEven`/`testOdd` | S | a mutual clique **merged into one `fix`** with a tag, laid out as a `Program`; `parityMerged_implements` proves both members faithful |
| `sumList` | S | recursion over data: the alternatives **bind their fields**, the rank is `Term.structRank` |
| `sharedTail` | — | a block whose join point is reached from both arms of a branch |
| `Nat.gcd` (`Examples/WellFounded.lean`) | W | `gcdTerm_implements`: the term is `Nat.gcd`, on every input |
| `Tco03` `go`/`k` | W | a clique guarded by an erased `Prop`, merged, shared rank |
| `Tco04` `test1`/`test2` | W | the walkthrough's clique as a `Program`, rank `x.toNat + 1`; inside the domain it answers Lean's `1`, outside it (`5`, `-3`) it **stops** at the exhausted branch |
| `Tco07.boom` | W | terminating in Lean only because an erased proof kills the divergent branch; the term answers at inputs Lean's function cannot be applied to |
| `Forest.len`, `sumEven`/`sumOdd` (`Examples/ValidData.lean`) | S, W | a clique whose **rank is a call to another declaration** — the measure is subject to the classifier, and the telescope makes a circular measure impossible |
| `span`, `stringWalk`, `double` (`Examples/Sequences.lean`) | W | index walks over an array and a string, measure `size - i`; `walkTerm_implements` proves the string walk faithful on every input |
| `ack` (`Examples/Ackermann.lean`) | W | a **lexicographic** measure, as two nested ranked recursions; `ackTerm_eq` proves the term is Lean's `ack` at every pair of arguments |
| `boomStep` (`Examples/RankVsAcc.lean`) | — | why the recursion carries a rank and not an `Acc`: `not_acc_boomStep` proves the erased `boom` has no well-founded certificate, while the ranked term still answers |

`LakeJs/Examples/Examples-Expr.txt` is the dump of all of them, 🎯 for a public entry point
and 📦 for a private one.

### The faithfulness scope, written down

For a function whose totality in Lean rests on an erased precondition, the term agrees with
the Lean function on the inputs the precondition admits, and answers the exhausted branch
on the others.  It never diverges.  That is stated per example rather than left implicit.

---

## 5. What is left

1. **The LCNF-to-`Term` translation.**  `LakeJs/Totality.lean` is the classifier — the
   safety, IO and recursion-kind gates, with `recKind?` a positive whitelist of the two
   admitted strategies — and it builds.  The translation proper is not in this tree:
   `LakeJs/FromLcnf.lean` is the previous one, written against the old grammar and against
   emitter modules (`LakeJs.Compile`, `EmitJs`, `Lookup`, `Simp`, `ExternTable`) that are
   not here, so it is kept but not built.  What a new one needs: the measure extractor of
   `TERM_TCO04_WALKTHROUGH.md` §1, the `Ty`-from-schema mapping, the tag-merging of a
   mutual clique, and the per-component currying of a lexicographic measure.
2. **A rank slot ordered lexicographically**, if a lexicographic measure is ever to be
   transcribed verbatim rather than curried.
3. **The emitter**: a tail `fix` prints as `while`, a non-tail one as a self-calling
   arrow; the counter need not be emitted at all (`TERM_RANK_VS_ACC.md` §2).
4. **A parser for the dump**, so that the round-trip milestone of the assessment §7 can run
   over the corpus.  The printer prints an extern by its type rather than by its runtime
   name, because the name table belongs to the emitter; a round trip needs that table.
