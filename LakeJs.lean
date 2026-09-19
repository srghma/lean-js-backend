import LakeJs.Ty
import LakeJs.TyExamples
import LakeJs.TyPretty
import LakeJs.TySchema
import LakeJs.RTy
import LakeJs.RTyWf
import LakeJs.Schema
import LakeJs.Layout
import LakeJs.LeanPrimTy
import LakeJs.LeanPrimTyCovariant
import LakeJs.LeanPrimTyLit
import LakeJs.LeanInitPureExterns
import LakeJs.Externs
import LakeJs.ExternEval
import LakeJs.ExternEval1
import LakeJs.ExternEval2
import LakeJs.ExternEvalMisc
import LakeJs.ExternDen
import LakeJs.FloatDecide
import LakeJs.Den
import LakeJs.Expr
import LakeJs.ExprPretty
import LakeJs.Subst
import LakeJs.SubstLemmas
import LakeJs.LSubstLemmas
import LakeJs.Reduce
import LakeJs.CertGen
import LakeJs.Program
import LakeJs.Curry
import LakeJs.Usage
import LakeJs.InlineSize
import LakeJs.TailPos
import LakeJs.TailShape
import LakeJs.Fragment
import LakeJs.Progress
import LakeJs.Terminating
import LakeJs.TerminatingSubst
import LakeJs.Reducibility
import LakeJs.Fundamental
import LakeJs.Descends
import LakeJs.DescentVC
import LakeJs.DescentSimp
import LakeJs.DescentTactic
import LakeJs.FaithfulTactic
import LakeJs.SN
import LakeJs.TermTotal
import LakeJs.Diverge
import LakeJs.DivergeNeg
import LakeJs.Totality
import LakeJs.CoreModels
import LakeJs.Examples.Ops
import LakeJs.Examples.Structural
import LakeJs.Examples.WellFounded
import LakeJs.Examples.ValidData
import LakeJs.Examples.Sequences
import LakeJs.Examples.Ackermann
import LakeJs.Examples.RankVsAcc
import LakeJs.Examples.Descent
import LakeJs.Examples.DescentAuto

/-!
# `LakeJs`: one grammar, terminating by construction, with a total evaluator

This is the implementation of the plan of record of `TERM_ONE_GRAMMAR_ASSESSMENT.md`, as
amended by `TERM_TCO04_WALKTHROUGH.md`, `TERM_VALID_DATA_WALKTHROUGH.md` and
`TERM_PROOF_FIELDS.md`; `TERM_TOTAL_IMPLEMENTATION.md` says what each plan item became and
what is left.

There is exactly **one** grammar (`LakeJs.Expr`) and exactly **one** evaluator
(`LakeJs.Reduce`).  Of the six kinds of recursive definition Lean offers, the grammar can
express the first two and *cannot express* the other four:

| kind | in `Term` |
| :-- | :-- |
| structurally recursive | `Term.fix`, measured by `Term.structMeasure` |
| well-founded recursive | `Term.fix`, measured by the transcribed `termination_by` components |
| partial fixpoint | unrepresentable: recursion is `Term.fix`, and it descends on a measure |
| coinductive / inductive fixpoint | unrepresentable: no coinductive former, no unmeasured fixpoint |
| `partial` | unrepresentable, and rejected by the classifier of `LakeJs.Totality` |
| `unsafe` | the same |

`IO` is unrepresentable too: `Ty` has no `IO` former and `LakeJs.Externs` lists only pure
functions of the runtime.

| module | what it holds |
| :-- | :-- |
| `LakeJs.Ty`, `LakeJs.RTy`, `LakeJs.Schema`, `LakeJs.Layout` | the type language and the layouts a `case` and a `ctor` are checked against |
| `LakeJs.Den` | what a type denotes, and the runtime trees values live in |
| `LakeJs.Externs`, `LakeJs.ExternDen` | the pure functions of the Lean runtime, and what each one means |
| `LakeJs.Expr` | `Term`, `Spine`, `Alts`, `Tail`, `AltsT`: the one grammar, with `fix`/`selfCall` the only recursion and `join` the only label |
| `LakeJs.Reduce` | the total evaluator, and the equations of the recursion |
| `LakeJs.CertGen` | the two measure builders, and the recipes that prove a recursion faithful |
| `LakeJs.Program` | a module as a telescope of declarations, so the call graph is acyclic by construction |
| `LakeJs.TermTotal`, `LakeJs.Terminating`, `LakeJs.SN`, `LakeJs.Progress` | the guarantee, stated: every term has a value, and none of the old certificate machinery is needed to get one |
| `LakeJs.Diverge`, `LakeJs.DivergeNeg` | the terms that used to diverge, and why they cannot be written now |
| `LakeJs.Totality` | the front end's classifier: which Lean declarations are admitted, and why the others are refused |
| `LakeJs.ExprPretty`, `LakeJs.Examples.Dump` | the `Term` printer and the `-Expr.txt` writer |
| `LakeJs.Examples.*` | the worked examples, kind S and kind W, each checked against the Lean function it came from |
| `LakeJs.Examples.Ackermann` | a lexicographic recursion, as one two-component `fix`, proved equal to Lean's `ack` |
| `LakeJs.Examples.RankVsAcc` | why the recursion carries a computed measure and not Lean's `Acc`, with the erasure argument proved |
| `LakeJs.Descends`, `LakeJs.DescentVC`, `LakeJs.Examples.Descent` | the verification condition that a recursion never reaches its `stuck` branch, and it discharged on the worked examples |
| `LakeJs.DescentSimp`, `LakeJs.DescentTactic`, `LakeJs.Examples.DescentAuto` | `descent_auto`, which assembles that derivation mechanically, and the same conditions proved by it in one line each |

`LakeJs/FromLcnf.lean` is the previous front end and is **not** part of this library: it
is written against the old grammar and against modules of the JavaScript emitter that are
not in this tree.  Its job is now split in two, both of them outside this library's root
because they are meta code over Lean's own compiler:

* `LakeJs.Totality` decides which Lean declarations may be translated at all;
* `LakeJs.FrontEnd` translates the `saveBase` LCNF of a compiled module into a term of
  this grammar — one `Term.fix` per declaration, carrying the components of its
  termination measure — and the
  `lean-to-js-backend` executable (`Main.lean`) writes it out as a module's
  `<Module>Program.lean` — a Lean file that type checks, whose header comment is the
  same program as a tree.
-/
