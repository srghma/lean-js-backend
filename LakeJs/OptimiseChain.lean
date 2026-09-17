import LakeJs.Compile
import LakeJs.Reduce

/-!
# The optimiser the backend runs is a reduction of the relation

`LakeJs/Reduce.lean` writes the optimiser down as an inductive relation `Step` and proves
that each of its three passes — the simplifier, the inliner and the scalariser — only
ever produces terms reachable by those rules.  This file puts the three together and
says it of the pipeline the driver actually runs, `LakeJs.Compile.optimise`:

```lean
theorem LakeJs.OptimiseChain.optimise_chain (tbl) (t) :
    t —↠[tbl] LakeJs.Compile.optimise tbl t
```

so the JavaScript the backend prints for a declaration is printed from a term that the
*rules* relate to the term the translation produced — the one `<Module>-Expr.txt` holds.
-/

namespace LakeJs.OptimiseChain

open LakeJs
open LakeJs.Ty
open LakeJs.Expr
open LakeJs.Reduce
open LakeJs.Compile

/-- Everything `optimise` does to a declaration — simplify, inline, simplify, scalarise,
    simplify — is a reduction of the rules of `LakeJs.Reduce.Step`. -/
theorem optimise_chain {Sg : Sig} {τ : Ty} (tbl : LakeJs.Inline.Table Sg)
    (t : Term Sg [] τ) : t —↠[tbl] optimise tbl t := by
  show t —↠[tbl]
    LakeJs.Simp.Term.simpAll (LakeJs.Scalarise.scalarise
      (if tbl.isEmpty then LakeJs.Simp.Term.simpAll t
       else LakeJs.Simp.Term.simpAll
         (LakeJs.Inline.Term.inlineCalls tbl (LakeJs.Simp.Term.simpAll t))))
  refine Chain.trans ?_ (Term.simpAll_chain _)
  refine Chain.trans ?_ (Term.scalarise_chain _)
  split
  · exact Term.simpAll_chain t
  · exact ((Term.simpAll_chain t).trans (Term.inlineCalls_chain _)).trans
      (Term.simpAll_chain _)

end LakeJs.OptimiseChain
