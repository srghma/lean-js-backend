module

public import LakeJs.ExprPretty
public import LakeJs.Examples.Structural
public import LakeJs.Examples.WellFounded
public import LakeJs.Examples.ValidData
public import LakeJs.Examples.Sequences
public import LakeJs.Examples.Ackermann

@[expose] public section

set_option autoImplicit false

/-!
# The `-Expr.txt` writer

Item 12 of `TERM_ONE_GRAMMAR_ASSESSMENT.md`'s phase 4: a dump, per module, of the `Term`
tree of every declaration — 🎯 for a public entry point, 📦 for a private declaration the
translation pulled in.  Running the `lakejs-expr-dump` executable writes
`LakeJs/Examples/Examples-Expr.txt`.

Every entry below is a term this library also *runs*: the example files check each one
against the Lean function it was translated from.
-/

namespace LakeJs.Expr

open LakeJs.Expr.Examples

/-- The dump of the worked examples. -/
def examplesDump : String :=
  String.intercalate "\n"
    [ prettyEntry true "sumTo" (sumToTerm (Sg := ⟨[], by decide⟩))
    , prettyEntry true "testEven" testEvenWrapper
    , prettyEntry true "testOdd" testOddWrapper
    , prettyEntry false "parity._mutual" (parityMerged (Sg := ⟨[], by decide⟩))
    , prettyEntry true "sumList" (sumListTerm (Sg := ⟨[], by decide⟩))
    , prettyEntry true "sharedTail" (sharedTailTerm (Sg := ⟨[], by decide⟩))
    , prettyEntry true "Nat.gcd" (gcdTerm (Sg := ⟨[], by decide⟩))
    , prettyEntry true "go" (tco03Go (Sg := ⟨[], by decide⟩))
    , prettyEntry true "k" (tco03K (Sg := ⟨[], by decide⟩))
    , prettyEntry false "go_k._mutual"
        (tco03Merged (Sg := ⟨[], by decide⟩) (Γ := []))
    , prettyEntry true "test1" tco04Test1
    , prettyEntry true "test2" tco04Test2
    , prettyEntry false "test1._mutual" (tco04Merged (Sg := ⟨[], by decide⟩))
    , prettyEntry true "boom" (boomTerm (Sg := ⟨[], by decide⟩))
    , prettyEntry true "Forest.len" (forestLen (Sg := ⟨[], by decide⟩))
    , prettyEntry false "sumEven._mutual" sumMerged
    , prettyEntry true "sumEven" sumEvenTerm
    , prettyEntry true "sumOdd" sumOddTerm
    , prettyEntry true "span.go" (spanTerm (Sg := ⟨[], by decide⟩))
    , prettyEntry true "stringWalk.go" (walkTerm (Sg := ⟨[], by decide⟩))
    , prettyEntry true "double.go" (doubleTerm (Sg := ⟨[], by decide⟩))
    , prettyEntry true "ack" (ackTerm (Sg := ⟨[], by decide⟩))
    ]

end LakeJs.Expr

/-- Write the dump. -/
def main : IO Unit :=
  IO.FS.writeFile "LakeJs/Examples/Examples-Expr.txt" LakeJs.Expr.examplesDump
