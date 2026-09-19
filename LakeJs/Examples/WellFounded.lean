module

public import LakeJs.Examples.Ops
public import LakeJs.Program

@[expose] public section

set_option autoImplicit false

/-!
# Worked examples, kind W: well-founded recursive Lean functions

For a well-founded recursion the measure of the `Term.fix` is the **transcribed
`termination_by` measure** — an ordinary `Term` over the real, non-erased arguments,
with nothing added to it, because nothing counts iterations: the evaluator recomputes the
measure at every self call and recurses only on a strict decrease.  `Term.measure1` builds
the one-component measure, and `Term.fix_implements_measure` is the recipe that turns
Lean's own `decreasing_by` argument into faithfulness of the term.

Four things this file is meant to show.

1. `Nat.gcd` — a well-founded recursion whose measure is an argument.  The term is proved
   to agree with Lean's `Nat.gcd` on **every** input (`gcdTerm_implements`).
2. `Tco03` — a mutual clique guarded by erased `Prop` arguments, merged into one
   `Term.fix` with a tag parameter and a shared measure.
3. `Tco04` — the clique of `TERM_TCO04_WALKTHROUGH.md`, laid out as a `Program`: the
   merged recursion is a private declaration and the two Lean names are wrappers over it,
   so a caller reaches them by name and cannot interfere with the measure.
4. `Tco07.boom` — the function that terminates *only* because an erased precondition kills
   its divergent branch.  The term is total anyway: on the one input Lean can be called
   with it gives Lean's answer, and on an input Lean has no answer for it stops at the
   `stuck` branch instead of running forever.

A `Prop` argument — `Valid1 n`, `m ≥ 100`, `Safe n` — is erased before LCNF exists, so the
front end never sees it.  What it does see is the measure, and the measure is enough: a
self call happens only when the measure descends, whatever Lean's reason for termination
was.
-/

-- Running a hundred-odd iterations of a term inside the kernel needs a deeper elaborator
-- stack than the default.
set_option maxRecDepth 100000
-- …and, for the runs that descend from a measure of nine hundred, a larger budget than
-- the default number of heartbeats.
set_option maxHeartbeats 4000000

namespace LakeJs.Expr.Examples

open LakeJs
open LakeJs.Ty
open LakeJs.Expr.Ops

variable {Sg : Sig}

/-! ## 1. `Nat.gcd`

```lean
def gcd : Nat → Nat → Nat
  | 0, y => y
  | x + 1, y => gcd (y % (x + 1)) (x + 1)
```

(`SnapshotsMy/GcdEntry.lean`; the plan treats `Nat.gcd` as an ordinary well-founded
function and ignores its `@[extern "lean_nat_gcd"]`.)  Measure: the first argument. -/

/-- `if x = 0 then y else self(y % x, x)`. -/
def gcdBody : Term Sg [Ty.nat, Ty.nat] [⟨[Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  .ite (natEq (♯0) (Term.natL 0))
    (♯1)
    (.selfCall .head (.cons (natMod (♯1) (♯0)) (.cons (♯0) .nil)))

/-- `fix (x, y) { … }`, measured by `x`. -/
def gcdTerm : Term Sg [] [] (.nat ⇒ .nat ⇒ .nat) :=
  .fix [Ty.nat, Ty.nat]  1 (Term.measure1 (♯0)) gcdBody (Term.natL 0)

/-- The Lean function, as a function of an argument environment. -/
def gcdFun (as : Env [Ty.nat, Ty.nat]) : Ty.nat.den :=
  Nat.gcd (as.get .head) (as.get (.tail .head))

/-- **Faithfulness**: the term is `Nat.gcd`, at every pair of arguments. -/
theorem gcdTerm_implements (δ : GEnv Sg.decls) :
    (gcdTerm (Sg := Sg)).Implements δ gcdFun := by
  intro args
  refine Term.fix_implements_measure (♯0) gcdBody (Term.natL 0) δ .nil .nil
    gcdFun (fun as => as.get .head) (fun as => ?_) (fun g as hg => ?_) args
  · match as with
    | .cons _ (.cons _ .nil) => rfl
  · match as with
    | .cons x (.cons y .nil) =>
      cases (x : Nat) with
      | zero =>
        show (y : Nat) = gcdFun (.cons (0 : Nat) (.cons y .nil))
        simp [gcdFun, Env.get]
      | succ k =>
        show g (.cons ((y : Nat) % (k + 1)) (.cons (k + 1 : Nat) .nil))
            = gcdFun (.cons (k + 1 : Nat) (.cons y .nil))
        rw [hg (.cons ((y : Nat) % (k + 1)) (.cons (k + 1 : Nat) .nil))
          (by exact Nat.mod_lt _ (Nat.succ_pos k))]
        show Nat.gcd ((y : Nat) % (k + 1)) (k + 1) = Nat.gcd (k + 1) y
        exact (Nat.gcd_rec (k + 1) y).symm

example : Term.runNat2 gcdTerm 12 18 = 6 := rfl
example : Term.runNat2 gcdTerm 0 7 = 7 := rfl
example : Term.runNat2 gcdTerm 270 192 = Nat.gcd 270 192 := rfl

/-! ## 2. `Tco03`: a mutual clique guarded by an erased proof

```lean
mutual
def go (n : Nat) : Nat :=
  if h1 : n = 0 then n
  else if h2 : n ≤ 100 then go (n - 1)
  else k (n - 1) (by omega)
termination_by n

def k (m : Nat) (h : m ≥ 100) : Nat :=
  if h1 : m = 100 then go (m - 1)
  else if h2 : m = 900 then 42
  else k (m - 1) (by omega)
termination_by m
end
```

`h : m ≥ 100` is a `Prop` and is erased, so the front end sees a clique of two functions
of one `Nat` each with the measure `n` / `m`.  The merged `fix` takes `(tag, x)` and is
measured by `x`; a call from one member to the other is a self call with the tag
flipped. -/

/-- The body of the merged `go`/`k`, in the context `tag :: x :: Γ`. -/
def tco03Body {Γ : Ctx} :
    Term Sg ([Ty.nat, Ty.nat] ++ Γ) [⟨[Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  .ite (natEq (♯0) (Term.natL 0))
    -- tag 0: `go x`
    (.ite (natEq (♯1) (Term.natL 0))
      (♯1)
      (.ite (natLe (♯1) (Term.natL 100))
        (.selfCall .head
          (.cons (Term.natL 0) (.cons (natSub (♯1) (Term.natL 1)) .nil)))
        (.selfCall .head
          (.cons (Term.natL 1) (.cons (natSub (♯1) (Term.natL 1)) .nil)))))
    -- tag 1: `k x`
    (.ite (natEq (♯1) (Term.natL 100))
      (.selfCall .head
        (.cons (Term.natL 0) (.cons (natSub (♯1) (Term.natL 1)) .nil)))
      (.ite (natEq (♯1) (Term.natL 900))
        (Term.natL 42)
        (.selfCall .head
          (.cons (Term.natL 1) (.cons (natSub (♯1) (Term.natL 1)) .nil)))))

/-- The merged clique, measured by `x`. -/
def tco03Merged {Γ : Ctx} : Term Sg Γ [] (.nat ⇒ .nat ⇒ .nat) :=
  .fix [Ty.nat, Ty.nat]  1 (Term.measure1 (♯1)) tco03Body (Term.natL 0)

/-- The public wrapper for `go`: tag `0`. -/
def tco03Go : Term Sg [] [] (.nat ⇒ .nat) :=
  ƛ (tco03Merged ⬝ Term.natL 0 ⬝ (♯0))

/-- The public wrapper for `k`: tag `1`. -/
def tco03K : Term Sg [] [] (.nat ⇒ .nat) :=
  ƛ (tco03Merged ⬝ Term.natL 1 ⬝ (♯0))

example : Term.runNat1 tco03Go 0 = 0 := rfl
example : Term.runNat1 tco03Go 5 = 0 := rfl
example : Term.runNat1 tco03Go 100 = 0 := rfl

/-- `go 150` walks down through `k` to `k 100`, hands over to `go 99`, and lands on `0`. -/
example : Term.runNat1 tco03Go 150 = 0 := rfl

/-- `k 900` is the one input that answers `42`. -/
example : Term.runNat1 tco03K 900 = 42 := rfl

/-- `k 901` counts down to `900` and answers `42` as well. -/
example : Term.runNat1 tco03K 901 = 42 := rfl

/-! ## 3. `Tco04`: the clique of `TERM_TCO04_WALKTHROUGH.md`, as a module

```lean
mutual
def test1 (n : Int) (h : Valid1 n) : Int :=
  if hn : n = 1 then n else test2 (n - 1) (test1_step h hn)
termination_by n.toNat

def test2 (m : Int) (h : Valid2 m) : Int :=
  if hm : m = 2 then m else test1 (m - 2) (test2_step h hm)
termination_by m.toNat
end
```

The measure is `n.toNat`, so the `fix` is measured by `Int.toNat x` — Lean's own measure,
transcribed as a call of the runtime's `lean_int_to_nat`.  The three declarations are a
`Program`: the packed recursion is private and the two public names are wrappers that
supply the tag. -/

/-- The body of the merged `test1`/`test2`, in the context `tag :: x :: []`. -/
def tco04Body : Term Sg [Ty.nat, Ty.int] [⟨[Ty.nat, Ty.int], Ty.int⟩] Ty.int :=
  .ite (natEq (♯0) (Term.natL 0))
    -- tag 0: `test1 x`
    (.ite (intEq (♯1) (Term.intL 1))
      (♯1)
      (.selfCall .head
        (.cons (Term.natL 1) (.cons (intSub (♯1) (Term.intL 1)) .nil))))
    -- tag 1: `test2 x`
    (.ite (intEq (♯1) (Term.intL 2))
      (♯1)
      (.selfCall .head
        (.cons (Term.natL 0) (.cons (intSub (♯1) (Term.intL 2)) .nil))))

/-- The packed recursion, measured by `x.toNat`. -/
def tco04Merged : Term Sg [] [] (.nat ⇒ .int ⇒ .int) :=
  .fix [Ty.nat, Ty.int]  1 (Term.measure1 (intToNat (♯1))) tco04Body (Term.intL 0)

/-- The private declaration holding the packed recursion. -/
def declTco04Merged : GlobalDecl := ⟨"test1._mutual", .nat ⇒ .int ⇒ .int⟩
/-- The public declaration `test1`. -/
def declTco04Test1 : GlobalDecl := ⟨"test1", .int ⇒ .int⟩
/-- The public declaration `test2`. -/
def declTco04Test2 : GlobalDecl := ⟨"test2", .int ⇒ .int⟩

/-- `test1`, as a wrapper that supplies tag `0`. -/
def tco04Test1 : Term ⟨[declTco04Merged], by decide⟩ [] [] (.int ⇒ .int) :=
  ƛ ((Term.global .here) ⬝ Term.natL 0 ⬝ (♯0))

/-- `test2`, as a wrapper that supplies tag `1`. -/
def tco04Test2 : Term ⟨[declTco04Test1, declTco04Merged], by decide⟩ [] [] (.int ⇒ .int) :=
  ƛ ((Term.global (.there .here)) ⬝ Term.natL 1 ⬝ (♯0))

/-- The signature of the `Tco04` module. -/
def tco04Sig : Sig := ⟨[declTco04Test2, declTco04Test1, declTco04Merged], by decide⟩

/-- The module: the packed recursion, then the two wrappers.  Each body is written
    against the declarations *before* it, so the call graph is acyclic by construction and
    the clique's cycle lives entirely inside the one `Term.fix`. -/
def tco04Program : Program tco04Sig.decls :=
  .cons declTco04Test2 (by decide) tco04Test2
    (.cons declTco04Test1 (by decide) tco04Test1
      (.cons declTco04Merged (by decide) tco04Merged .nil))

/-- Run the module's `test1`. -/
def runTco04Test1 (n : Int) : Int :=
  tco04Program.run (Sg := tco04Sig) (τ := .int ⇒ .int) (.global (.there .here)) n

/-- Run the module's `test2`. -/
def runTco04Test2 (m : Int) : Int :=
  tco04Program.run (Sg := tco04Sig) (τ := .int ⇒ .int) (.global .here) m

/-- Inside the domain of `test1` (`Valid1 7` holds): the term gives Lean's answer, `1`. -/
theorem tco04_test1_in_domain : runTco04Test1 7 = 1 := rfl

/-- `test2 6` is in the domain of `test2`, and answers `1` too. -/
theorem tco04_test2_in_domain : runTco04Test2 6 = 1 := rfl

/-- Outside the domain — Lean cannot be called at `5`, because `Valid1 5` is false — the
    term is still total: the measure stops descending and it answers the `stuck`
    default. -/
theorem tco04_test1_out_of_domain : runTco04Test1 5 = 0 := rfl

/-- The same for a negative input, whose measure `Int.toNat` is `0`. -/
theorem tco04_test1_negative : runTco04Test1 (-3) = 0 := rfl

/-! ## 4. `Tco07.boom`: terminating only because of an erased proof

```lean
def Safe (n : Nat) : Prop := n = 1

def boom (n : Nat) (h : Safe n) : Nat :=
  if hn : n = 1 then 0 else boom (3 * n) (by simp [Safe] at h; omega)
termination_by n
```

`h` is erased, so the front end sees a function that *triples* its argument.  It measures
it by `n` all the same, and the semantics stops the recursion whatever Lean's reason was:
the call `boom (3 * n)` does not descend, so it answers `stuck` instead of running. -/

/-- `if n = 1 then 0 else self(3 * n)`. -/
def boomBody : Term Sg [Ty.nat] [⟨[Ty.nat], Ty.nat⟩] Ty.nat :=
  .ite (natEq (♯0) (Term.natL 1))
    (Term.natL 0)
    (.selfCall .head (.cons (natMul (Term.natL 3) (♯0)) .nil))

/-- `fix (n) { … }`, measured by `n`. -/
def boomTerm : Term Sg [] [] (.nat ⇒ .nat) :=
  .fix [Ty.nat]  1 (Term.measure1 (♯0)) boomBody (Term.natL 0)

/-- **Inside the domain.**  `n = 1` is the only value `Safe n` admits, and there the term
    answers what Lean's `boom` answers. -/
theorem boomTerm_at_one : Term.runNat1 boomTerm 1 = 0 := rfl

/-- **Outside the domain.**  Lean's `boom` cannot be called at `2`; the erased term can,
    and it *stops*: the measure does not descend, so the `stuck` branch answers. -/
theorem boomTerm_at_two : Term.runNat1 boomTerm 2 = 0 := rfl

/-- And at an input whose divergent chain is long: still an answer, not a hang. -/
example : Term.runNat1 boomTerm 7 = 0 := rfl

end LakeJs.Expr.Examples

end
