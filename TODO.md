remove LakeJs/TermC.lean, we should have only one grammar. `Term` should be terminating by constructions (not by certificate CertGen), it should not support partial Lean functions, unsafe Lean funcitons, also it should not support IO functions


https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/ mentions six main kinds of recursive functions

```
# Structurally recursive functions
Structurally recursive functions take an argument such that the function makes recursive calls only on strict sub-components of said argument.Strictly speaking, arguments whose types are indexed families are grouped together with their indices, with the whole collection considered as a unit. The elaborator translates the recursion into uses of the argument's recursor. Because every type-correct use of a recursor is guaranteed to avoid infinite regress, this translation is evidence that the function terminates. Applications of functions defined via recursors are definitionally equal to the result of the recursion, and are typically relatively efficient inside the kernel.

# Recursion over well-founded relations
Many functions are also difficult to convert to structural recursion; for instance, a function may terminate because the difference between an array index and the size of the array decreases as the index increases, but Nat.rec isn't applicable because the index that increases is the function's argument. Here, there is a measure of termination that decreases at each recursive call, but the measure is not itself an argument to the function. In these cases, well-founded recursion can be used to define the function. Well-founded recursion is a technique for systematically transforming recursive functions with a decreasing measure into recursive functions over proofs that every sequence of reductions to the measure eventually terminates at a minimum. Applications of functions defined via well-founded recursion are not necessarily definitionally equal to their return values, but this equality can be proved as a proposition. Even when definitional equalities exist, these functions are frequently slow to compute with because they require reducing proof terms that are often very large.

# Recursive functions as partial fixpoints
The definition of a function can be understood as an equation that specifies its behavior. In certain cases, the existence of a function that satisfies this specification can be proven even when the recursive function does not necessarily terminate for all inputs. This strategy is even applicable in some cases where the function definition does not necessarily terminate for all inputs. These partial functions emerge as fixed points of these equations are called partial fixpoints.

In particular, any function whose return type is in certain monads (e.g. Option) can be defined using this strategy. Lean generates additional partial correctness theorems for these monadic functions. As with well-founded recursion, applications of functions defined as partial fixpoints are not definitionally equal to their return values, but Lean generates theorems that propositionally equate the function to its unfolding and to the reduction behavior specified in its definition.

# Coinductive and inductive predicates as fixpoints
Recursive Prop-valued functions can be defined as greatest or least fixpoints of monotone operators on complete lattices. Coinductive predicates, defined using coinductive_fixpoint or the coinductive command, describe potentially infinite behavior such as infinite sequences or bisimulation. Inductive predicates, defined using inductive_fixpoint, provide an alternative to standard inductive types that is compatible with mixed inductive-coinductive mutual blocks.

# Partial functions with nonempty codomains
For many applications, it's not important to reason about the implementation of certain functions. A recursive function might be used only as part of the implementation of proof automation steps, or it might be an ordinary program that will never be formally proved correct. In these cases, the Lean kernel does not need either definitional or propositional equalities to hold for the definition; it suffices that soundness is maintained. Functions marked partial are treated as opaque constants by the kernel and are neither unfolded nor reduced. All that is required for soundness is that their return type is inhabited. Partial functions may still be used in compiled code as usual, and they may appear in propositions and proofs; their equational theory in Lean's logic is simply very weak.

# Unsafe recursive definitions
Unsafe definitions have none of the restrictions of partial definitions. They may freely make use of general recursion, and they may use features of Lean that break assumptions about its equational theory, such as primitives for casting (unsafeCast), checking pointer equality (ptrAddrUnsafe), and observing reference counts (isExclusiveUnsafe). However, any declaration that refers to an unsafe definition must itself be marked unsafe, making it clear when logical soundness is not guaranteed. Unsafe operations can be used to replace the implementations of other functions with more efficient variants in compiled code, while the kernel still uses the original definition. The replaced function may be opaque, which results in the function name having a trivial equational theory in the logic, or it may be an ordinary function, in which case the function is used in the logic. Use this feature with care: logical soundness is not at risk, but the behavior of programs written in Lean may diverge from their verified logical models if the unsafe implementation is incorrect.
```

The Term should (by construnction) support only first 2 kinds and other 4 should be unrepresentable (!) in Term. Evaluator for Term should be terminating. The Term tree constructor that transsforms Lean's LCNF.saveBase to Term should reject all functions except "Structurally recursive functions" and "Recursion over well-founded relations" (it was defined in `LakeJs/FromLcnf.lean` previously)

Here is list of lean test files that contain at least one terminating recursive function and should be supported

**All recursive functions with S/W classification:**

### `SnapshotsPBOPure/`

| File | Recursive functions |
|---|---|
| [`CaptureDerefRegression01.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/CaptureDerefRegression01.lean) | 🟦 S `testEven` / `testOdd` (mutual, pattern on `n+1`) |
| [`CaseJacobs.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/CaseJacobs.lean) | 🟦 S `renderExpr` (pattern on `Expr` subtrees) |
| [`CaseLeafTco.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/CaseLeafTco.lean) | 🟦 S `test1Fuel` (pattern on `n+1`) |
| [`Fusion02.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/Fusion02.lean) | 🟥 W `toArrayLoop`, 🟥 W `filterMapStep` (`termination_by u.measure s`) |
| [`RecursionSchemes01.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/RecursionSchemes01.lean) | 🟦 S `cata` / `cataMap` (mutual, pattern on `FixExpr` / `ExprF FixExpr`) |
| [`Tco01.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/Tco01.lean) | 🟦 S `test` (pattern on `n+1`) |
| [`Tco03.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/Tco03.lean) | 🟥 W `go`, 🟥 W `k` (`termination_by n` / `termination_by m`, subtracts 1 without pattern match) |
| [`Tco04.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/Tco04.lean) | 🟥 W `test1` / `test2` (mutual, `termination_by n.toNat` / `m.toNat` on `Int`) |
| [`Tco05.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/Tco05.lean) | 🟥 W `go` (inner `let rec`, `i+1` bounded by `arr.size`, Lean infers well-founded) |
| [`Tco06.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/Tco07.lean) | 🟦 S `f` / `g` (mutual, pattern on `fuel+1`) |
| [`VanLaarhovenTraversals01.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsPBOPure/VanLaarhovenTraversals01.lean) | 🟦 S `traverseFun1` (pattern on `Fun`), 🟦 S `Fun.size` (pattern on `Fun`), 🟥 W `rewriteBottomUpM` (`termination_by t.size`) |

### `SnapshotsMy/`

| File | Recursive functions |
|---|---|
| [`GcdEntry.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsMy/GcdEntry.lean) | 🟥 W `Nat.gcd` (well-founded on remainder, note that we ignore `@[extern "lean_nat_gcd"]` on `Nat.gcd` and treat it as ordinary function, not primitive) |
| [`HashContainers.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsMy/HashContainers.lean) | *(none)* |
| [`MutualTail.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsMy/MutualTail.lean) | 🟦 S `test1` / `test2` (mutual, `n+1`); 🟦 S `test3` / `test4` / `test5` (mutual, `n+1`) |
| [`StringWalk.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsMy/StringWalk.lean) | 🟥 W `go` in `test1`, 🟥 W `go` in `test2` (`termination_by s.utf8ByteSize - p.byteIdx`); 🟥 W `go` in `test4` (inferred, `i+1` bounded by `s.length`) |
| [`AssignSteps.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsMy/AssignSteps.lean) | 🟦 S `test1`, `test2`, `test3`, `test4` (pattern on `fuel+1`) |
| [`LoopEntry.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsMy/LoopEntry.lean) | 🟦 S `countUp` (pattern on `n+1`) |
| [`MutualSlots.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsMy/MutualSlots.lean) | 🟦 S `walkStr` / `walkNat` (mutual, pattern on `n+1`) |
| [`ScalarRepl.lean`](file:///home/srghma/projects/lean-js-backend/SnapshotsMy/ScalarRepl.lean) | 🟦 S `clampSum` (pattern on `n+1`) |

**Legend:** 🟦 S = structurally recursive &nbsp;|&nbsp; 🟥 W = well-founded recursive

P.S. Tests runner should create -Expr.txt with a Term tree for these files (the targets are public functions and they should be marked with "target" emoji) suitable to copy paste it into a [LEAN|...] elab

Interesting case is how to support e.g. SnapshotsPBOPure/Tco04.lean

```
mutual
def test1 (n : Int) (h : Valid1 n) : Int :=
  if hn : n = 1 then
    n
  else
    test2 (n - 1) (test1_step h hn)
termination_by n.toNat
decreasing_by
  simp_wf
  grind only [Valid1]

def test2 (m : Int) (h : Valid2 m) : Int :=
  if hm : m = 2 then
    m
  else
    test1 (m - 2) (test2_step h hm)
termination_by m.toNat
decreasing_by
  simp_wf
  grind only [Valid2, = Int.max_def]
end
```

or SnapshotsPBOPure/Tco03.lean

```
mutual
def go (n : Nat) : Nat :=
  if h1 : n = 0 then n
  else if h2 : n ≤ 100 then go (n - 1)
  else k (n - 1) (by omega)
termination_by n
decreasing_by all_goals omega

def k (m : Nat) (h : m ≥ 100) : Nat :=
  if h1 : m = 100 then go (m - 1)
  else if h2 : m = 900 then 42
  else k (m - 1) (by omega)
termination_by m
decreasing_by all_goals omega
end
```

or SnapshotsMy/Tco07.lean


```lean
-- Without the proof this function triples n at every step and diverges for every
-- input.  With h : Safe n the else-branch is dead code: omega derives False from
-- h (which unfolds to n = 1) and hn (n ≠ 1), so the impossible recursive call
-- `boom (3 * n)` never executes and Lean still accepts the termination proof.

/-- Only n = 1 is a safe starting point; every other value diverges. -/
def Safe (n : Nat) : Prop := n = 1

/-- Triples its argument at every step — obviously diverges for n ≠ 1.
    The proof `h : Safe n` rules out all other inputs:
    the else-branch is unreachable, proven by contradiction. -/
def boom (n : Nat) (h : Safe n) : Nat :=
  if hn : n = 1 then
    0                              -- the one terminating case
  else
    boom (3 * n)                   -- blatant divergence: 1 → 3 → 9 → 27 → …
      (by simp [Safe] at h; omega) -- h : n = 1, hn : n ≠ 1 ⊢ False → anything
termination_by n
decreasing_by
  simp [Safe] at h  -- h : n = 1
  omega             -- n = 1 ∧ n ≠ 1 ⊢ False ⊢ 3 * n < n

example : boom 1 (by simp [Safe]) = 0 := by simp [boom]
```

there are two public mutual functions. each of them are non-terminating structurally, but they ARE terminating only for some `n` (this is why proof/"filter" `h` is added).

How our Term can support such case? E.g. `#lean_to_lean_term should output Term`, I should be able to run this term on some inputs using evaluator without fuel.
How to accomplish this? Term should use joint points and loops. There should be two constructors: one for structural recursive functions and other one for well-founded? well-foundedness measure should be come part of Term? Then if variable is supplied - the well-foundedness becomes sealed? Loops should be ranked?


Here is proposal from Claude ai on question "The Term should (by construnction) support only first 2 kinds and other 4 should be unrepresentable (!) in Term. Evaluator for Term should be terminating.".

```md
Good question — and yes, that's exactly the right move. Here's the concrete plan.

## The core idea: one constructor, not two

`Acc.rec` and `Nat.rec` are the same shape: `Acc r x` is itself an inductive type whose constructor hands you strictly-smaller `Acc` proofs, so eliminating it *is* structural recursion — just on a proof instead of on data. Lean's own `termination_by`/`decreasing_by` machinery bottoms out at exactly this: a measure expression into `Nat`, well-founded by `Nat.lt`, and `Acc` for `Nat.lt` is built by ordinary structural induction on `Nat`.

So instead of two loop constructors (structural vs. well-founded), give `Tail` **one** loop constructor that is literally `Nat.rec`-shaped, and make the well-founded *measure* a mandatory field of it — a `Term Sg Γ Ty.nat` computed once, at loop entry, from the real (non-erased) arguments. Kind S and kind W stop being a grammar distinction; they become a distinction only in *how `FromLcnf` computes that one field*. That answers your question directly:

> **Yes — the measure becomes part of `Term`. Once it is supplied (at loop entry, from the enclosing `Γ`), it is sealed: every further iteration's fuel is not re-suppliable, it is mechanically produced by destructuring the previous one. There is no syntax in the grammar for a jump to name an arbitrary "smaller" fuel — so divergence is unrepresentable, not merely disallowed.**

## The grammar change

Split `Tail.label (self : Bool)` into two constructors that replace it:

```lean
inductive Tail (Sg : Sig) : Ctx → LCtx → Ty → Type
  | ret  : Term Sg Γ τ → Tail Sg Γ Ω τ
  | jmp  : Ω ∋ₗ ps → Spine Sg Γ ps → Tail Sg Γ Ω τ
  | letT : Term Sg Γ σ → Tail Sg (σ :: Γ) Ω τ → Tail Sg Γ Ω τ
  | iteT : Term Sg Γ (.prim .bool) → Tail Sg Γ Ω τ → Tail Sg Γ Ω τ → Tail Sg Γ Ω τ
  | caseT : Term Sg Γ σ → AltsT Sg Γ Ω τ tags full → (h : …) → Tail Sg Γ Ω τ

  /-- Old `label false`, unchanged: a join point. No fuel needed, because its body
      cannot jump back to it — it cannot fail to terminate. -/
  | join : (body : Tail Sg (ps ++ Γ) Ω τ) →
           (rest : Tail Sg Γ (ps :: Ω) τ) →
           Tail Sg Γ Ω τ

  /-- The ONLY way to recurse. `fuel0` is the sealed measure, a term of the enclosing
      `Γ` — this is where kind S and kind W differ, invisibly to everything downstream.
      `zero`/`succ` is a forced `Nat.rec` shape: the label is only in scope (`Ω`) inside
      `succ`, so `zero` cannot jump back — there is no `LVar` for it to use. -/
  | loop : (ps : List Ty) →
           (fuel0 : Term Sg Γ Ty.nat) →
           (zero : Tail Sg (ps ++ Γ) Ω τ) →
           (succ : Tail Sg (ps ++ Γ) (ps :: Ω) τ) →
           (rest : Tail Sg Γ (ps :: Ω) τ) →
           Tail Sg Γ Ω τ
```

The crucial detail: **`Ω`'s entry for a loop label records only `ps` — never a `Ty.nat` slot.** So `Tail.jmp` to it, from inside `succ`, can only ever supply the real loop arguments. The predecessor fuel is *not a value the term can name* — it's threaded implicitly by the evaluator, the same way `Nat.rec`'s recursive call is never something the *user's* pattern-match body writes out, it's supplied by the eliminator. Concretely at the semantics level:

```lean
-- StepT, only new case (replaces labelLoop):
| loopEnter : StepT (.loop ps fuel0 zero succ rest) (rest.lsubst0 (Tail.loopEntry fuel0 zero succ))

-- entering the loop with fuel `k`:
def Tail.loopEntry (k : Term Sg Γ Ty.nat) (zero succ : Tail …) : Tail Sg (ps ++ Γ) Ω' τ :=
  -- case on `k`: 0 → zero;  succ pred → succ, with the (single!) label in Ω bound so that
  -- the only jump available to it is pre-filled with `pred` for the fuel and whatever the
  -- body computes for `ps` — pred is bound by the eliminator, never by the jump.
```

This is now an honest `Nat.rec` — SN is proved **once, generically**, in `LakeJs`, by induction on `fuel0`'s value, exactly the way you'd prove `Nat.rec` terminates. **CertGen's per-function certificate machinery disappears entirely** — not just for the loop-free case it already covered, but for every loop, because there is no longer an unrestricted loop to certify.

## Mutual recursion (Tco03 / Tco04 / Tco07)

A mutual pair `test1`/`test2` doesn't call itself, so it isn't directly `Nat.rec`-shaped per-function — but the *pair*, taken together, decreases one shared measure (`n.toNat` / `m.toNat`, exactly what their `termination_by` already says). Represent it as **one `Tail.loop`** whose `ps` is `Nat.nat ⊕ …`-tagged (a two-constructor sum picking "currently running test1" vs "currently running test2", each carrying its own real argument), sharing the single `fuel0`. `succ`'s body dispatches on the tag with `caseT`; a call from `test1`'s branch to `test2` is a jump back into the *same* loop label with the tag flipped and the fuel implicitly decremented — which is exactly what `decreasing_by`'s `omega`/`grind` proof already established was sound for `n.toNat`/`m.toNat`. `Tco07`'s `boom` is the degenerate one-function case of this, and its "impossible else-branch" collapses for a different reason (see below).

## Why this doesn't need to re-derive Tco07's contradiction

`h : Safe n` / `h : Valid1 n` are `Prop`-typed and already **erased before LCNF exists** — `FromLcnf` never sees them, only the erased arity. That's fine: `FromLcnf` isn't asked to reprove that the else-branch is dead. It only needs the **measure expression** (`n.toNat`, `m.toNat`), which is a plain arithmetic term over the *real*, non-erased arguments, read off Lean's `termination_by` clause before erasure. It transcribes that expression as `fuel0`, and the grammar's own `Nat.rec` shape guarantees the loop terminates regardless — even in `boom`'s case, where the "divergent" branch (`3 * n`) is represented, but it's just another `succ`-branch jump with fuel `pred`, which the loop-level SN proof bounds unconditionally. You get a *sound* representation (it terminates, provably, inside `LakeJs`, with zero trust in Lean's `omega` proof) even though it's a **looser** bound than the true one Lean derived from `h`. That's fine — you don't need the tight bound, you only need *some* correct decreasing measure, and `termination_by`'s expression, transcribed verbatim, always is one (Lean already proved it decreases along every reachable recursive call — you don't need to know *why* it does for the unreachable ones, an over-generous but still terminating loop is exactly as terminating).

## `FromLcnf`'s job, restated as a whitelist

For each recursive declaration, before LCNF/erasure:

1. **Safety gate**: `Declaration.safety ≠ .safe` ⇒ reject (`partial`, `unsafe` — kinds 5/6, gone).
2. **IO gate**: unchanged — `Ty`'s translator has no IO former, so an `IO`-returning declaration fails to translate at all.
3. **Recursion-kind gate, positive match only**:
   - Lean recorded *structural* recursion (recursor/`brecOn`) ⇒ compute `fuel0` as a generic `Ty`-indexed structural size of the recursed-on argument (definable once, by structural recursion over `Ty`'s own well-founded layout via `RTyWf` — same well-foundedness fact that already makes `Ty` itself well formed by construction).
   - Lean recorded *well-founded* recursion with a completed `decreasing_by` proof ⇒ transcribe the `termination_by` measure expression directly as `fuel0` (an ordinary `Term`, built from real arguments with ordinary externs — `Int.toNat`, `Array.size`, etc.).
   - Anything else — `partial_fixpoint` (kind 3), `coinductive_fixpoint`/`inductive_fixpoint` (kind 4), or an unrecognized future strategy — **no code path produces a `fuel0` for it**, so translation fails hard. Nothing falls through to "assume fine."

## Rollout

1. Delete `LakeJs/TermC.lean`; single grammar in `LakeJs/Expr.lean`.
2. Replace `Tail.label (self : Bool) …` with `Tail.join`/`Tail.loop` as above; update `Subst`, `Reduce`(`StepT.labelJoin`/`labelLoop` → `join`/`loopEnter`), `Progress`.
3. Write the one generic SN proof for `Tail.loop` (induction on `fuel0`'s value) — this fully replaces `LakeJs/CertGen.lean`'s loop ambitions; keep only its `LoopFree`/join-point certification for `Tail.join`-only blocks (still correct, now genuinely the *whole* uncertified-loop problem, since loops are certified by construction).
4. Add the generic `Ty`-indexed `sizeOf`-by-structure function (needs `RTyWf`) for kind S's `fuel0`.
5. Rewrite `FromLcnf.lean` as the whitelist classifier above, producing `Tail.loop`/`Tail.join` only.
6. Re-run the snapshot corpus; every S/W-marked function in your table should translate; anything from `SnapshotsPBOPartial` should now fail to translate at all (not silently admit).

If you share the actual `Ty`, `Subst`, `Reduce` sources I'll turn steps 2–4 into real patches rather than sketches.
```


write md file with assessment of the task and plan.
