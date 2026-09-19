# Will `lean-to-js-backend SnapshotsMy/Tco08.lean` work?

*The same assessment as `TERM_TCO07_CLI_ASSESSMENT.md`, for the new snapshot
`SnapshotsMy/Tco08.lean`:*

```lean
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

def ack999 := ack 999 1
```

*Hypothesis, as before: `LakeJs/FromLcnf.lean` is rewritten against the grammar of
`LakeJs/Expr.lean`, a Term-only driver exists, and the driver emits only the `Term` tree —
no JavaScript.*

*Every claim marked **[verified]** was reproduced against this tree with the toolchain it
pins (`leanprover/lean4:v4.28.0`); the commands are given so each one can be re-run.
Claims marked **[design]** are consequences of the grammar and of the plan of record, not
measurements.*

---

## 0. The short answer

**`ack` is not rejected, and — unlike `boom` — the term the front end should emit is not
even an approximation: it is `ack`, at every pair of arguments, and that is already proved
in this tree.**

Tco07 asked whether a function that only terminates *because of an erased proof* survives
the trip through the compiled artefacts. Tco08 asks a different and sharper question:
`ack` needs no erased proof, but it terminates on a **lexicographic** measure, and the
grammar's `Term.fix` carries exactly one `Nat` rank. Three things could have gone wrong,
and none of them does:

| worry | verdict |
|---|---|
| "the compiled module only records a `Nat` measure" | false: it records `invImage` into `Prod Nat Nat` with `Prod.instWellFoundedRelation` **[verified]** — the lexicographic structure is *in* the artefact |
| "one `Nat` rank cannot pay for a lexicographic recursion" | it cannot, *per function* — but it does not have to: the recursion is curried into **one ranked `fix` per component**, and the result is proved equal to `ack` everywhere **[verified]** |
| "a rank would have to count the recursive calls, and `ack m n` makes about `ack m n` of them" | a rank bounds the **depth** of self-calls, not their **number**; `Nat.rec` at rank `k+1` hands you the rank-`k` function and lets you call it as often as you like. That is why `m + 1` and `n + 1` suffice (§3.4) |

The genuinely new front-end work Tco08 forces is in §3.1–§3.2: a measure that lands in a
lexicographic product has to be *split*, and the parameters have to be *partitioned* so
that component `i` is computable from the parameters bound at level `i`. `ack` satisfies
that trivially; not every `termination_by` does, and the classifier must refuse the ones
that do not rather than mistranslate them.

`ack999` is a second, unrelated question — a nullary constant whose value is
astronomically large. It translates (§3.6); it will never be *run*, by any backend, in any
language, and an emitter that evaluates constants at module-initialisation time would hang
on import. That is an emitter policy question, not a `Term` question.

What still blocks the command line is the same plumbing as in Tco07 — §4.

---

## 1. What the compiled module contains for `Tco08`

Build first — `lake env` runs a binary, it does not build the snapshot:

```
lake build SnapshotsMy.Tco08
```

**Recursion kind and measure [verified]:**

```
$ lake env lean --run scripts/dump-recursion-kind.lean SnapshotsMy.Tco08 ack ack999
ack: well-founded recursion
  clique     : [ack]
  packed     : ack._unary
  measure, via invImage:
    fun x => PSigma.casesOn x fun a a_1 => { fst := a, snd := a_1 }
  safety     : safe
  compiled   : true

ack999: no recursion info recorded
  safety     : safe
  compiled   : true
```

Note what the measure *is*: the identity pairing `fun m n => (m, n)`, exactly the
`termination_by m n => (m, n)` of the source. Its interest is in the relation it is
compared with, which `scripts/dump-wf-measure.lean` does not print. This assessment adds
`scripts/dump-wf-relation.lean` for that **[verified]**:

```
$ lake env lean --run scripts/dump-wf-relation.lean SnapshotsMy.Tco08 ack
ack: WF recursion
  packed decl  : ack._unary
  measure      : fun x => PSigma.casesOn x fun a a_1 => { fst := a, snd := a_1 }
  lands in     : Prod Nat Nat
  ordered by   : Prod.instWellFoundedRelation
  single-Nat rank possible : false

$ lake env lean --run scripts/dump-wf-relation.lean SnapshotsMy.Tco07 boom
boom: WF recursion
  packed decl  : boom._unary
  no `invImage` application found (measure is a plain `Nat`)
```

That contrast is the whole difference between the two snapshots. `boom`'s measure is a
`Nat` and goes straight into a rank slot; `ack`'s is a pair ordered lexicographically and
does not.

**The body, at the `saveBase` LCNF phase [verified]** (read out of the compiled module, in
a process that imported it and nothing else):

```
$ lake env lean --run scripts/dump-lcnf-saveBase.lean SnapshotsMy.Tco08
════ 🎯 ack
def ack x.1 x.2 : Nat :=
  cases x.1 : Nat
  | Nat.zero =>
    let _x.3 := 1;
    let _x.4 := Nat.add x.2 _x.3;
    return _x.4
  | Nat.succ n.5 =>
    cases x.2 : Nat
    | Nat.zero =>
      let _x.6 := 1;
      let _x.7 := ack n.5 _x.6;
      return _x.7
    | Nat.succ n.8 =>
      let _x.9 := 1;
      let _x.10 := Nat.add n.5 _x.9;
      let _x.11 := ack _x.10 n.8;      -- the NESTED call, in argument position
      let _x.12 := ack n.5 _x.11;
      return _x.12

════ 🎯 ack999
def ack999 : Nat :=
  let _x.1 := 999;
  let _x.2 := 1;
  let _x.3 := ack _x.1 _x.2;
  return _x.3
```

Four observations, all of which matter downstream:

* the body is **directly self-recursive** and **uncurried** (arity 2) — the compiler does
  not hand the backend a `WellFounded.fix` tower, and it does not hand it the curried shape
  the two nested `fix`es want either;
* nothing is erased. There is no `◾` anywhere: `ack` has no `Prop` argument, so unlike
  `boom` nothing about it is lost in translation;
* `_x.11 := ack (n.5+1) n.8` is a **non-tail** call — its result is an argument of the next
  call. No amount of tail-call machinery reaches it;
* the packed declaration has no LCNF of its own: `ack._unary` → `-- LCNF (saveBase): not
  stored` **[verified]**, exactly as for `boom._unary`. The measure is only ever available
  as a kernel `Expr`.

**The existing gate accepts both declarations [verified]:**

```
$ lake env lean --run scripts/dump-totality-verdict.lean SnapshotsMy.Tco08
ack: accepted (Except.ok (LakeJs.Totality.RecKind.wellFounded #[`ack]))
ack999: accepted (Except.ok (LakeJs.Totality.RecKind.nonRecursive))
ack.eq_def: accepted (Except.ok (LakeJs.Totality.RecKind.nonRecursive))
ack.match_1: accepted (Except.ok (LakeJs.Totality.RecKind.nonRecursive))
```

Safety gate — passes (`safe`); IO gate — passes (`Nat`); recursion-kind whitelist —
positive match on well-founded recursion. The gate says nothing about the *shape* of the
measure; that is the measure translator's job, and it is the part that does not exist yet
(§3.1).

## 2. What the emitted `Term` is

The target already exists, hand-written and *proved*, in `LakeJs/Examples/Ackermann.lean`:

```lean
abbrev ackOuterSig : RSig := ⟨[Ty.nat], .nat ⇒ .nat⟩   -- outer: takes m, answers a function
abbrev ackInnerSig : RSig := ⟨[Ty.nat], Ty.nat⟩        -- inner: takes n, answers a number

def ackTerm : Term Sg [] [] (.nat ⇒ .nat ⇒ .nat) :=
  .fix [Ty.nat] (Term.rankSucc (♯0)) ackOuterBody (ƛ (Term.natL 0))
```

and it is what `lakejs-expr-dump` already prints into `LakeJs/Examples/Examples-Expr.txt`,
in the format the question asks a `-Expr.txt` / `-Program.txt` to carry, target emoji and
all **[verified]**:

```
════ 🎯 ack : (fn nat (fn nat nat))
fix (nat) rank { ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#) } body {
  if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ƛ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#) else fix (nat) rank { ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#) } body {
    if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then (self1⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ 1#)) ⬝ 1#) else (self1⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ 1#)) ⬝ self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#)))
  } exhausted { 0# }
} exhausted { ƛ 0# }
```

Read it as: *outer* `fix` over `m`, ranked `m + 1`, answering a function `nat ⇒ nat`; at
`m = 0` the successor function; otherwise an *inner* `fix` over `n`, ranked `n + 1`, whose
body calls `self1` (the outer recursion, at `m - 1`) and `self0` (the inner one, at
`n - 1`). Entering the outer recursion resets the inner rank — which is precisely what
"lexicographic" means.

**Faithfulness, at every input — not just the reachable ones [verified, in the library
build]:**

```lean
theorem ackTerm_implements (δ : GEnv Sg.decls) : (ackTerm (Sg := Sg)).Implements δ ackFun
theorem ackTerm_eq (m n : Nat) : Term.runNat2 ackTerm m n = ack m n
```

`lake build LakeJs` builds `LakeJs.Examples.Ackermann` (76 s) with no `sorry` in it
**[verified]**. This is the sharpest contrast with Tco07: `boomTerm` agrees with Lean's
`boom` only at `n = 1`, because the precondition that made `boom` terminate was erased and
the rank is a *looser* bound than the truth. For `ack` nothing was erased, the rank is
exact, and the agreement is unconditional.

And the term really runs **[verified]**:

```
ackTerm 2 3 = 9      ackTerm 3 1 = 13     ackTerm 3 3 = 61
ackTerm 3 5 = 253    ackTerm 3 7 = 1021
```

## 3. The real difficulties

### 3.1 The measure is lexicographic: it must be *split*, not transcribed

Tco07's recipe — "transcribe the `termination_by` expression into the rank slot" — does not
typecheck here: the rank slot is `Term … (.prim .nat)` and the measure is a `Prod Nat Nat`.
`FromLcnf` therefore needs one more step than Tco07 suggested:

1. read the `invImage` application out of the packed declaration (as
   `scripts/dump-wf-relation.lean` does);
2. recognise the relation instance as a **lexicographic product** and peel it into a list
   of component measures `[μ₀, μ₁, …]`, each an ordinary first-order expression over the
   real parameters (here `μ₀ = m`, `μ₁ = n`);
3. emit one `Term.fix` per component, outermost first, each ranked `μᵢ + 1` (§3.3), with
   the answer type of level `i` being `Ty.arrows (params of levels > i) τ`.

The peeling must be a *positive* match on the instances Lean actually uses
(`Prod.instWellFoundedRelation` and its `PSigma`/`PSum` relatives), not a fallback: an
unrecognised relation is a translation failure, in the same spirit as the recursion-kind
whitelist. **[design]**

A rank slot holding a *list* of `Nat`s compared lexicographically would be the alternative
design. It is not needed — the currying above is a front-end translation, not a language
extension — and the docstring of `LakeJs/Examples/Ackermann.lean` records that choice.

### 3.2 Currying is only possible if the parameters *partition* along the measure

The transformation of §3.1 turns an arity-2 function into a function that takes `m` and
answers a closure expecting `n`. That is sound only when component `μ₀` mentions no
parameter bound at the inner level; otherwise the outer rank cannot be computed at outer
entry. `ack` is the easy case (`μ₀ = m`, `μ₁ = n`, in argument order). Realistic hard
cases the classifier must refuse rather than guess at:

* a lexicographic measure whose first component mentions a *later* parameter
  (`termination_by (n, m)` with the arguments in the other order is fine — reorder the
  levels — but `termination_by (m + n, n)` is not: the outer rank is not a function of the
  outer parameter alone);
* a mutual clique where the measure is a `PSum` over the members *and* lexicographic
  within a member: the `PSum` tag has to become a `caseTag` dispatch inside a single shared
  `fix` (the Tco04 shape, see `TERM_TCO04_WALKTHROUGH.md`) while the lexicographic
  components become nesting — the two encodings have to compose, and nothing in this tree
  has exercised that combination yet. **[design]**

### 3.3 The nested call is not a tail call — `Tail`, join points and TCO do not apply

`ack m (ack (m + 1) n)` has a self-call in *argument* position. The `Tail` fragment of the
grammar (`LakeJs/Expr.lean`, `Tail.jmp`/`Tail.join`) is for control that leaves the block;
it has no non-tail call, and `Tail.join`'s body is deliberately typed in the *outer* label
context so that no loop can be written with it. The nested call is therefore an ordinary
`Term.selfCall` in *expression* position, which the grammar allows and which the dump above
shows (`self1⟨↓⟩(m-1) ⬝ self0⟨↓⟩(n-1)`).

Two consequences for a future JavaScript emitter, neither of them a `Term` problem: `ack`
is genuinely stack-recursive (only the `m + 1, 0` branch is a tail call), and the curried
shape allocates a closure per outer level, which Lean's own arity-2 compiled code does not.
**[design]**

### 3.4 A rank bounds recursion *depth*, not the number of calls

This is the objection that makes Ackermann look impossible, and it is worth stating why it
is not: `Term.fix`'s rank is consumed the way `Nat.rec` consumes its argument — at rank
`k + 1` the body is handed *the rank-`k` function* and may apply it any number of times.
So a rank of `m + 1` does not claim that `ack m n` performs at most `m + 1` calls; it
claims that no chain of *nested* outer self-calls is longer than `m + 1`, which is exactly
what "the first component of the measure strictly decreases" already says. The number of
calls is hyper-exponential; both ranks stay small; nothing anywhere has to compute a number
of the size of `ack m n`. **[design, and confirmed by `ackTerm_eq`, which would be false
if the ranks were ever exhausted — [verified]]**

### 3.5 `Nat` is a leaf of `Ty`, so the pattern match becomes a zero test

`Ty` has no constructor layout for `Nat`, so `cases x.1 : Nat | Nat.zero | Nat.succ n.5` of
the LCNF cannot become a `Term.caseTag`. It becomes `if m = 0 then … else …` with `m - 1`
where the LCNF binds `n.5` — which is what the dumped term does
(`if (natEq ♯0 0#) … natSub ♯0 1#`). The same rewriting is what makes the S/W distinction
evaporate for `Nat`-recursive functions: a structural match on `m + 1` and a well-founded
`termination_by m` produce the same term. **[verified against the dump; design for the
general rule]**

### 3.6 `ack999`: translatable, and unrunnable

`ack999` is a nullary constant: LCNF `let _x.3 := ack 999 1; return _x.3`, IR arity 0
**[verified]**, i.e. a CAF. It is accepted by the gate as `nonRecursive` **[verified]** and
its `Term` is trivial — `Term.global ack ⬝ 999# ⬝ 1#`, no `fix` of its own.

What is not trivial is what an emitter *does* with it. `ack 999 1` sits at level 999 of the
hyperoperation hierarchy: already `ack 4 1 = 65533`, `ack 4 2` has 19729 digits, and `ack 5 1`
is past any notation worth writing down — so:

* both the result and the cost of reaching it are out of reach, by an enormous margin. No
  representation of the value exists to be printed, so the question "how long would it
  take" never arises;
* an emitter that computes module constants **at initialisation time** would make
  *importing* the module non-terminating in practice. Lean itself does not do this eagerly
  in the interpreter — importing `SnapshotsMy.Tco08` and printing a line takes 0.7 s
  **[verified]** — because codegen emits an initialiser that the `.olean` reader never
  runs;
* representing a CAF as `Ty.lazy` (a `Term.lazyMk`/`Term.lazyForce` pair) is the obvious
  alternative, with one caveat recorded in the grammar itself: `Term.lazyMk` is documented
  as **unmemoised** — forcing it twice runs it twice — so it is a thunk, not a CAF. For
  `ack999` the difference is invisible (neither finishes); for a cheap-but-shared constant
  it is a real regression, and a memoising former would have to be added if CAF sharing is
  wanted. **[design]**

`ack999` is thus a good regression test for *emission policy* and a useless one for
*evaluation*.

### 3.7 The evaluator terminates in the logic; the host stack is a separate limit

`Term.eval` is a total function, and `ackTerm_eq` says it returns `ack m n` for every `m`,
`n`. That is a statement in Lean's logic, and it does not promise that a *host* can run it:
in the Lean interpreter, `Term.runNat2 ackTerm` succeeds up to `(3, 7) = 1021` and
segfaults on the host stack at `(3, 8)` **[verified]**, while Lean's own compiled-then-
interpreted `ack` reaches `(3, 10) = 8189` in 8.5 s and dies at `(3, 12)` **[verified]**.
The gap (a few levels) is the interpretive overhead of `Term.eval`'s frames over Lean's
own; the shape of the failure is identical, and it is the ordinary limit of any
stack-recursive Ackermann, not something the rank introduces. Kernel evaluation is stricter
still: the examples in `LakeJs/Examples/Ackermann.lean` need
`set_option maxRecDepth 100000` and `maxHeartbeats 4000000` to check `ack 3 1 = 13` by
`rfl`, and that file takes 76 s to build **[verified]**.

Worth stating plainly, because "the evaluator is terminating" invites the wrong inference:
*terminating* is a theorem about the semantics; *usable* is a property of the host.

## 4. What actually blocks the command line today

Unchanged from `TERM_TCO07_CLI_ASSESSMENT.md` §4 — none of it is about `ack`:

1. **The executable is not declared.** `lakefile.toml` has the `lean-to-js-backend`
   `lean_exe` commented out, so `./.lake/build/bin/lean-to-js-backend` does not exist
   **[verified]**.
2. **`Main.lean` calls functions that are not in the tree.** `LakeJs.Program.programOf` and
   `LakeJs.Program.javascriptOf` occur only in `Main.lean` and `LakeJsTest/Main.lean`
   **[verified]**.
3. **Restoring the old `Compile.lean` is not a one-file move**; a Term-only driver over
   `LakeJs.Totality.check` + a rewritten `FromLcnf` + `LakeJs.ExprPretty` is cheaper.
4. **The `-<name>-Program.txt` name comes from the `--decl=` path**; the plain invocation
   writes `<stem>.js` + `<stem>-Expr.txt`.
5. **The `.olean` must exist** — `lake build SnapshotsMy.Tco08` first; the driver imports
   the module and never reads the `.lean`.
6. **Non-exposed declarations of `module`-style files** lose their recursion-kind evidence
   across the module boundary. `SnapshotsMy/Tco08.lean` is a plain file, so this does not
   bite here.

Tco08 adds one item that Tco07 did not need:

7. **The measure translator must handle `invImage` into a lexicographic product** and must
   perform the currying of §3.1–§3.2, refusing a measure it cannot partition. Until it
   does, `ack` is *accepted by the gate* and *not translatable by the front end* — the one
   place where Tco08 is strictly harder than Tco07.

## 5. Answers, one line each

* *Will `lake env ./.lake/build/bin/lean-to-js-backend SnapshotsMy/Tco08.lean` work?*
  Not until items 1–5 and 7 of §4 are done; after them, yes — and the term it should
  produce already exists and is proved correct.
* *Is `ack` rejected for being lexicographically, rather than numerically, terminating?*
  No. The gate accepts it as well-founded recursion **[verified]**, and the compiled module
  carries the lexicographic structure (`invImage` into `Prod Nat Nat`,
  `Prod.instWellFoundedRelation`) that the front end needs in order to split it.
* *Does a lexicographic `termination_by` force a new rank former into the grammar?*
  No — it forces a translation: one ranked `fix` per component, outermost first. The
  grammar is unchanged, and `ackTerm` is a term in it **[verified]**.
* *Can one `Nat` rank pay for `ack`, which makes about `ack m n` recursive calls?*
  Yes, because a rank bounds nesting depth, not call count (§3.4).
* *Is the emitted term an over-approximation, as `boom`'s was?*
  No. `ack` has no erased precondition, so the term is `ack` at **every** pair of
  arguments: `ackTerm_eq (m n : Nat) : Term.runNat2 ackTerm m n = ack m n` **[verified]**.
* *And `ack999`?*
  It translates to a `Term` with no recursion of its own and is accepted **[verified]**; no
  backend will ever evaluate it, and an emitter that initialises constants eagerly would
  hang at import time rather than at use (§3.6).
