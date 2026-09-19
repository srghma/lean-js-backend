# Will `lean-to-js-backend SnapshotsMy/Tco07.lean` work?

*Assessment of the hypothetical: `LakeJs/FromLcnf.lean` is rewritten against the new
grammar, `.trash/LeanJs/Compile.lean` comes back as `LakeJs/Compile.lean`, `Main.lean`
is made to build, and the driver emits only the `Term` tree into
`<path>-<name>-Program.txt` — no JavaScript for now.*

*Every claim marked **[verified]** was reproduced against this tree with the toolchain it
pins (`leanprover/lean4:v4.28.0`); the commands are given so each one can be re-run.
Claims marked **[design]** are consequences of the grammar in `LakeJs/Expr.lean` and of
the plan of record, not measurements.*

---

## 0. The short answer

**`boom` is not rejected, and nothing about the `.olean`-only diet stands in the way.**

The worry in the question — "`boom` is non-terminating without its proof, and the backend
can only read `.olean`s, so it cannot see the proof" — rests on the assumption that the
backend has to *re-establish* termination. It does not, and it must not. Lean already ran
the termination proof when the module was compiled, and it left three things behind in the
`.olean`, all three of which are present for `boom` **[verified]**:

| what the front end needs | where it is | for `boom` |
|---|---|---|
| the verdict "this was elaborated by well-founded recursion" | `Lean.Elab.WF.eqnInfoExt` | `clique = #[boom]`, `declNameNonRec = boom._unary` |
| the `termination_by` **measure** | inside the packed declaration `boom._unary` | `fun x => PSigma.casesOn x fun n h => n`, i.e. `n` |
| the **body** to translate | the `saveBase` LCNF phase | a self-recursive body whose proof argument is already erased to `◾` |

The proof `h : Safe n` is exactly the thing the backend never needs. It is `Prop`-typed, so
it is erased before LCNF exists; what survives is a loop over `n` whose iteration count is
capped by the rank. The termination argument of the emitted `Term` is the grammar's own
(`Term.fix` counts down), not Lean's — so the backend never has to know *why* the
else-branch of `boom` is dead.

What *will* stop the command today is plumbing, not `boom`: the executable is not built,
`Main.lean` calls two functions that exist nowhere in the tree, and the default (no
`--decl=`) code path writes `-Expr.txt`, not `-<name>-Program.txt`. Section 4 lists all of
it.

---

## 1. What the `.olean` actually contains for `Tco07`

Build first — `lake env` runs a binary, it does not build the snapshot:

```
lake build SnapshotsMy.Tco07
```

**Recursion kind and measure [verified]:**

```
$ lake env lean --run scripts/dump-recursion-kind.lean SnapshotsMy.Tco07 boom
boom: well-founded recursion
  clique     : [boom]
  packed     : boom._unary
  measure, via WellFounded.Nat.fix:
    fun x => PSigma.casesOn x fun n h => n
  safety     : safe
  compiled   : true

$ lake env lean --run scripts/dump-wf-measure.lean SnapshotsMy.Tco07 boom
boom: WF recursion
  clique       : [boom]
  packed decl  : boom._unary
  measure, via WellFounded.Nat.fix:
    fun x => PSigma.casesOn x fun n h => n
```

The measure is exported because `Lean.Elab.WF.eqnInfoExt` is a
`MapDeclarationExtension` whose `exportEntriesFn` keeps every declaration that has a value
— which an ordinary, exposed `def` such as `boom` does.

**The body, at the `saveBase` LCNF phase [verified]** (read out of the same `.olean`, in a
process that imported the module and nothing else):

```
def boom n h : Nat :=
  let _x.1 := 1;
  let _x.2 := instDecidableEqNat _uniq.1 _uniq.3;
  cases _uniq.4 : Nat
  | Decidable.isFalse hn =>
    let _x.3 := 3;
    let _x.4 := Nat.mul _uniq.6 _uniq.1;
    let _x.5 := boom _uniq.7 ◾;      -- the proof argument, already erased
    return _uniq.8
  | Decidable.isTrue hn =>
    let _x.6 := 0;
    return _uniq.10
```

Two details matter. The body is **directly self-recursive** — the compiler does not hand
the backend a `WellFounded.fix` tower — and the proof argument is `◾`. `Safe` itself has no
LCNF at all (`no base LCNF: Safe` **[verified]**), which is the expected shape: a
`Prop`-valued definition is not code.

**The existing gate already accepts it [verified]:**

```
$ lake env lean --run scripts/dump-totality-verdict.lean SnapshotsMy.Tco07 boom
boom: accepted (Except.ok (LakeJs.Totality.RecKind.wellFounded #[`boom]))
```

(`scripts/dump-totality-verdict.lean` is added by this assessment; it runs
`LakeJs.Totality.check`, the safety / IO / recursion-kind whitelist that a rewritten
`FromLcnf` is meant to sit behind.)

So: safety gate — passes (`safe`); IO gate — passes (`Nat`); recursion-kind whitelist —
positive match on well-founded recursion. There is no path on which `boom` is refused for
being "non-terminating without its proof".

## 2. What the emitted `Term` would be

The target already exists, hand-written, in `LakeJs/Examples/WellFounded.lean`:

```lean
def boomTerm : Term Sg [] [] (.nat ⇒ .nat) :=
  .fix [Ty.nat] (Term.rankSucc (♯0)) boomBody (Term.natL 0)
```

and it is what `lakejs-expr-dump` already prints into
`LakeJs/Examples/Examples-Expr.txt`, in the format the question asks
`<path>-<name>-Program.txt` to carry, target emoji and all **[verified]**:

```
════ 🎯 boom : (fn nat nat)
fix (nat) rank { ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#) } body {
  if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 1#) then 0# else self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ 3#) ⬝ ♯0))
} exhausted { 0# }
```

Every piece of that term is mechanically derivable from what section 1 showed is in the
`.olean`: the parameter list and the branch structure from the LCNF body, the rank from
the measure (`n`, plus one — see 3.2), the `exhausted` value from the result type. The
library also *runs* it: `boomTerm_at_one : Term.runNat1 boomTerm 1 = 0` **[verified, in
the library build]**.

## 3. The four real difficulties — none of them fatal, all of them in `FromLcnf`

### 3.1 The measure is a kernel `Expr` over *packed* arguments, and it has no LCNF

`boom._unary` is not compiled: `no base LCNF for boom._unary` **[verified]**. The measure
therefore arrives as a `Lean.Expr` phrased over the packed argument
(`PSigma`, and `PSum` for a mutual clique), including the erased proof binders:

* single function, `Tco07.boom`: `fun x => PSigma.casesOn x fun n h => n`;
* mutual clique, `SnapshotsPBOPure.Tco04`: one **shared** measure over the tag
  **[verified]** —
  `fun x => PSum.casesOn x (fun _x => PSigma.casesOn _x fun n h => n.toNat) fun _x => PSigma.casesOn _x fun m h => m.toNat`.

This is excellent news for the design — the `PSum` tag is literally the "which member of
the clique is running" tag that `Term.fix` wants, and the shared rank is already shared —
but it means `FromLcnf` needs a small **`Expr` → `Term`** path for measures (beta-reduce
the `PSigma.casesOn`/`PSum.casesOn` projections against the real parameters, then
translate a first-order arithmetic expression: `n`, `n.toNat`, `a.size`, `s.utf8ByteSize -
p.byteIdx`), *or* it must synthesise an auxiliary `def` for the measure and push it through
the ordinary LCNF pipeline. It cannot simply reuse the LCNF of the packed declaration,
because there is none. **[design]**

Corner case to reject rather than mistranslate: a measure that mentions an erased binder in
a way that survives (`termination_by h.choose`) is `noncomputable` and has no runtime
counterpart; the measure translator should fail hard on it, exactly like any other
unrecognised strategy.

### 3.2 Off-by-one between "strictly decreasing measure" and "rank"

Lean guarantees the measure *strictly decreases* at each recursive call; the grammar's rank
is the number of iterations the loop is allowed. A function whose measure is `n` may still
perform one body step at `n = 0`, so the rank is `measure + 1` — which is exactly why the
hand-written `boomTerm` uses `Term.rankSucc (♯0)` and not `♯0`. **[design]**

### 3.3 The `exhausted` branch needs an inhabitant of the result type

`Term.fix` takes a fourth field, the answer when the rank runs out. For `boom` it is `0#`.
In general `FromLcnf` must produce a canonical inhabitant of the result `Ty`; the `Ty`
layer gives one for every type it admits, so this is bookkeeping rather than a design
question. **[design]**

### 3.4 The emitted term is a *sound over-approximation*, not an extensional equal

This is the honest cost of erasing the precondition, and it is already the documented
position of `TERM_PROOF_FIELDS.md`:

* on inputs Lean can actually supply — those for which `Safe n` is inhabited, i.e. `n = 1`
  — the term answers what Lean's `boom` answers (`boomTerm_at_one`);
* on inputs Lean **cannot** supply, the term still answers, because the rank cuts the loop
  off: `boomTerm_at_two : Term.runNat1 boomTerm 2 = 0` **[verified, in the library build]**,
  while Lean's `boom` cannot be applied at `2` at all and the erased call relation has no
  well-founded certificate there (`not_acc_boomStep` in `LakeJs/Examples/RankVsAcc.lean`).

So the answer to "will it work" has a second half worth stating plainly: the *Term* will be
produced and will run on every input, but for `boom` specifically the produced term is only
faithful to Lean on `n = 1`. That is unavoidable once the proof is erased, and it is the
deliberate trade: terminating by construction, pessimistic about reachability.

## 4. What actually blocks the command line today

None of these is about `boom`; all are about the driver. In rough order of size:

1. **The executable is not declared.** `lakefile.toml` has the `lean-to-js-backend`
   `lean_exe` commented out, so `./.lake/build/bin/lean-to-js-backend` does not exist
   **[verified]**.
2. **`Main.lean` calls functions that are not in the tree.** The `--decl=` path — the only
   one that writes `-<name>-Program.txt` — calls `LakeJs.Program.programOf` and
   `LakeJs.Program.javascriptOf`. A search of the whole repository finds those two names
   only in `Main.lean` and `LakeJsTest/Main.lean`; `LakeJs/Program.lean` defines
   `Program`, `Program.env`, `Program.run` and nothing else **[verified]**. They have to be
   written: `programOf` = run the gate, translate the declaration and its transitive
   callees, pretty-print the telescope; `javascriptOf` can be dropped while JavaScript is
   skipped.
3. **Restoring `Compile.lean` is not a one-file move.** `.trash/LeanJs/Compile.lean`
   imports `LakeJs.FromLcnf`, `LakeJs.Usage`, `LakeJs.LinearLet`, `LakeJs.Contify`,
   `LakeJs.DeadSlot`, `LakeJs.Scalarise`, `LakeJs.Specialise`, `LakeJs.Inline`,
   `LakeJs.TermPretty`; those in turn need `LakeJs.Rename`, `LakeJs.ExternsMeta`,
   `LakeJs.ExternTable`, `LakeJs.Config` and the `MiniAST` library — none of which is in
   this tree, and `MiniAST/` does not exist even though `lakefile.toml` still declares the
   library **[verified]**. Worse, `.trash/LeanJs/Usage.lean` would land on top of the
   *current* `LakeJs/Usage.lean`, which is a different file written against the new
   grammar. Since the hypothesis is "Term only, skip JavaScript", the cheap route is **not**
   to restore `Compile.lean` at all: a module walker over `LakeJs.Totality.check` + the
   rewritten `FromLcnf` + the existing `LakeJs.ExprPretty` (the same printer
   `lakejs-expr-dump` uses) is a few dozen lines and has no JavaScript dependencies.
4. **The file name in the question comes from the wrong code path.** `Main.lean` writes
   `<stem>-<decl>-Program.txt` only under `--decl=<name>`; the plain invocation
   `lean-to-js-backend SnapshotsMy/Tco07.lean` goes through `compileModule` and writes
   `<stem>.js` + `<stem>-Expr.txt` **[verified]**. To get
   `SnapshotsMy/Tco07-boom-Program.txt` from the plain invocation, the module path must be
   changed to enumerate the module's public declarations and write one `-Program.txt` per
   target (which is also what the "targets marked with 🎯" requirement wants).
5. **The `.olean` must exist.** The driver's `withModule` calls `importModules`; it never
   reads the `.lean` file — the path is only turned into a module name by `moduleOfPath`
   **[verified by reading `Main.lean`]**. `lake env` does not build, so
   `lake build SnapshotsMy.Tco07` must run first, or the `lean_exe` must carry
   `extraDepTargets = ["SnapshotsMy", ...]` as the old test executable did. A stale
   `.olean` silently compiles stale code.
6. **Non-exposed declarations in `module`-style files.** `eqnInfoExt`'s `exportEntriesFn`
   drops entries for declarations without a value, so a well-founded function that is not
   exposed loses its recursion-kind evidence across the module boundary and would be
   refused by the whitelist. The snapshots are plain (non-`module`) files, so this does not
   bite here, but it is the one case where "the backend can only read `.olean`s" really
   does cost information. **[verified reading `Lean/Elab/PreDefinition/WF/Eqns.lean`]**

## 5. Answers, one line each

* *Will `lake env ./.lake/build/bin/lean-to-js-backend SnapshotsMy/Tco07.lean` work?*
  Not until items 1–5 of section 4 are done; after them, yes, provided
  `lake build SnapshotsMy.Tco07` has run and the invocation uses the declaration path
  (`--decl=boom`, or a module path changed to write one `-Program.txt` per public
  declaration).
* *Will `boom` be rejected for being non-terminating without its proof?*
  No. The `.olean` records that Lean elaborated it by well-founded recursion, records the
  measure `n`, and gives a self-recursive LCNF body with the proof erased; the gate accepts
  it today **[verified]**.
* *Is the `.olean`-only diet a problem?*
  Only for non-exposed declarations of `module`-style files (4.6). For everything in the
  snapshot corpus the `.olean` carries strictly more than the `.lean` source would give a
  naive reader: the *elaborated* recursion strategy and the *packed* measure, which is
  precisely what the rank needs.
* *And the result?*
  A `Term` that terminates on every input, agrees with Lean's `boom` at `n = 1`, and
  answers `0` (the `exhausted` value) instead of diverging on the inputs Lean's `boom`
  cannot be applied to.
