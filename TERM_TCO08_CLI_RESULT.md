# `lean-to-js-backend SnapshotsMy/Tco08.lean` now works

`TERM_TCO08_CLI_ASSESSMENT.md` §4 listed seven things that stood between the command line
and `SnapshotsMy/Tco08.lean`.  All of them are done, and the command produces the file the
question asked for:

```
$ lake build lean-to-js-backend SnapshotsMy.Tco08
$ lake env ./.lake/build/bin/lean-to-js-backend SnapshotsMy/Tco08.lean
SnapshotsMy/Tco08.lean -> SnapshotsMy/Tco08-Program.txt (2 declarations, checked)
```

`SnapshotsMy/Tco08-Program.txt` is committed beside the snapshot.

## What changed

| item of §4 | what was done |
| :-- | :-- |
| 1. the executable is not declared | `lakefile.toml` declares `lean-to-js-backend` again, with `Main.lean` as its root |
| 2. `Main.lean` calls functions that are not in the tree | `Main.lean` is a new, Term-only driver: no `LakeJs.Compile`, no JavaScript |
| 3. restoring the old `Compile.lean` is not a one-file move | it was not restored; the driver is `LakeJs.Totality` + the new `LakeJs.FrontEnd` + a renderer |
| 4. `-Program.txt` came only from the `--decl=` path | the plain invocation writes `<stem>-Program.txt` for the whole module |
| 5. the `.olean` must exist | unchanged, and documented: `lake build SnapshotsMy.Tco08` first |
| 6. non-exposed declarations of `module`-style files | unchanged; `SnapshotsMy/Tco08.lean` is a plain file, so it does not bite |
| 7. the measure translator must split a lexicographic `invImage` | `LakeJs.FrontEnd` does exactly that: one ranked `Term.fix` per component |

## The new front end, in one paragraph

`LakeJs/FrontEnd.lean` reads the **`saveBase` LCNF phase** of a compiled module and builds
a term of the one grammar of `LakeJs/Expr.lean`.  It is a whitelist:

* `LakeJs.Totality` refuses `partial`, `unsafe`, `IO` and partial fixpoints before
  anything else happens, and a declaration it refuses is not translated;
* the recursion kind must be one Lean recorded as *structural* or *well-founded*;
* the `termination_by` measure is read out of the packed declaration (`invImage f inst`,
  or the `h` of `WellFounded.Nat.fix`).  A measure ordered by `Prod.instWellFoundedRelation`
  is split into its components, the parameters are partitioned so that component `i` is
  computable from the parameters of levels `≤ i`, and one `Term.fix` is emitted per
  component, ranked by that component plus one.  A measure that does not partition that
  way is refused rather than guessed at;
* a self call is emitted at the outermost level whose argument actually changed, and the
  arguments of the levels inside it are applied to the result.  That is what makes
  reaching an outer level reset the inner rank — the meaning of "lexicographic";
* the body fragment it understands is: `Nat`/`Bool`/`Int`/`String` values, `let`, join
  points (inlined at their jumps), dispatch on `Nat`, `Bool` and `Decidable`, the runtime
  functions of a small table (`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.mod`, the `Nat`
  comparisons, `Int.sub`, `Int.mul`, `Int.toNat`, `String.length`), calls of other
  declarations of the same module, and self calls.  Everything else — a local function, a
  projection, a dispatch on a user inductive, a mutual clique — is refused with a message
  naming it.  Those are the next pieces of work, not silent approximations.

## What the file contains, and why it can be trusted

`-Program.txt` has two halves.  The first is the `Term` tree of every declaration in the
notation of `LakeJs.ExprPretty`, 🎯 for a public entry point of the module and 📦 for a
declaration the translation pulled in.  The second is the *same* program as Lean source: a
`GlobalDecl` and a `Sig` per declaration, the `Term` itself, and the `Program` telescope
that ties them together — copy-pasteable into a file of this package.

Before writing the file the driver **elaborates that Lean source** against `import LakeJs`
(`--no-check` skips it).  So the file is not a rendering that happens to look like a term:
the tree in it is a term of the grammar, in which the only recursion is `Term.fix` with
its rank, and it is therefore terminating by construction.

## `ack`, as the front end emits it

```
════ 🎯 ack : (fn nat (fn nat nat))
fix (nat) rank { ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#) } body {
  fix (nat) rank { ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#) } body {
    if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then … n + 1
    else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then … self1⟨↓⟩(m - 1) ⬝ 1#
    else … self1⟨↓⟩(m - 1) ⬝ self0⟨↓⟩(n - 1)
  } exhausted { 0# }
} exhausted { ƛ 0# }
```

Two ranked recursions, `m + 1` outside and `n + 1` inside, exactly the shape
`LakeJs/Examples/Ackermann.lean` hand-wrote and proved equal to Lean's `ack`.  The one
difference is where the dispatch sits: the front end nests both `fix`es first and puts the
whole body inside, which is the uniform shape for any number of components.

The emitted term was also *run* against Lean's `ack`: `Term.runNat2 tm_ack m n = ack m n`
for every `m ∈ 0..3`, `n ∈ 0..4`.  (That is a check by evaluation of the generated term,
not a proof; the general theorem, for the hand-written term of the same shape, is
`ackTerm_eq` in `LakeJs/Examples/Ackermann.lean`.)

`ack999` translates to `@ack ⬝ 999# ⬝ 1#` with no recursion of its own, and — as §3.6 of
the assessment says — no backend will ever evaluate it.

## Other modules

The driver is not specific to Tco08.  For instance:

```
$ lake env ./.lake/build/bin/lean-to-js-backend --check SnapshotsMy/Tco07.lean
SnapshotsMy/Tco07.lean: ok (1 declarations)

$ lake env ./.lake/build/bin/lean-to-js-backend --check SnapshotsPBOPure/Tco01.lean
SnapshotsPBOPure/Tco01.lean: ok (1 declarations)

$ lake env ./.lake/build/bin/lean-to-js-backend --check SnapshotsPBOPartial/Tco02.lean
SnapshotsPBOPartial/Tco02.lean: refused by the totality gate: `test`: it is a `partial def`, …
```

`boom` of Tco07 comes out as a single `fix` ranked `n + 1`, with the divergent branch
present but bounded by the rank — the sound over-approximation the assessment predicted.
Modules whose bodies use constructs outside the fragment above report, per declaration,
which construct stopped the translation.
