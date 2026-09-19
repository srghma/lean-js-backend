# The snapshot corpus as `Term` programs: what is generated, and what is refused

`lean-to-js-backend` reads the compiled module (`saveBase` LCNF), translates every
declaration it admits into a term of the one grammar of `LakeJs.Expr`, and writes
`<Module>Program.lean` beside the module: the `Term` tree of every declaration as a
header comment (🎯 a public entry point, 📦 a declaration the translation pulled in),
followed by the same program as Lean source — a `Sig`, one `Term` per declaration and the
`Program` telescope.  The driver **elaborates** the file it is about to write, so every
`…Program.lean` in the tree type checks against `import LakeJs`; since the only recursion
of the grammar is `Term.fix`, which carries the rank it was translated with, each of them
is terminating by construction.

```
lake build SnapshotsPBOPure.CaseLeafTco
lake env ./.lake/build/bin/lean-to-js-backend SnapshotsPBOPure/CaseLeafTco.lean
#   SnapshotsPBOPure/CaseLeafTco.lean -> SnapshotsPBOPure/CaseLeafTcoProgram.lean (5 declarations, checked)
```

`scripts/corpus-modules.txt` lists the modules of the requested corpus; the driver takes
them all at once.

## Coverage of the requested corpus

🟦 S = structurally recursive, 🟥 W = well-founded recursive (the classification of the
request).  "In the program" means the function has a `Term` of its own in the generated
`…Program.lean`.

### `SnapshotsPBOPure/`

| File | declarations written | recursive function | in the program |
| :-- | --: | :-- | :-- |
| `CaptureDerefRegression01.lean` | 8 | 🟦 S `testEven` / `testOdd` | ✅ one merged ranked recursion, plus an entry point per member |
| `CaseJacobs.lean` | 4 | 🟦 S `renderExpr` | ✅ ranked by the structural size of the `Expr` |
| `CaseLeafTco.lean` | 5 | 🟦 S `test1Fuel` | ✅ with `Array.back?` and `Array.append` compiled at `Int` |
| `Fusion02.lean` | 1 | 🟥 W `toArrayLoop`, 🟥 W `filterMapStep` | ❌ a stream carries its own *state type* (see below); `dropPrefix1` and the string primitives it is built from are written out |
| `RecursionSchemes01.lean` | 7 | 🟦 S `cata` / `cataMap` | ✅ compiled at `Int`, as one merged ranked recursion |
| `Tco01.lean` | 1 | 🟦 S `test` | ✅ |
| `Tco03.lean` | 3 | 🟥 W `go`, 🟥 W `k` | ✅ one merged ranked recursion for the clique |
| `Tco04.lean` | 3 | 🟥 W `test1` / `test2` (on `Int`) | ✅ ranked by the transcribed `n.toNat` / `m.toNat` |
| `Tco05.lean` | 2 | 🟥 W `go` (inner `let rec`) | ✅ as `span.go` |
| `Tco06.lean` | 3 | 🟦 S `f` / `g` | ✅ one merged ranked recursion |
| `VanLaarhovenTraversals01.lean` | 0 | 🟦 S `traverseFun1`, 🟦 S `Fun.size`, 🟥 W `rewriteBottomUpM` | ❌ `Fun` has no values (see below) |

### `SnapshotsMy/`

| File | declarations written | recursive function | in the program |
| :-- | --: | :-- | :-- |
| `GcdEntry.lean` | 3 | 🟥 W `Nat.gcd` | ✅ compiled from its Lean body, ranked by `m + 1`; the `@[extern]` implementation is ignored |
| `HashContainers.lean` | 0 | *(none)* | — the module is `Std.HashMap`/`Std.HashSet` code, which the type language does not model |
| `MutualTail.lean` | 7 | 🟦 S `test1` / `test2`; 🟦 S `test3` / `test4` / `test5` | ✅ two merged ranked recursions |
| `StringWalk.lean` | 11 | 🟥 W `go` in `test1`, `test2`, `test4`; 🟥 W the range loop of `test3` | ✅ all four, ranked by `s.utf8ByteSize - p` / `s.length - i` / `range.stop - i` |
| `AssignSteps.lean` | 5 | 🟦 S `test1`, `test2`, `test3`, `test4` | ✅ (`test3` calls `Nat.gcd`, which is pulled in) |
| `LoopEntry.lean` | 2 | 🟦 S `countUp` | ✅ (`main`, `printAll` are refused by the totality gate: they are `IO`) |
| `MutualSlots.lean` | 3 | 🟦 S `walkStr` / `walkNat` | ✅ one merged ranked recursion |
| `ScalarRepl.lean` | 12 | 🟦 S `clampSum`; 🟥 W the range loops of `test1` and `test2` | ✅ (`clampSum` as the private `…0.clampSum`; each `for` loop as the range loop the compiler specialized, ranked by `range.stop - i`) |

`SnapshotsMy/Tco07.lean`, `Tco08.lean` and `Tco09.lean` — the earlier snapshots — are
regenerated with the same front end and are unchanged in content.

## What the front end gained in this round

* **A polymorphic declaration is compiled at the types its callers use.**  The type
  language is monomorphic, so a polymorphic declaration has no type of its own; what has
  one is the declaration *at an instantiation* of its type parameters.  The front end
  reads the instantiation off the call — the LCNF types of a call are concrete — and
  translates the declaration once per instantiation, under the name the types are part of:
  `Array.back? @ Int`, `cata @ Int`.  The body of the specialization is the body of the
  declaration with its type parameters standing for those types.
* **`Array.append` is compiled from a Lean-source model.**  Lean replaces the body of
  `Array.append` by a specialization of `Array.foldlMUnsafe.fold`, an `unsafe` walk over
  `USize` with no termination measure.  `LakeJs/CoreModels.lean` now holds the two
  definitions the source says `Array.append` is — `arrayAppendFrom`, well-founded on the
  number of elements left, and `arrayAppend` — with `arrayAppend_eq`, the proof that the
  model really is `Array.append`.  `Array.mkEmpty` became a call of the runtime.
* **A nested newtype is erased.**  `structure FixExpr where unFix : ExprF FixExpr` is the
  `ExprF` tree it wraps: building it, reading it and matching on it are the identity, and
  a field of type `FixExpr` inside `ExprF FixExpr` is an occurrence of the type itself, so
  the pair becomes one recursive tagged union.
* **A mutual clique whose members answer with different types.**  `cata` answers with an
  `α` and `cataMap` with an `ExprF α`.  The merged recursion is one recursion, so it has
  one result type: the tagged union of the members' types.  Each member's body tags its
  answer, and a call of a member reads its own summand back out, so nothing outside the
  clique sees the union.  The rank of a structural clique is the measure times the number
  of members, because a call from one member to another need not descend (`cata` hands its
  argument to `cataMap` unchanged) while a chain of such calls cannot enter the same member
  twice.
* **A local function is an abstraction.**  An LCNF `fun` — the algebra `eval ∘ bump` that
  `RecursionSchemes01.test2` hands to `cata`, the closures of
  `CaptureDerefRegression01` — is bound to a name and translated as a `Term` abstraction.
* **The binders of a `termination_by` measure are matched with the parameters by name.**
  Lean writes the measure against the binders of the *packed* function, whose fixed prefix
  comes first, whatever position those parameters have in the function; matching by
  position alone transcribed the wrong parameter into the rank.  The position of a
  structural recursion likewise counts the erased parameters, so it is mapped through them.
* **A `for` loop over a range is compiled.**  Lean compiles `for i in [0:n] do …` by
  *specializing* its own range loop at the body of the function: the result,
  `Std.Legacy.Range.forIn'.loop._at_.test1.spec_0`, has a compiled body but **no
  declaration** — no `ConstantInfo`, no type, no equation info of its own.  The front end
  now reads its type off LCNF, and takes the recursion it has from the declaration it was
  specialized from, whose `termination_by` measure is `range.stop - i`.  A specialization
  does not take the same parameters as its origin — what the caller fixed (the monad
  instance, the loop body) is gone, and what the caller captured is added in front — so
  the binders of the measure are matched with the parameters by name alone, and a measure
  that mentions a binder the specialization does not have is refused.  Reading
  `range.stop` needed one more thing: a **structure field in a measure**, mapped to the
  slot the field has once the `Prop`-valued fields are dropped.
* **`String.startsWith` and `String.extract`.**  Both are built on primitives the runtime
  catalogue already lists (`lean_string_memcmp`, `lean_string_utf8_extract`), which the
  front-end table now names; their byte positions are held as the byte index they are, the
  way `lean_string_decode_char` already took one.  A `Char` literal — which LCNF stores as
  a `UInt32` — is read as the code point it is.

## Running the generated terms

These run the emitted terms and compare them with the Lean functions they came from.  A
`Term` has no fuel argument, so running one is an ordinary total Lean computation; what the
checks add is that the rank the front end chose is *enough*, so no recursion is cut short.

| Check | what it runs |
| :-- | :-- |
| `SnapshotsPBOPure/CaseLeafTcoCheck.lean` | `Array.append @ Int`, `Array.back? @ Int` and `test1Fuel`, at every fuel up to 6 |
| `SnapshotsPBOPure/RecursionSchemes01Check.lean` | `cata @ Int`, `test1` and `test2` on trees up to five levels deep |
| `SnapshotsPBOPure/CaseJacobsCheck.lean` | `renderExpr` and `test1` on trees that take every branch |
| `SnapshotsPBOPure/CaptureDerefRegression01Check.lean` | `test1`, `test2`, `test3` and the merged `testEven` / `testOdd` |
| `SnapshotsMy/GcdEntryCheck.lean` | `Nat.gcd` over a square of arguments |
| `SnapshotsMy/StringWalkCheck.lean` | the three string walks and the `for` loop of `test3`, over ASCII and multi-byte strings |
| `SnapshotsMy/ScalarReplCheck.lean` | the two `for` loops of `test1` / `test2`, and `test3`, `test5`, `test6` |
| `SnapshotsMy/Tco09Check.lean` | the Ackermann/hyper/McCarthy snapshots |

## Why the two remaining modules are refused

Neither is a gap in the translation; each is a statement about the type language
`LakeJs.Ty`, which is monomorphic, first order in its data, and has a canonical value for
every type.

* **`Fusion02`: a stream carries its own state type.**  `structure Unfold (α : Type) where
  State : Type; seed : State; step : State → Option (State × α); …` has a *field whose
  value is a type*, and the type of the next field depends on it.  `Ty` has no such
  former, so `Unfold α` is not a type of the language at any instantiation, and neither
  `toArrayLoop` nor `filterMapStep` — which take a `u : Unfold α` and a `u.State` — has a
  type there.  The only monomorphic caller, `test`, builds its stream with local functions
  whose argument type LCNF has already erased to `lcAny` (that is the state type again),
  so nothing can be read off it either.
* **`VanLaarhovenTraversals01`: an empty type.**  Every constructor of
  `inductive Fun | Abs : String → Fun → Fun | App : Fun → Fun → Fun` mentions `Fun`, so
  `Fun` has no values at all.  Every type of the language has a canonical value — it is
  what an exhausted rank and an unreachable branch answer with, and it is what keeps the
  evaluator total without an error monad — so a type with no values is not a `Ty`
  (`LakeJs.RTyWf`), and `Fun.size`, `traverseFun1` and `rewriteBottomUpM` are functions of
  it.  `traverseFun1` and `rewriteBottomUpM` are polymorphic in an applicative/monad
  besides, which is a type *constructor* parameter rather than a type parameter, so there
  is no instantiation to compile them at either.
* **`HashContainers`: the hash containers themselves.**  A `Std.HashMap` is a polymorphic
  structure of arrays of buckets; nothing in it is within the type language.

## What the header of a generated file says

The header of a `…Program.lean` keeps three kinds of declaration apart, and the third
list is the one that has to stay empty.

* `refused by the totality gate:` — a `partial def`, an `unsafe def`, an `IO` function or
  a partial fixpoint.  `LakeJs.Totality` refuses these on purpose: the grammar has no
  construct for them.
* `outside the language:` — the declaration is not a program of `LakeJs.Ty` at all.  Its
  type, or the type of one of its parameters, has no counterpart there (a `Repr`, a
  `Sort`-valued motive, a hash container, a type with no values), or it is polymorphic and
  no call in the module says at which types to compile it.  What calls such a declaration
  is outside the language too, and says so.
* `not translated:` — the declaration **is** a program of the language and the front end
  failed on it anyway.  This is the list of gaps, and **no module of the corpus has an
  entry in it**: every `…Program.lean` in the tree is free of `not translated`.

## Keeping that so

`scripts/regen-corpus-programs.sh` regenerates `<Module>Program.lean` for every module of
`scripts/corpus-modules.txt` (each one elaborated against `import LakeJs` before it is
written) and then greps the whole tree for `-- not translated:`, exiting non-zero if a
single entry appears.  Running it reproduces every generated program in this repository
and reports

```
OK: no generated program reports `not translated:`
```

The same check is run more widely by `scripts/sweep-not-translated.sh`, over every module
of `SnapshotsPBOPure/`, `SnapshotsMy/`, `SnapshotsPBOIO/` and `SnapshotsPBOPartial/` — 185
modules, translated in `--check` mode, so nothing is written and only the verdict is read.
It reports

```
sweeping 185 modules
modules translated: 185
OK: no declaration is reported as `not translated`
```

Not one of the 185 produces a `not translated` entry.  Everything the front end declines
is declined either by the totality gate or as outside the language, with the reason named.
(The IO snapshots have to be compiled for the sweep to read them, so `SnapshotsPBOIO` is a
library of `lakefile.toml`; every declaration in it is refused by the totality gate, as an
`IO` function.)

One declination was reclassified by translating it instead: `Char.mk`, which takes the
`UInt32` of a code point, is now the conversion of the runtime (`lean_uint32_to_nat`
followed by `lean_char_of_nat_aux`) rather than a wrapper the language has no counterpart
for, so `SnapshotsPBOPure/BackendSemantics01.test3` — a character written as its code
point and a validity proof — is a `Term` like any other.  The reverse direction, reading
the code point *out* of a `Char`, still has no primitive in the runtime catalogue, so
`Char`'s comparison instances remain outside the language.
