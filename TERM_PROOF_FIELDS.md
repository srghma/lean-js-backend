# Structures whose fields are proofs

*Companion to `TERM_ONE_GRAMMAR_ASSESSMENT.md` (the plan of record),
`TERM_TCO04_WALKTHROUGH.md` (a numeric `Valid`-guarded pair) and
`TERM_VALID_DATA_WALKTHROUGH.md` (the same over data).  Every claim below is marked
**[verified]** — reproducible from a file or a dump checked in beside this document — or
**[proposed]**, meaning it is a design decision I am recommending, not a fact about the
tree.*

Specimens: `ExamplesProofFields/` (builds with `lake build ExamplesProofFields`, no
`sorry`).  Tools: `scripts/dump-shape.lean` (new), `scripts/dump-recursion-kind.lean`
(new), `scripts/dump-lcnf-saveBase.lean` (existing).

---

## 0. The two answers, first

**Should `LeanEnumSchema` and the other schemas preserve the proof fields?  No.**  A
proof field is not a smaller amount of information than a data field — it is *no*
information: by proof irrelevance any two inhabitants of a `Prop` are equal, so every
function of a proof is constant (`ExamplesProofFields.measure_indep_of_proof`, **[verified]**),
and the only way to extract a number from a proof is `Classical.choice`, which makes the
whole declaration `noncomputable` and so removes it from the compiler's world entirely
(`ExamplesProofFields.fromProof`, **[verified]**).  A schema that carried the proof fields
would carry a field that no term could read, no measure could mention and no JavaScript
value would hold.  What the schemas must do — and already do — is **count only the fields
that survive erasure**, which is what makes `Status`'s three proof-carrying constructors
an `enum ⟨0,0⟩` and `Rose`'s two source fields a one-field `recAlias`.

**And how can `test1 (input : Status n)` terminate, if `Status` is two numbers?**  It
terminates the same way it terminated before the proofs were deleted: on the **rank**.
Termination in the grammar never rests on the proof; it rests on the `termination_by`
measure, which is an expression over the *runtime* arguments, and which the loop turns
into a counter that is initialised at entry and decremented once per iteration.  The
proofs in `Status` decide which runtime values are *reachable*, and reachability is
exactly what the design is allowed to be pessimistic about: on the inputs Lean can
actually construct the ranked loop returns Lean's answer
(`ExamplesProofFields.runRanked_agrees`, **[verified]**), and on an input Lean cannot
construct — a tag with no proof-carrying counterpart — it stops at the counter and
answers the canonical inhabitant instead of diverging
(`ExamplesProofFields.runRanked_bad_tag`, **[verified]**).  This is `Tco07`'s `boom`
again, moved from an argument into a constructor.

---

## 1. The rule, in one line

> A field exists in the type language if and only if it survives erasure; the shapes
> count surviving fields and surviving constructors.

Erased are: a `Prop`-typed field (a proof), a `Sort`-typed field (a type), and a field
whose type has a single value.  Constructors are **never** erased — a constructor with no
values still has a tag.

Everything else in this document is that rule applied, plus its consequences for the
front end.

### 1.1 What the rule is worth: the shape does not move  **[verified]**

`ExamplesProofFields/Shapes.lean` declares seven proof-carrying types, one per shape, and
next to each one its *erased twin* — the same declaration with the proof fields deleted by
hand.  `scripts/dump-shape.lean` computes both shapes from the environment
(`ExamplesProofFields/Shapes-Shapes.txt`):

| proof-carrying | shape | erased twin | shape |
| :--- | :--- | :--- | :--- |
| `Status` | `enum` | `StatusE` | `enum` |
| `Window` | `record` | `WindowE` | `record` |
| `Reading` | `taggedUnion` | `ReadingE` | `taggedUnion` |
| `NTree` | `recTaggedUnion` | `NTreeE` | `recTaggedUnion` |
| `Tag` | `recObject` | `TagE` | `recObject` |
| `Rose` | `recAlias` | `RoseE` | `recAlias` |
| `PNode` / `PForest` | `mutualRecursiveFamily` | `PNodeE` / `PForestE` | `mutualRecursiveFamily` |

and for each pair the file proves that the erasure map is **injective**
(`Status.erase_injective`, …, `PForest.erase_injective`): deleting the proof fields loses
nothing, because two values with the same data have equal proof fields by
`proof_irrel`.  For `NTree` it also proves `NTree.size_erase` — the *rank* of a value and
the rank of its erased twin are the same number, which is what lets the backend compute a
structural rank from the erased value.

What erasure is not is *surjective* — `Status.erase_not_surjective` **[verified]**: for
`n = 5` there is no `error` value, but the erased enum has the tag anyway.  That gap is
the subject of §4.

### 1.2 The `Ty`s themselves  **[verified]**

`ExamplesProofFields/ShapesTy.lean` writes each of the seven down in `LakeJs.Ty` and
checks well-formedness by `decide`:

```lean
def statusTy  : Ty := .enum ⟨0, 0⟩                                    -- three tags, no fields
def windowTy  : Ty := .record ⟨.prim .nat, .prim .nat, []⟩
def readingTy : Ty := .taggedUnion (.skip (.here ⟨.prim .nat, []⟩ [])) -- = Ty.option .nat
def ntreeTy   : Ty := .recTaggedUnion (.skip (.here ⟨.prim .nat, [.self 0, .self 0]⟩ []))
def tagTy     : Ty := .recObject ⟨.prim .nat, .array (.self 0), []⟩
def roseTy    : Ty := .recAlias (.array (.self 0))
def pforestTy : Ty := .mutualRecursiveFamily (.selectedLast pnodeMember [] pforestMember)
```

Note `roseTy ≠ tagTy` (proved in the file): `Rose` is written with two fields and is a
newtype, `Tag` is written with three and is an object.

---

## 2. Seven examples per shape — the forty-nine  **[verified]**

`ExamplesProofFields/Variants.lean` contains seven declarations in each of the seven
groups, and `ExamplesProofFields/Variants-Shapes.txt` is the computed shape of every one
of them.  Within a group the variants are always: (1) no proofs, (2) one proof, (3) a
proof in every constructor, (4) a proof about a parameter, (5) a data field whose type
depends on an earlier field, (6) several proofs in one constructor, (7) the **collapse** —
one more field turned into a proof.

| group | V1–V6 (all the same shape) | V7, the collapse |
| :--- | :--- | :--- |
| `Enum` | `enum` | two constructors left ⇒ **`bool`** |
| `Record` | `record` | one surviving field ⇒ **newtype** (`Ty` of the field) |
| `Union` | `taggedUnion` | no surviving field anywhere ⇒ **`enum`** |
| `RecUnion` | `recTaggedUnion` | *no collapse exists* — see below |
| `RecObject` | `recObject` | one surviving field ⇒ **`recAlias`** |
| `RecAlias` | `recAlias` | a second surviving field ⇒ **`recObject`** |
| `Family` | `mutualRecursiveFamily` | a member stops mentioning the others ⇒ the block is **not a family**: `F7` is an `enum` and `N7` a newtype for it |

Two of those rows are findings rather than bookkeeping.

**A recursive sum cannot be collapsed by proofs.**  A proof field can never *hold* a
recursive occurrence: writing `| node (n : Nat) (h : Nonempty V7)` inside a `Type`-valued
inductive is rejected by the kernel — *"mutually inductive types must live in the same
universe"* **[verified]** — so there is no way to make the recursion disappear into the
erased part.  A recursive sum stays a recursive sum however many proofs are added.  The
nearest thing to a collapse is the payload shrinking from `[nat, self, self]` to
`[self, self]`.

**A mutual block can stop being a family.**  `Ty`'s family members are `ctors`, `record`
and `alias` — there is deliberately no *enum* member, because an enum mentions no other
member.  Group `Family`'s V7 is exactly that case: proofs remove `F7`'s last data field,
`F7` becomes a three-constructor enum, and the block decomposes into two independent
declarations.  So **the front end must recompute strong connectivity after erasure, not
before** **[proposed]** — `scripts/dump-shape.lean` does it that way, which is why it
reports `N7` as a newtype and not as a family member.

### 2.1 The same rule over the standard library  **[verified]**

`ExamplesProofFields/Library-Shapes.txt`:

| Lean type | shape after erasure |
| :--- | :--- |
| `Subtype`, `Fin`, `Vector`, `Array`, `String` | newtype — the wrapper and the proof are gone |
| `Decidable` | `bool` (both constructors carry only a proof) |
| `Ordering` | `enum` |
| `Option`, `Except` | `taggedUnion` |
| `Prod`, `Sigma`, `PSigma` | `record` |
| `Acc`, `Nonempty` | the whole type is a `Prop`: erased, no `Ty` |

(`Array`, `String` and `List` are *primitive* in `Ty`; the classifier reports the
structural shape they would have if they were user-defined.)

`ExamplesProofFields/Classes.lean` adds the bundles **[verified]**: a class with one
operation and a law is a **newtype** for the operation (`Semi`), a class with two
operations is a `record` (`SemiUnit`), a class with nothing but laws is itself a `Prop`
and is erased outright (`Lawful`) — so an instance argument of it is dropped from every
signature.  A structure whose fields are all proofs is likewise a `Prop` (`OnlyProof`).
Inheritance is just a field: `Child extends Base` is a `record` of the parent's surviving
field and its own, and `ChildOfProof extends OnlyProof` is a newtype.  An `autoParam`
field (`hle : lo ≤ hi := by omega`) is erased like any other proof; an `optParam` data
field (`step : Nat := 1`) survives.

---

## 3. Why the schemas must not carry the proofs

Four reasons, in decreasing order of finality.

1. **There is nothing to carry.**  `measure_indep_of_proof` **[verified]**: for any
   `f : p → Nat` and any `h₁ h₂ : p`, `f h₁ = f h₂`.  A proof field cannot influence a
   value, a branch or a rank.
2. **The one escape hatch removes the declaration from the compiler.**
   `Exists.choose`/`Classical.choice` is the only way to read data out of a proof, and a
   definition that uses it is `noncomputable`: Lean emits no code, so the translator never
   sees it **[verified]**.
3. **`Ty` has no `Prop`.**  The type language is a description of runtime values: `{ tag,
   _1, _2 }` and nothing else.  A proof field in a schema would either have to be given a
   JavaScript representation (a value that is provably indistinguishable from any other —
   pure cost) or be a phantom entry that every traversal must skip, which is the field
   renumbering bug waiting to happen.
4. **It would import the termination problem into the object language.**  Carrying
   `h : 0 < n` only helps if something *reads* it, and the only thing that would want to
   read it is a `decreasing_by` argument — i.e. the certificate design that
   `TERM_ONE_GRAMMAR_ASSESSMENT.md` removes.  The rank exists precisely so that the
   grammar never has to re-prove Lean's termination argument.

**What is given up, and where to get it back.**  Because the proofs are gone, the term
cannot *refuse* a bad input; it runs and, at worst, exhausts its rank.  The three ways to
restore the refusal are unchanged from `TERM_VALID_DATA_WALKTHROUGH.md` §6: a typed entry
wrapper in Lean (`run (n : Int) (h : Valid1 n)`), which makes a statically known bad input
a proof obligation; a `checked : … → option …` entry compiled from the decidable
precondition, for inputs known only at run time; or moving the condition into the *type*,
where it is a shape condition (`ForestRefined`).  Proof-carrying data adds nothing new to
that list — and note that moving a condition into the type *removes* fields (the flag
field disappears), so it makes the runtime type smaller, not larger.

---

## 4. The question worked through: `Status`, and a recursion over it

`ExamplesProofFields/Countdown.lean` **[verified]**.  `Step n` is the `Status` pattern with
teeth: three constructors, five proof fields between them, no data —

```lean
inductive Step (n : Nat) where
  | stop (h : n = 0)
  | half (h : 0 < n)
  | boom (h1 : n = 0) (h2 : 0 < n)   -- no values at all; still a tag
```

— and `run` halves `n` in the `half` branch and **loops on the spot** in the `boom`
branch, which Lean accepts because the contradictory proofs discharge the `decreasing_by`
obligation:

```lean
def run (n : Nat) (s : Step n) : Nat :=
  match s with
  | .stop _ => 0
  | .half _ => 1 + run (n / 2) (Step.of (n / 2))
  | .boom h1 h2 => 1 + run n (.boom h1 h2)
termination_by n
```

**What Lean hands the front end.**  `scripts/dump-recursion-kind.lean` **[verified]**:

```
ExamplesProofFields.run: well-founded recursion
  packed  : ExamplesProofFields.run._unary
  measure : fun x => PSigma.casesOn x fun n s => n
```

The measure is `n`.  The `Step` argument contributes nothing to it — as it cannot, being
an enum.  So the rank is available, and the proof-carrying argument is irrelevant to it:
**the answer to "how can it terminate?" is that the measure was never about the data**.

**And the divergent branch is really there.**  In the `saveBase` dump
(`ExamplesProofFields/Countdown-Lcnf.txt`) all three alternatives survive, and the third
one rebuilds the empty constructor and calls itself:

```
  | ExamplesProofFields.Step.boom h1.9 h2.10 =>
    let _x.12 := @ExamplesProofFields.Step.boom n ◾ ◾;
    let _x.13 := ExamplesProofFields.run n _x.12;
```

Lean did not mark the branch unreachable (it is dead by the *proofs*, not by the code), so
the compiled function contains a loop that never terminates if control ever reaches it.
The erased twin `runErased` demonstrates it: it answers on tags 0 and 1, and at fuel 5000
still has no answer on tag 2 **[verified]**.

**The ranked loop repairs it, and changes nothing else.**  `runRanked rank n tag` is the
shape the grammar gives this function: one loop, a counter initialised to the measure, one
decrement per iteration, the canonical inhabitant when it runs out.  Two theorems:

* `runRanked_agrees : n ≤ rank → runRanked rank n (tagOf n) = run n (Step.of n)` — started
  the way the loop's entry starts it, it is exactly Lean's function;
* `runRanked_bad_tag : runRanked rank n 2 = rank` — on the tag no Lean value has, it stops.

That is the whole design in miniature, and it is the reason the schemas do not need the
proofs: the proofs would only be able to tell us that tag 2 is unreachable, and the rank
does not need to know.

---

## 5. Where proofs *do* reach the front end: three gates  **[proposed, evidence verified]**

The schemas need no change.  The **whitelist** of `TERM_ONE_GRAMMAR_ASSESSMENT.md` §6
needs three clarifications, all of them about erasure.

### G1.  Kind S must require that the recursed-on argument survives erasure

The kind-S branch reads `Structural.eqnInfoExt`'s `recArgPos` and ranks the recursion by
the size of that argument.  If the argument is a `Prop`, there is no such size.
`scripts/dump-recursion-kind.lean` now reports the type of that argument and whether it is
a proof, and the gate is one line: refuse if it is.

Reassuringly, the case is hard to hit.  `ExamplesProofFields.accDown` recurses on an
`Acc (· < ·) n` proof and needs no `termination_by`, and yet Lean records it as
**well-founded**, choosing the measure itself over the surviving argument **[verified]**:

```
ExamplesProofFields.accDown: well-founded recursion
  measure : fun x => PSigma.casesOn x fun n h => n
```

Its `saveBase` body is identical to that of the hand-ranked `accDownRanked`, except for
the erased argument `◾`.

### G2.  A body that eliminates an erased argument itself must be refused

`ExamplesProofFields.accDownRec` writes the same recursion as a direct `Acc.rec`
application.  It is then *not a recursive declaration at all*: no equation info of any
kind, so the whitelist's "not recursive ⇒ no `fix`" branch fires — and yet the compiled
code loops, in a generated callee that carries no measure **[verified]**:

```
def Acc.recC._at_.ExamplesProofFields.accDownRec.spec_0 r a t : Nat :=
  … | Decidable.isTrue hx =>
    let _x.5 := Acc.recC._at_.ExamplesProofFields.accDownRec.spec_0 ◾ _x.4 ◾;
```

Two checks catch it: refuse a body mentioning `Acc.rec` / `WellFounded.fix` /
`WellFounded.fixF`, and run the call-graph acyclicity check of §6.6 over the *generated*
callees as well as the module's own declarations.  A cycle that no classifier produced is
an error, not a warning.

### G3.  Positions are counted twice, and the translator must keep the two apart

At `saveBase` a projection still uses the **kernel** field index, which counts the erased
fields.  In `ExamplesProofFields/Shapes-Lcnf.txt` **[verified]**, `Tag.erase` reads its
second surviving field as `t # 2`, because the proof field sits at index 1:

```
def ExamplesProofFields.Tag.erase t : ExamplesProofFields.TagE :=
  let _x.1 := t # 0;
  let _x.2 := t # 2;
```

and a `cases` alternative still *binds* the erased fields
(`| Status.warn h.3 => …`).  The existing translator already handles both — `runtimeFieldIndex`
renumbers projections by counting non-erased binders, `transAltBody` skips an erased
alternative binder without advancing the field counter, and `isNewtypeInduct` /
`runtimeFieldCount` decide newtypes on surviving fields — so this gate is a statement of
what must stay true, not a change (read from `LakeJs/FromLcnf.lean`; that module does not
build in this tree, which is missing `LakeJs.Compile`, `LakeJs.EmitJs`, `LakeJs.Lookup`,
`LakeJs.Simp` and `LakeJs.ExternTable`, so it was inspected rather than run).

---

## 6. Question 2 — the other complex cases

In rough order of how likely they are to appear in the corpus.  "Supported" means the rule
of §1 already determines the answer and the machinery exists; "needs work" means a plan
item.

| # | case | verdict |
| :-- | :--- | :--- |
| 1 | **Subtypes and refinements** — `Subtype`, `Fin`, `Vector`, a user's `{ xs // Sorted xs }` | supported: a newtype, `Ty` = the base type **[verified]** |
| 2 | **Lawful type classes** — one or more operations plus laws | supported: newtype or record of the operations; a law-only class is a `Prop` and its instance argument is dropped **[verified]** |
| 3 | **Structure inheritance** — `extends` | supported: the parent is one field, which may itself be a newtype or erased **[verified]** |
| 4 | **`autoParam` / `optParam` fields** | supported: classified by the field's type, not by how it is supplied **[verified]** |
| 5 | **Empty constructors** — contradictory proof fields, as `Step.boom` | supported: the tag exists, the branch is kept, and the rank bounds it **[verified]** |
| 6 | **Indexed families** — `Vec α n`, `inductive T : Nat → Type` | indices are erased, so the runtime shape is the unindexed one; the *index*, when it is a function argument, is ordinary runtime data and is frequently the measure **[proposed]** |
| 7 | **Dependent data fields** — `(n : Nat) (v : Vector Nat n)` | supported: a `record` of `nat` and `array nat`; the two are unrelated at run time, which is exactly the loss of the invariant **[verified]** |
| 8 | **Nested recursion through a container** — `Array Tag`, `List V`, `Option V` | supported as data; the *recursion over* it is kind W with an `invImage … sizeOf` measure **[verified]**, so it needs the runtime size primitive (B1 of the plan) **[proposed]** |
| 9 | **Genuine mutual families whose members carry proofs** | supported: the family is recomputed after erasure, and may stop being a family (§2) **[verified]** |
| 10 | **A `Prop` member inside a mutual inductive block** | cannot arise: Lean requires the members of a mutual inductive to share a universe **[verified]** |
| 11 | **A measure that is itself a compiled recursive call** — `t.size`, `xs.len` | must pass the same whitelist as the function it ranks; already a plan item from `TERM_VALID_DATA_WALKTHROUGH.md` §7 **[proposed]** |
| 12 | **Polymorphic declarations** — `{α : Type}` fields or arguments | neither `Ty` nor `RTy` has a `typeParam` constructor today **[verified]**, although `LakeJs/Ty.lean`'s header prose and `FromLcnf`'s `toRTy` still refer to one — so either the constructor comes back or a declaration keeping a value of a type variable must be monomorphised at its instantiation, or refused with a message that says which **[proposed]** |
| 13 | **Quotients** — `Quot`, `Squash`, `Trunc` | a value is its representative, so `Quot.mk`/`Quot.lift` are the identity and an application; soundness rests on the lifted function respecting the relation, which is a Lean-side obligation the backend cannot see **[proposed]** |
| 14 | **Self-reference passed as a value** — `xs.map f` inside `f` | not representable under the plan's §5.2; must be refused or specialised, unchanged by proof fields **[proposed]** |
| 15 | **A declaration whose every argument is erased** | supported: it is a constant, and calls with different proofs are one call **[verified]** |

The two that I would put on the critical path are **8** (the structural rank needs a
runtime size, and proof-carrying recursive structures are the common case for it) and
**12** (nothing to do with proofs, but the same "there is no `Ty` for this" failure mode,
and today it is the most likely refusal a user will meet).

---

## 7. Files

| file | what it is |
| :--- | :--- |
| `ExamplesProofFields/Shapes.lean` | the seven proof-carrying specimens, their erased twins, injectivity of erasure, `NTree.size_erase`, `measure_indep_of_proof` |
| `ExamplesProofFields/ShapesTy.lean` | the same seven written in `LakeJs.Ty`, well-formedness by `decide` |
| `ExamplesProofFields/Variants.lean` | seven variants of each of the seven shapes — forty-nine declarations |
| `ExamplesProofFields/Classes.lean` | classes with laws, inheritance, `autoParam` |
| `ExamplesProofFields/Countdown.lean` | `Step`/`run`/`runErased`/`runRanked` and the two theorems of §4 |
| `ExamplesProofFields/Rejected.lean` | `accDown`, `accDownRec`, `fromProof`, `alwaysSeven` — the three gates of §5 |
| `ExamplesProofFields/*-Shapes.txt` | computed shapes (specimens, variants, classes, library) |
| `ExamplesProofFields/*-Lcnf.txt` | what Lean stored at `saveBase` |
| `ExamplesProofFields/*-Kinds.txt` | which kind of recursion Lean recorded, and the measure |
| `scripts/dump-shape.lean` | the shape classifier; `lake env lean --run scripts/dump-shape.lean <Module> [--out f] [<Type> …]` |
| `scripts/dump-recursion-kind.lean` | recursion kind, `recArgPos`, whether that argument is erased, and the measure |

Reproduce everything with:

```
lake build ExamplesProofFields
lake env lean --run scripts/dump-shape.lean ExamplesProofFields.Variants
lake env lean --run scripts/dump-recursion-kind.lean ExamplesProofFields.Countdown ExamplesProofFields.run
lake env lean --run scripts/dump-lcnf-saveBase.lean ExamplesProofFields.Countdown
```
