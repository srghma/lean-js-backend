module

public import NonEmpty.String.Basic

open NonEmpty.String

@[expose] public section

/-!
# The seven schemas of a user-defined Lean type

A Lean declaration that is neither a primitive (`PrimTy`) nor a built-in container
(`Array`, `List`, `Thunk`, `Task`, …) is compiled through exactly one of seven
schemas:

| Shape                                       | Mutual? | Recursive? | ≥ 2 ctors? | Fields of a 1-ctor decl | schema                     | `Ty` constructor           |
| :------------------------------------------ | :------ | :--------- | :--------- | :---------------------- | :------------------------- | :------------------------- |
| `inductive Direction \| north \| …`         | no      | no         | yes        | —                       | `LeanEnumSchema`           | `Ty.enum`                  |
| `structure Point where x, y`                | no      | no         | no         | ≥ 2                     | `LeanRecordSchema`         | `Ty.record`                |
| `inductive Option \| none \| some …`        | no      | no         | yes        | —                       | `LeanTaggedUnionSchema`    | `Ty.taggedUnion`           |
| `inductive MyList \| nil \| cons …`         | no      | yes        | yes        | —                       | `LeanRecTaggedUnionSchema` | `Ty.recTaggedUnion`        |
| `structure Tree where n : Nat; kids : Array Tree` | no | yes     | no         | ≥ 2                     | `LeanRecObjectSchema`      | `Ty.recObject`             |
| `structure Rose where kids : Array Rose`    | no      | yes        | no         | exactly 1               | `LeanRecAliasSchema`       | `Ty.recAlias`              |
| a genuinely mutual block                    | yes     | yes        | varies     | any                     | `LeanMutualRecFamily`      | `Ty.mutualRecursiveFamily` |

## No newtypes

A declaration with **one constructor carrying exactly one field** — a newtype /
wrapper — has no runtime representation of its own: the wrapper is erased and the
type *is* its field's type.  So there is no schema for it:

* `structure Wrapper where x : Nat` is `Ty.nat`, not a one-field `Ty.record`;
* `structure Rose where kids : Array Rose` is the *recursive* case — erasing the
  wrapper leaves the equation `Rose = Array Rose`, which is not a plain `Ty` but a
  fixed point.  That is what `LeanRecAliasSchema` records: the single field's type,
  with `SelfTy.self` marking the recursive occurrence.  In JS a `Rose` is an array of
  arrays of … — `[[], [[]], …]` — with no object wrapper anywhere.

This is why `LeanRecordSchema` and `LeanRecObjectSchema` require **two** fields.

A member of a `LeanMutualRecFamily` may be a wrapper, and then it is an **alias
member** (`famIsAliasMember`): the mutual analogue of `LeanRecAliasSchema`.  It has no
object of its own either — a value of it is a value of its single field, with no tag
and no wrapping object — so a mutual block such as

```lean
mutual
  inductive Exp | lit (n : Int) | block (s : Stm)
  inductive Stm | ret (es : Array Exp)
end
```

is accepted, with `Stm = Array Exp`.  The block stays well formed: every member of a
genuinely mutual block references the block
(`LeanMutualRecFamily.famTargets_ne_nil`), so an alias member is always *recursive*,
and a cycle of aliases with no guard (`A = B`, `B = A`) is uninhabited and is rejected
by `famWellFoundedOk`.

Unit-like and void-like *fields* never reach a schema either: they are erased by the
front-end (`Array Unit` becomes `Ty.nat`, a `Unit`-typed field disappears, a
constructor with an uninhabited field disappears), which is also what can turn a
two-field record into a wrapper — see `LakeJs.SourceToTy`.

The shapes are **disjoint**, so no Lean type has two spellings: a tagged union all of
whose constructors are field-less must be an enum; a "recursive" declaration that
never mentions itself must be one of the non-recursive shapes; and a family must be
*genuinely* mutual — at least two members whose reference graph is strongly connected.
In particular the "fake mutual" block

```lean
mutual
  inductive Color | red | blue
  inductive Shape | circle | box
end
```

is **two** `Ty.enum`s, not a family.

## Shapes and rows

Every schema is parameterised by the type `α` of its field types; `Ty` instantiates
`α := Ty`, which makes well-formedness hereditary.

The kernel refuses a field whose *statement* applies a function to a nested occurrence
of the type being defined — `fields.length`, `(fields.map (·.1)).Nodup`, or
`HashMap.size fields`.  So the invariants cannot be `Prop` fields mentioning a field
list that contains `α`.  Each schema is therefore split into

* a **shape** — names only, plus, for recursive declarations, the way each field uses
  the type being declared.  A shape mentions no `α` at all, so it may carry arbitrary
  decidable properties (`Nodup`, "at least one constructor has a field", …); and
* a **row** — an inductive family *indexed by* the shape, holding the actual types.

Counting conditions ("≥ 1 field", "≥ 2 constructors", "≥ 2 members") become index
patterns `x :: xs` / `x :: y :: xs`, so they hold by construction; naming,
recursion and well-foundedness conditions are `by decide` obligations on the shape,
discharged automatically when a schema literal is written.
-/

/-! ## Shapes of the non-mutual schemas -/

/-- The field names of one constructor / one record, in declaration order. -/
abbrev FieldShape := List NonEmptyString

/-- A constructor: its runtime tag and its field names. -/
abbrev CtorShape := NonEmptyString × FieldShape

/-- The constructors of a non-recursive tagged union. -/
abbrev TaggedUnionShape := List CtorShape

/--
The fields of a *recursive* declaration.  Each entry is
`(name, usesSelf, avoidsSelf)`:

* `usesSelf`   — the field mentions the type being declared;
* `avoidsSelf` — a value of the field can be produced **without** already having a
  value of the type being declared (an `Array`/`List`/`Option` of it can be empty; a
  `Thunk`/`Task`/`Promise` of it cannot).

Both bits are determined by the field's type: see `SelfTy`, which is indexed by them.
-/
abbrev SelfFieldShape := List (NonEmptyString × Bool × Bool)

/-- A constructor of a recursive tagged union: its tag and its fields. -/
abbrev RecCtorShape := NonEmptyString × SelfFieldShape

/-- The constructors of a recursive tagged union. -/
abbrev RecTaggedUnionShape := List RecCtorShape

/-- Field names are pairwise distinct. -/
def fieldShapeOk (fs : FieldShape) : Bool := decide fs.Nodup

/--
A non-recursive tagged union: constructor tags pairwise distinct, field names of each
constructor pairwise distinct, and at least one constructor carrying a field
(otherwise the declaration is an enum).
-/
def taggedUnionShapeOk (s : TaggedUnionShape) : Bool :=
  decide ((s.map (·.1)).Nodup)
    && s.all (fun c => fieldShapeOk c.2)
    && s.any (fun c => !c.2.isEmpty)

/-- Field names of a recursive declaration are pairwise distinct. -/
def selfFieldNamesOk (fs : SelfFieldShape) : Bool := decide ((fs.map (·.1)).Nodup)

/-- Some field mentions the type being declared. -/
def selfFieldsUseSelf (fs : SelfFieldShape) : Bool := fs.any (fun f => f.2.1)

/-- A **base** constructor: every field can be produced without a value of the type
    being declared. -/
def selfFieldsAreBase (fs : SelfFieldShape) : Bool := fs.all (fun f => f.2.2)

/--
A recursive tagged union: tags pairwise distinct, field names pairwise distinct, some
constructor really mentioning the declared type (otherwise this is a non-recursive
shape), and some **base** constructor, so that a value can be built at all.
-/
def recTaggedUnionShapeOk (s : RecTaggedUnionShape) : Bool :=
  decide ((s.map (·.1)).Nodup)
    && s.all (fun c => selfFieldNamesOk c.2)
    && s.any (fun c => selfFieldsUseSelf c.2)
    && s.any (fun c => selfFieldsAreBase c.2)

/--
A recursive record: field names pairwise distinct, some field really mentioning the
declared type, and **every** self occurrence guarded by a possibly-empty container, so
that a value can be built at all (`structure S where s : S` is rejected;
`structure Tree where n : Nat; kids : Array Tree` is accepted).

The "at least two fields" condition is an index pattern of `LeanRecObjectSchema`, not
part of this check: a one-field recursive record is a newtype, and is erased into a
`LeanRecAliasSchema`.
-/
def recObjectShapeOk (fs : SelfFieldShape) : Bool :=
  selfFieldNamesOk fs && selfFieldsUseSelf fs && selfFieldsAreBase fs

/-! ## Rows of the non-mutual schemas

The data of a schema: inductive families indexed by the shapes above.  A row and its
shape can never disagree — the shape is *determined* by the row. -/

/-- The fields of a record / of one constructor, in declaration order. -/
inductive FieldRow (α : Type) : FieldShape → Type
  | nil : FieldRow α []
  | cons (name : NonEmptyString) (ty : α) {ks : FieldShape} (rest : FieldRow α ks) :
      FieldRow α (name :: ks)

/-- The constructors of a non-recursive tagged union, in declaration order. -/
inductive CtorRow (α : Type) : TaggedUnionShape → Type
  | nil : CtorRow α []
  | cons (tag : NonEmptyString) {ks : FieldShape} (fields : FieldRow α ks)
         {cs : TaggedUnionShape} (rest : CtorRow α cs) :
      CtorRow α ((tag, ks) :: cs)

/--
The type of one field of a **non-mutual recursive** declaration: an ordinary type, or
a (possibly guarded) occurrence of the type being declared.

The indices are `usesSelf` and `avoidsSelf`, so the two bits a well-foundedness check
needs are computed by the type system while the field type is written:

* `usesSelf = true` — the field mentions the declared type somewhere;
* `avoidsSelf = true` — a value of this field type exists **without** a value of the
  declared type.

`array`, `list` and `option` are *guards*: they may be empty/`none`, so they set
`avoidsSelf := true` whatever they contain.  `thunk`, `task` and `promise` are **not**
guards: producing one still requires producing the declared type, so they pass
`avoidsSelf` through.  `fn` likewise passes it through, and takes its parameter types
from `α`: a self occurrence in a *parameter* would be a negative occurrence and is
therefore not representable.
-/
inductive SelfTy (α : Type) : (usesSelf : Bool) → (avoidsSelf : Bool) → Type
  /-- The type currently being declared. -/
  | self : SelfTy α true false
  /-- An ordinary, already-known type. -/
  | ty (t : α) : SelfTy α false true
  /-- An array — it may be empty, so it never *requires* a value of the declared type. -/
  | array {u a : Bool} : SelfTy α u a → SelfTy α u true
  /-- A list — likewise. -/
  | list {u a : Bool} : SelfTy α u a → SelfTy α u true
  /-- An option — likewise: `none` requires nothing. -/
  | option {u a : Bool} : SelfTy α u a → SelfTy α u true
  /-- A thunk: forcing it must produce the value, so this is *not* a guard. -/
  | thunk {u a : Bool} : SelfTy α u a → SelfTy α u a
  /-- A task: likewise. -/
  | task {u a : Bool} : SelfTy α u a → SelfTy α u a
  /-- A promise: likewise. -/
  | promise {u a : Bool} : SelfTy α u a → SelfTy α u a
  /-- A function whose *result* may mention the declared type.  Parameters are plain
      types (`α`): a self occurrence there would be negative. -/
  | fn (params : List α) {u a : Bool} (ret : SelfTy α u a) : SelfTy α u a
  /-- A pair.  It mentions the declared type when either side does, and it can be
      built without one only when **both** sides can (`Array (Int × Rose)` is a legal
      field of `Rose`; `Int × Rose` on its own is not). -/
  | prod {u₁ a₁ u₂ a₂ : Bool} : SelfTy α u₁ a₁ → SelfTy α u₂ a₂ →
      SelfTy α (u₁ || u₂) (a₁ && a₂)

/-- The fields of a recursive declaration / of one of its constructors. -/
inductive SelfFieldRow (α : Type) : SelfFieldShape → Type
  | nil : SelfFieldRow α []
  | cons (name : NonEmptyString) {u a : Bool} (ty : SelfTy α u a)
         {fs : SelfFieldShape} (rest : SelfFieldRow α fs) :
      SelfFieldRow α ((name, u, a) :: fs)

/-- The constructors of a recursive tagged union, in declaration order. -/
inductive RecCtorRow (α : Type) : RecTaggedUnionShape → Type
  | nil : RecCtorRow α []
  | cons (tag : NonEmptyString) {fs : SelfFieldShape} (fields : SelfFieldRow α fs)
         {cs : RecTaggedUnionShape} (rest : RecCtorRow α cs) :
      RecCtorRow α ((tag, fs) :: cs)

/-! ## The non-mutual schemas -/

/--
A plain enumeration: **not** recursive, **not** mutual, and no constructor has any
field.

At least two constructors are required: one constructor with no fields is a *unit*
type and zero constructors is a *void* type, and neither is representable.

In JS: `0 | 1 | 2 | …` or `"north" | "south" | …`, depending on the configuration.
-/
structure LeanEnumSchema where
  name : NonEmptyString
  /-- The first two constructors, kept separate so that "≥ 2 constructors" holds by
      construction rather than by proof. -/
  ctor1 : NonEmptyString
  ctor2 : NonEmptyString
  ctorRest : List NonEmptyString := []
  /-- Constructor tags are pairwise distinct. -/
  h_tags : fieldShapeOk (ctor1 :: ctor2 :: ctorRest) = true := by decide
  deriving Repr, DecidableEq

namespace LeanEnumSchema

/-- All constructor tags, in declaration order. -/
def tags (s : LeanEnumSchema) : List NonEmptyString :=
  s.ctor1 :: s.ctor2 :: s.ctorRest

/-- An enum has at least two constructors: it is never unit-like and never void. -/
theorem two_le_tags_length (s : LeanEnumSchema) : 2 ≤ s.tags.length := by
  simp [tags]

/-- Constructor tags are pairwise distinct. -/
theorem tags_nodup (s : LeanEnumSchema) : s.tags.Nodup := by
  have h := s.h_tags
  simpa [tags, fieldShapeOk] using h

end LeanEnumSchema

/--
A plain record: **not** recursive, **not** mutual, exactly one constructor with at
least **two** fields.

A field-less record is a unit type, and a *one*-field record is a newtype: both are
erased, so neither is representable.  "At least two fields" is an index pattern
(`field1 :: field2 :: fieldRest`), so it holds by construction.

In JS: `{ _x: …, _y: … }` or `{ _1: …, _2: … }`, depending on the configuration.
-/
structure LeanRecordSchema (α : Type) where
  name : NonEmptyString
  {field1 : NonEmptyString}
  {field2 : NonEmptyString}
  {fieldRest : FieldShape}
  fields : FieldRow α (field1 :: field2 :: fieldRest)
  /-- Field names are pairwise distinct. -/
  h_names : fieldShapeOk (field1 :: field2 :: fieldRest) = true := by decide

/--
A **non-mutual, non-recursive** tagged union: ≥ 2 constructors, at least one of which
carries fields (`Option α`, `Except ε α`, `Sum α β`).

In JS: `{ tag: "none" } | { tag: "some", _val: … }`.
-/
structure LeanTaggedUnionSchema (α : Type) where
  name : NonEmptyString
  {ctor1 : CtorShape}
  {ctor2 : CtorShape}
  {ctorRest : TaggedUnionShape}
  ctors : CtorRow α (ctor1 :: ctor2 :: ctorRest)
  h_shape : taggedUnionShapeOk (ctor1 :: ctor2 :: ctorRest) = true := by decide

/--
A **non-mutual, recursive** tagged union: `MyList`, `Nat`, a binary tree, ….  It refers
only to itself, never to another member of a family.

In JS: `{ tag: …, _1: …, _2: … }`.
-/
structure LeanRecTaggedUnionSchema (α : Type) where
  name : NonEmptyString
  {ctor1 : RecCtorShape}
  {ctor2 : RecCtorShape}
  {ctorRest : RecTaggedUnionShape}
  ctors : RecCtorRow α (ctor1 :: ctor2 :: ctorRest)
  h_shape : recTaggedUnionShapeOk (ctor1 :: ctor2 :: ctorRest) = true := by decide

/--
A **non-mutual, recursive** record: one constructor, at least **two** fields, at least
one field mentioning the type itself, and every such occurrence guarded by a
possibly-empty container
(`structure Tree where n : Nat; kids : Array Tree`).

A one-field recursive record is a newtype; the wrapper is erased and the type becomes
a `LeanRecAliasSchema` (`structure Rose where kids : Array Rose`).
-/
structure LeanRecObjectSchema (α : Type) where
  name : NonEmptyString
  {field1 : NonEmptyString × Bool × Bool}
  {field2 : NonEmptyString × Bool × Bool}
  {fieldRest : SelfFieldShape}
  fields : SelfFieldRow α (field1 :: field2 :: fieldRest)
  h_shape : recObjectShapeOk (field1 :: field2 :: fieldRest) = true := by decide

/--
A **non-mutual, recursive newtype**, with the wrapper erased: one constructor, exactly
one field, and that field mentions the type itself under a guard.

`structure Rose where kids : Array Rose` is the example.  There is no object in the
runtime representation — a `Rose` *is* an `Array Rose`, i.e. a JS array of arrays of
… — so the schema records no field name, only the declaration's name (for diagnostics)
and the body of the fixed point `Name = body[self := Name]`.

The indices of `body` carry both invariants:

* `usesSelf = true` — the field really does mention the declared type; a one-field
  wrapper that does *not* is erased completely (its `Ty` is the field's own `Ty`, and
  no schema is created);
* `avoidsSelf = true` — every self occurrence is guarded by a possibly-empty container,
  so the fixed point has values.  `structure S where s : S` (body `SelfTy.self`, of
  index `true false`) does not typecheck here, and indeed has no values.
-/
structure LeanRecAliasSchema (α : Type) where
  name : NonEmptyString
  body : SelfTy α true true

/-! ## Genuinely mutual families

`LeanMutualRecFamily` is the *unified* schema of a mutual block: there is no longer a
general "any family" schema with a separate wrapper adding the mutuality invariants.
A single structure carries the whole block and all of its invariants, in the same
shape/row style as the five non-mutual schemas — which is also what puts the field
types (`α`, i.e. `Ty`) *inside* a family, where previously a family only recorded
which fields were recursive and left the non-recursive ones untyped. -/

/-- A possibly-empty container guarding an occurrence of a family member.  With the
    general `FamFieldKind` grammar below this is no longer a primitive notion — it is
    just a name for the three guarding constructors — but it keeps the common
    "`Array`/`List`/`Option` of a member" case short to write
    (`FamFieldKind.recUnder`). -/
inductive FamGuard where
  /-- `Array Member`. -/
  | array
  /-- `List Member`. -/
  | list
  /-- `Option Member`. -/
  | option
  deriving Repr, DecidableEq, Inhabited

/--
How one field of one constructor of one family member uses the family: a *type
expression* in which the leaves are either an ordinary type (`nonRec`, whose actual
`Ty` the row supplies) or a direct occurrence of a member (`recAt i`).

This mirrors `SelfTy` — the grammar used for the fields of the *non-mutual* recursive
shapes — so a mutual block is no less expressive than a non-mutual one.  An earlier
version had only the three cases `nonRec`, `recAt i` and "member under one
`Array`/`List`/`Option`", which made fields such as `Array (Array Stm)`,
`Exp × Stm` or `Nat → Exp` unrepresentable even though the analogous non-mutual
fields are representable; those are now `array (array (recAt 1))`,
`prod (recAt 0) (recAt 1)` and `fn (recAt 0)`.

As in `SelfTy`, `array`/`list`/`option` are *guards* (they may be empty, so they do
not require a value of the member they contain) while `thunk`/`task`/`promise`/`fn`
pass that requirement through, and the parameters of a `fn` are ordinary types: an
occurrence of a member there would be negative.
-/
inductive FamFieldKind where
  /-- An ordinary field, mentioning no member of the family; the row supplies its
      type. -/
  | nonRec
  /-- A direct occurrence of member `member`: building this constructor requires a
      value of that member. -/
  | recAt (member : Nat)
  /-- `Array _`: a guard, it may be empty. -/
  | array (inner : FamFieldKind)
  /-- `List _`: a guard. -/
  | list (inner : FamFieldKind)
  /-- `Option _`: a guard (`none` requires nothing). -/
  | option (inner : FamFieldKind)
  /-- `Thunk _`: **not** a guard, forcing it must produce the value. -/
  | thunk (inner : FamFieldKind)
  /-- `Task _`: not a guard. -/
  | task (inner : FamFieldKind)
  /-- `Promise _`: not a guard. -/
  | promise (inner : FamFieldKind)
  /-- A function whose *result* may mention the family; its parameter types are
      ordinary types, carried by the row. -/
  | fn (ret : FamFieldKind)
  /-- A pair; it mentions the family when either side does, and can be built without
      a member only when both sides can. -/
  | prod (fst snd : FamFieldKind)
  deriving Repr, DecidableEq, Inhabited

namespace FamFieldKind

/-- An occurrence of member `member` under one possibly-empty container — the common
    case, spelled as one of the guarding constructors. -/
def recUnder : FamGuard → Nat → FamFieldKind
  | .array,  i => .array (.recAt i)
  | .list,   i => .list (.recAt i)
  | .option, i => .option (.recAt i)

/-- Every member referenced by a field kind, in order of occurrence. -/
def targets : FamFieldKind → List Nat
  | .nonRec     => []
  | .recAt i    => [i]
  | .array k    => targets k
  | .list k     => targets k
  | .option k   => targets k
  | .thunk k    => targets k
  | .task k     => targets k
  | .promise k  => targets k
  | .fn k       => targets k
  | .prod k₁ k₂ => targets k₁ ++ targets k₂

/-- The members a value of this field type cannot be produced without.  Guards
    (`array`/`list`/`option`) contribute nothing, since they may be empty. -/
def requires : FamFieldKind → List Nat
  | .nonRec     => []
  | .recAt i    => [i]
  | .array _    => []
  | .list _     => []
  | .option _   => []
  | .thunk k    => requires k
  | .task k     => requires k
  | .promise k  => requires k
  | .fn k       => requires k
  | .prod k₁ k₂ => requires k₁ ++ requires k₂

/-- Does this field mention the family at all? -/
def usesFamily (k : FamFieldKind) : Bool := !k.targets.isEmpty

/-- Can this field be filled given values of the members in `have`? -/
def isSatisfiableGiven (k : FamFieldKind) (have_ : List Nat) : Bool :=
  k.requires.all (have_.contains ·)

/-- Can this field be filled without already having a value of any member? -/
def isSatisfiable (k : FamFieldKind) : Bool := k.requires.isEmpty

/-- Everything a guarded occurrence needs is available from the start. -/
@[simp] theorem requires_recUnder (g : FamGuard) (i : Nat) : (recUnder g i).requires = [] := by
  cases g <;> rfl

/-- A guarded occurrence still references its member. -/
@[simp] theorem targets_recUnder (g : FamGuard) (i : Nat) : (recUnder g i).targets = [i] := by
  cases g <;> rfl

end FamFieldKind

/-- The fields of one constructor of one family member. -/
abbrev FamFieldShape := List (NonEmptyString × FamFieldKind)

/-- One constructor of one family member: its runtime tag and its fields. -/
abbrev FamCtorShape := NonEmptyString × FamFieldShape

/-- One member of the family: its type name and its constructors. -/
abbrev FamMemberShape := NonEmptyString × List FamCtorShape

/-- A whole mutual block. -/
abbrev FamShape := List FamMemberShape

/-- Every constructor tag of the block, in order. -/
def famAllTags (s : FamShape) : List NonEmptyString :=
  s.flatMap (fun m => m.2.map (·.1))

/-- Member names are pairwise distinct. -/
def famMemberNamesOk (s : FamShape) : Bool := decide ((s.map (·.1)).Nodup)

/-- Tags are pairwise distinct across the **whole** family, so a runtime tag
    determines its constructor. -/
def famTagsOk (s : FamShape) : Bool := decide ((famAllTags s).Nodup)

/-- Field names of each constructor are pairwise distinct. -/
def famFieldNamesOk (s : FamShape) : Bool :=
  s.all (fun m => m.2.all (fun c => decide ((c.2.map (·.1)).Nodup)))

/-- No member is *void*: each has at least one constructor. -/
def famCtorsNonEmptyOk (s : FamShape) : Bool := s.all (fun m => !m.2.isEmpty)

/-- Every recursive occurrence points at an existing member. -/
def famKindsInRangeOk (s : FamShape) : Bool :=
  s.all (fun m => m.2.all (fun c => c.2.all (fun f =>
    f.2.targets.all (fun j => decide (j < s.length)))))

/-- The members directly mentioned by member `i` (out-of-range indices give `[]`). -/
def famTargets (s : FamShape) (i : Nat) : List Nat :=
  match s[i]? with
  | none   => []
  | some m => m.2.flatMap (fun c => c.2.flatMap (fun f => f.2.targets))

/-- One step of reachability: everything already in `acc`, plus every member directly
    mentioned by a member of `acc`. -/
def famReachStep (s : FamShape) (acc : List Nat) : List Nat :=
  (List.range s.length).filter fun j =>
    acc.contains j || acc.any (fun i => (famTargets s i).contains j)

/-- `n` iterations of `famReachStep`. -/
def famReachIter (s : FamShape) : Nat → List Nat → List Nat
  | 0,     acc => acc
  | n + 1, acc => famReachIter s n (famReachStep s acc)

/-- The members reachable from member `i` (including `i` itself).  Each step that
    changes anything adds a member, so `s.length` iterations reach the fixed point. -/
def famReachableFrom (s : FamShape) (i : Nat) : List Nat :=
  famReachIter s s.length [i]

/-- Is the "mentions" graph of the block strongly connected?  This is what makes the
    block *genuinely* mutual: a block with no cross-edges (`Color`/`Shape`) or with
    one-way references (`A` mentions `B` but not conversely) is really a collection of
    independent declarations, each of which has its own `Ty` constructor. -/
def famStronglyConnectedOk (s : FamShape) : Bool :=
  (List.range s.length).all fun i =>
    (List.range s.length).all fun j =>
      (famReachableFrom s i).contains j

/-- One step of the "which members are inhabited?" fixed point: a member joins `acc`
    when it has a constructor all of whose fields are satisfiable — ordinary fields,
    guarded occurrences, and direct occurrences of members already in `acc`. -/
def famInhabStep (s : FamShape) (acc : List Nat) : List Nat :=
  (List.range s.length).filter fun i =>
    acc.contains i ||
      (match s[i]? with
       | none   => false
       | some m => m.2.any (fun c => c.2.all (fun f =>
           f.2.isSatisfiableGiven acc)))

/-- `n` iterations of `famInhabStep`. -/
def famInhabIter (s : FamShape) : Nat → List Nat → List Nat
  | 0,     acc => acc
  | n + 1, acc => famInhabIter s n (famInhabStep s acc)

/-- Is the block well-founded, i.e. is **every** member inhabited?  A mutual block in
    which some member can never be built has no values, and a void type is not
    representable. -/
def famWellFoundedOk (s : FamShape) : Bool :=
  (List.range s.length).all ((famInhabIter s s.length []).contains ·)

/-- Is member `i` an **alias member**: exactly one constructor carrying exactly one
    field?  Such a member is a newtype, and a newtype has no object of its own: its
    runtime representation *is* its single field's, with no tag and no wrapping
    object — exactly what `LeanRecAliasSchema` does for a non-mutual declaration.  The
    tag and the field name recorded for such a member are diagnostics only.

    An alias member is therefore allowed in a family; it is not a reason to reject the
    block.  It cannot escape the family either: every member of a genuinely mutual
    block references the block (`LeanMutualRecFamily.famTargets_ne_nil`), so an alias
    member is always the mutual analogue of `Ty.recAlias`, never a disguised
    declaration of its own. -/
def famIsAliasMember (s : FamShape) (i : Nat) : Bool :=
  match s[i]? with
  | some (_, [c]) => decide (c.2.length = 1)
  | _             => false

/-- All the invariants of a genuinely mutual block, as one decidable check. -/
def famShapeOk (s : FamShape) : Bool :=
  famMemberNamesOk s && famTagsOk s && famFieldNamesOk s && famCtorsNonEmptyOk s
    && famKindsInRangeOk s && famStronglyConnectedOk s && famWellFoundedOk s

/--
The type of one field of a member of a mutual family, indexed by its `FamFieldKind`.
This is the family analogue of `SelfTy`: `nonRec` leaves carry an actual type (`α`),
`recAt i` leaves carry nothing but their member index, and the containers mirror the
grammar of `FamFieldKind` exactly, so the kind is *determined* by the value.
-/
inductive FamTy (α : Type) : FamFieldKind → Type
  /-- An ordinary, already-known type. -/
  | ty (t : α) : FamTy α .nonRec
  /-- A direct occurrence of member `member` of the block. -/
  | memberRef (member : Nat) : FamTy α (.recAt member)
  /-- An array — a guard. -/
  | array {k : FamFieldKind} : FamTy α k → FamTy α (.array k)
  /-- A list — a guard. -/
  | list {k : FamFieldKind} : FamTy α k → FamTy α (.list k)
  /-- An option — a guard. -/
  | option {k : FamFieldKind} : FamTy α k → FamTy α (.option k)
  /-- A thunk — not a guard. -/
  | thunk {k : FamFieldKind} : FamTy α k → FamTy α (.thunk k)
  /-- A task — not a guard. -/
  | task {k : FamFieldKind} : FamTy α k → FamTy α (.task k)
  /-- A promise — not a guard. -/
  | promise {k : FamFieldKind} : FamTy α k → FamTy α (.promise k)
  /-- A function whose result may mention the family.  Parameters are plain types: an
      occurrence of a member there would be negative. -/
  | fn (params : List α) {k : FamFieldKind} (ret : FamTy α k) : FamTy α (.fn k)
  /-- A pair. -/
  | prod {k₁ k₂ : FamFieldKind} : FamTy α k₁ → FamTy α k₂ → FamTy α (.prod k₁ k₂)

/-- The fields of one constructor of a family member. -/
inductive FamFieldRow (α : Type) : FamFieldShape → Type
  | nil : FamFieldRow α []
  | cons (name : NonEmptyString) {k : FamFieldKind} (ty : FamTy α k) {fs : FamFieldShape}
      (rest : FamFieldRow α fs) :
      FamFieldRow α ((name, k) :: fs)

namespace FamFieldRow

variable {α : Type}

/-- An ordinary field, carrying its type. -/
def consTy (name : NonEmptyString) (ty : α) {fs : FamFieldShape} (rest : FamFieldRow α fs) :
    FamFieldRow α ((name, .nonRec) :: fs) :=
  .cons name (.ty ty) rest

/-- A field that is a direct occurrence of member `member`. -/
def consRec (name : NonEmptyString) (member : Nat) {fs : FamFieldShape}
    (rest : FamFieldRow α fs) : FamFieldRow α ((name, .recAt member) :: fs) :=
  .cons name (.memberRef member) rest

/-- A field that is an occurrence of member `member` under one possibly-empty
    container. -/
def consRecUnder (name : NonEmptyString) (guard : FamGuard) (member : Nat)
    {fs : FamFieldShape} (rest : FamFieldRow α fs) :
    FamFieldRow α ((name, .recUnder guard member) :: fs) :=
  match guard with
  | .array  => .cons name (.array (.memberRef member)) rest
  | .list   => .cons name (.list (.memberRef member)) rest
  | .option => .cons name (.option (.memberRef member)) rest

end FamFieldRow

/-- The constructors of one family member, in declaration order. -/
inductive FamCtorRow (α : Type) : List FamCtorShape → Type
  | nil : FamCtorRow α []
  | cons (tag : NonEmptyString) {fs : FamFieldShape} (fields : FamFieldRow α fs)
         {cs : List FamCtorShape} (rest : FamCtorRow α cs) :
      FamCtorRow α ((tag, fs) :: cs)

/-- The members of a family, in declaration order. -/
inductive FamMemberRow (α : Type) : FamShape → Type
  | nil : FamMemberRow α []
  | cons (typeName : NonEmptyString) {cs : List FamCtorShape} (ctors : FamCtorRow α cs)
         {ms : FamShape} (rest : FamMemberRow α ms) :
      FamMemberRow α ((typeName, cs) :: ms)

/--
A **genuinely mutual** recursive family: at least two members (structurally — the
first two are separate fields), whose reference graph is strongly connected, whose
tags are distinct across the whole block, and every one of whose members is
inhabited.

This single structure replaces the earlier pair "unconstrained family +
`LeanMutualRecFamily` wrapper adding `h_multi`/`h_mutual`": the unconstrained family
described shapes that every other `Ty` constructor already describes, so it was never
usable on its own.

## Why `member` lives *inside* the schema

A `Ty` denotes **one** member of the block, so a member index has to be recorded
somewhere, and it has to be checked against the number of members.  It cannot be an
extra argument of the `Ty` constructor, as in
`(fam : …) → (member : Nat) → (h : member < fam.numMembers) → Ty`: the kernel refuses
a constructor argument whose type applies a function (`numMembers`) to a *nested*
occurrence of the type being defined, and it equally refuses making the shape a
parameter of the schema, since the parameters of a nested inductive may not contain
local variables.  Recording `member` as a field, next to the `memberRest` it is
checked against, keeps the bound inside the schema where both are ordinary fields —
and it also makes `Ty.mutualRecursiveFamily` uniform with the other five shapes: one
constructor, one schema.
-/
structure LeanMutualRecFamily (α : Type) where
  /-- The name of the block (conventionally the name of its first member). -/
  name : NonEmptyString
  /-- The first two members, kept separate so that "≥ 2 members" — i.e. "genuinely
      mutual" — holds by construction rather than by proof. -/
  {member1 : FamMemberShape}
  {member2 : FamMemberShape}
  {memberRest : FamShape}
  members : FamMemberRow α (member1 :: member2 :: memberRest)
  /-- Which member of the block this schema denotes. -/
  member : Nat
  h_shape : famShapeOk (member1 :: member2 :: memberRest) = true := by decide
  /-- The denoted member exists, so a schema never points outside its own block. -/
  h_member : member < memberRest.length + 2 := by decide

namespace LeanMutualRecFamily

variable {α : Type}

/-- The shape of the block: its members, their constructors and their field kinds. -/
def shape (fam : LeanMutualRecFamily α) : FamShape :=
  fam.member1 :: fam.member2 :: fam.memberRest

/-- The number of members — always at least `2`.  Computed from the *shape*, so it
    does not inspect the row. -/
def numMembers (fam : LeanMutualRecFamily α) : Nat := fam.memberRest.length + 2

@[simp] theorem numMembers_eq_shape_length (fam : LeanMutualRecFamily α) :
    fam.numMembers = fam.shape.length := by
  simp [numMembers, shape]

theorem two_le_numMembers (fam : LeanMutualRecFamily α) : 2 ≤ fam.numMembers := by
  simp [numMembers]

/-- The denoted member is in range. -/
theorem member_lt_numMembers (fam : LeanMutualRecFamily α) : fam.member < fam.numMembers :=
  fam.h_member

/-- The name of member `i`, if it exists. -/
def memberName? (fam : LeanMutualRecFamily α) (i : Nat) : Option NonEmptyString :=
  (fam.shape[i]?).map (·.1)

/-- Every constructor tag of the block. -/
def tags (fam : LeanMutualRecFamily α) : List NonEmptyString := famAllTags fam.shape

theorem memberNames_nodup (fam : LeanMutualRecFamily α) :
    (fam.shape.map (·.1)).Nodup := by
  have h := fam.h_shape
  simp only [famShapeOk, Bool.and_eq_true] at h
  have := h.1.1.1.1.1.1
  simpa [famMemberNamesOk, shape] using this

theorem tags_nodup (fam : LeanMutualRecFamily α) : fam.tags.Nodup := by
  have h := fam.h_shape
  simp only [famShapeOk, Bool.and_eq_true] at h
  have := h.1.1.1.1.1.2
  simpa [famTagsOk, tags, shape] using this

theorem stronglyConnected (fam : LeanMutualRecFamily α) :
    famStronglyConnectedOk fam.shape = true := by
  have h := fam.h_shape
  simp only [famShapeOk, Bool.and_eq_true] at h
  exact h.1.2

theorem wellFounded (fam : LeanMutualRecFamily α) :
    famWellFoundedOk fam.shape = true := by
  have h := fam.h_shape
  simp only [famShapeOk, Bool.and_eq_true] at h
  exact h.2

/-- Every member of a genuinely mutual family reaches at least one *other* member. -/
theorem exists_cross_edge (fam : LeanMutualRecFamily α) (i : Nat)
    (hi : i < fam.numMembers) :
    ∃ j, j < fam.numMembers ∧ j ≠ i ∧ j ∈ famReachableFrom fam.shape i := by
  have hall := fam.stronglyConnected
  have h2 : 2 ≤ fam.numMembers := fam.two_le_numMembers
  have hlen : fam.shape.length = fam.numMembers := by simp
  have hsel : ∃ j, j < fam.numMembers ∧ j ≠ i := by
    by_cases h : i = 0
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
  obtain ⟨j, hj, hji⟩ := hsel
  refine ⟨j, hj, hji, ?_⟩
  have hi' : i ∈ List.range fam.shape.length := List.mem_range.mpr (by omega)
  have hj' : j ∈ List.range fam.shape.length := List.mem_range.mpr (by omega)
  have h1 := List.all_eq_true.mp hall i hi'
  have h3 := List.all_eq_true.mp h1 j hj'
  exact List.contains_iff_mem.mp h3

/-- A member that mentions nothing cannot reach anything but itself. -/
theorem famReachIter_eq_self {s : FamShape} {i : Nat} (h : famTargets s i = [])
    (n : Nat) (acc : List Nat) (hacc : ∀ x ∈ acc, x = i) :
    ∀ x ∈ famReachIter s n acc, x = i := by
  induction n generalizing acc with
  | zero => intro x hx; exact hacc x hx
  | succ n ih =>
    intro x hx
    refine ih (famReachStep s acc) ?_ x hx
    intro y hy
    simp only [famReachStep, List.mem_filter, Bool.or_eq_true, List.any_eq_true] at hy
    rcases hy.2 with hmem | ⟨z, hz, hzy⟩
    · exact hacc y (List.contains_iff_mem.mp hmem)
    · have : z = i := hacc z hz
      subst this
      rw [h] at hzy
      simp at hzy

/-- **Every** member of a genuinely mutual family references the family: a member
    mentioning nobody could not be reached from — or reach — the others, so the block
    would not be strongly connected.  In particular an alias member
    (`famIsAliasMember`) is always a *recursive* newtype, i.e. the mutual analogue of
    `Ty.recAlias`, and never an independent declaration in disguise. -/
theorem famTargets_ne_nil (fam : LeanMutualRecFamily α) (i : Nat)
    (hi : i < fam.numMembers) : famTargets fam.shape i ≠ [] := by
  intro h
  obtain ⟨j, _, hji, hmem⟩ := exists_cross_edge fam i hi
  exact hji (famReachIter_eq_self h _ [i] (by simp) j hmem)

/-- The single field of an alias member really does mention the family. -/
theorem aliasMember_usesFamily (fam : LeanMutualRecFamily α) (i : Nat)
    (hi : i < fam.numMembers) {nm tag fname : NonEmptyString} {k : FamFieldKind}
    (h : fam.shape[i]? = some (nm, [(tag, [(fname, k)])])) : k.usesFamily = true := by
  have hne := famTargets_ne_nil fam i hi
  rw [famTargets, h] at hne
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hne
  simpa [FamFieldKind.usesFamily, List.isEmpty_iff] using hne

end LeanMutualRecFamily

/-! ## Reading a row back

The shape is an index, so these projections are total and their results are pinned to
the shape by the theorems below. -/

namespace FieldRow

/-- The fields, as an association list. -/
def toList {α : Type} {ks : FieldShape} : FieldRow α ks → List (NonEmptyString × α)
  | .nil => []
  | .cons k v rest => (k, v) :: toList rest

/-- The names of a row are exactly its shape. -/
theorem map_fst_toList {α : Type} {ks : FieldShape} (r : FieldRow α ks) :
    (toList r).map (·.1) = ks := by
  induction r with
  | nil => rfl
  | cons k v rest ih => simp [toList, ih]

end FieldRow

namespace SelfFieldRow

/-- The fields, as an association list of names paired with their two bits. -/
def toList {α : Type} {fs : SelfFieldShape} :
    SelfFieldRow α fs → List (NonEmptyString × Bool × Bool)
  | .nil => []
  | .cons k (u := u) (a := a) _ rest => (k, u, a) :: toList rest

/-- The shape of a row is exactly the list of its `(name, usesSelf, avoidsSelf)`. -/
theorem toList_eq {α : Type} {fs : SelfFieldShape} (r : SelfFieldRow α fs) :
    toList r = fs := by
  induction r with
  | nil => rfl
  | cons k ty rest ih => simp [toList, ih]

end SelfFieldRow

namespace CtorRow

/-- The constructor tags, in declaration order. -/
def tags {α : Type} {cs : TaggedUnionShape} : CtorRow α cs → List NonEmptyString
  | .nil => []
  | .cons t _ rest => t :: tags rest

end CtorRow

namespace RecCtorRow

/-- The constructor tags, in declaration order. -/
def tags {α : Type} {cs : RecTaggedUnionShape} : RecCtorRow α cs → List NonEmptyString
  | .nil => []
  | .cons t _ rest => t :: tags rest

end RecCtorRow

namespace FamCtorRow

/-- The constructor tags of one member, in declaration order. -/
def tags {α : Type} {cs : List FamCtorShape} : FamCtorRow α cs → List NonEmptyString
  | .nil => []
  | .cons t _ rest => t :: tags rest

end FamCtorRow

namespace FamMemberRow

/-- The member names, in declaration order. -/
def names {α : Type} {ms : FamShape} : FamMemberRow α ms → List NonEmptyString
  | .nil => []
  | .cons n _ rest => n :: names rest

end FamMemberRow

/-! ## Facts about the schemas -/

namespace LeanRecordSchema

variable {α : Type}

/-- The field names, in declaration order. -/
def names (s : LeanRecordSchema α) : FieldShape := s.field1 :: s.field2 :: s.fieldRest

/-- A record always has at least two fields: no unit-like record, and no newtype. -/
theorem two_le_numFields (s : LeanRecordSchema α) : 2 ≤ s.names.length := by
  simp [names]

/-- Field names are pairwise distinct. -/
theorem names_nodup (s : LeanRecordSchema α) : s.names.Nodup := by
  have h := s.h_names
  simpa [names, fieldShapeOk] using h

end LeanRecordSchema

namespace LeanTaggedUnionSchema

variable {α : Type}

/-- The constructors, as a shape. -/
def shape (s : LeanTaggedUnionSchema α) : TaggedUnionShape := s.ctor1 :: s.ctor2 :: s.ctorRest

/-- A tagged union always has at least two constructors. -/
theorem two_le_numCtors (s : LeanTaggedUnionSchema α) : 2 ≤ s.shape.length := by
  simp [shape]

/-- Constructor tags are pairwise distinct. -/
theorem tags_nodup (s : LeanTaggedUnionSchema α) : (s.shape.map (·.1)).Nodup := by
  have h := s.h_shape
  simp only [taggedUnionShapeOk, Bool.and_eq_true] at h
  simpa [shape] using h.1.1

/-- At least one constructor carries a field — otherwise this is a `Ty.enum`. -/
theorem some_ctor_has_field (s : LeanTaggedUnionSchema α) :
    s.shape.any (fun c => !c.2.isEmpty) = true := by
  have h := s.h_shape
  simp only [taggedUnionShapeOk, Bool.and_eq_true] at h
  exact h.2

end LeanTaggedUnionSchema

namespace LeanRecTaggedUnionSchema

variable {α : Type}

/-- The constructors, as a shape. -/
def shape (s : LeanRecTaggedUnionSchema α) : RecTaggedUnionShape :=
  s.ctor1 :: s.ctor2 :: s.ctorRest

/-- A recursive tagged union always has at least two constructors. -/
theorem two_le_numCtors (s : LeanRecTaggedUnionSchema α) : 2 ≤ s.shape.length := by
  simp [shape]

/-- Constructor tags are pairwise distinct. -/
theorem tags_nodup (s : LeanRecTaggedUnionSchema α) : (s.shape.map (·.1)).Nodup := by
  have h := s.h_shape
  simp only [recTaggedUnionShapeOk, Bool.and_eq_true] at h
  simpa [shape] using h.1.1.1

/-- It really is recursive: some constructor mentions the declared type. -/
theorem some_ctor_uses_self (s : LeanRecTaggedUnionSchema α) :
    s.shape.any (fun c => selfFieldsUseSelf c.2) = true := by
  have h := s.h_shape
  simp only [recTaggedUnionShapeOk, Bool.and_eq_true] at h
  exact h.1.2

/-- It is well-founded: some constructor is a base constructor, so a value can be
    built. -/
theorem some_ctor_is_base (s : LeanRecTaggedUnionSchema α) :
    s.shape.any (fun c => selfFieldsAreBase c.2) = true := by
  have h := s.h_shape
  simp only [recTaggedUnionShapeOk, Bool.and_eq_true] at h
  exact h.2

end LeanRecTaggedUnionSchema

namespace LeanRecObjectSchema

variable {α : Type}

/-- The fields, as a shape. -/
def shape (s : LeanRecObjectSchema α) : SelfFieldShape :=
  s.field1 :: s.field2 :: s.fieldRest

/-- A recursive record always has at least two fields: a one-field one is a newtype,
    and is erased into a `LeanRecAliasSchema`. -/
theorem two_le_numFields (s : LeanRecObjectSchema α) : 2 ≤ s.shape.length := by
  simp [shape]

/-- Field names are pairwise distinct. -/
theorem names_nodup (s : LeanRecObjectSchema α) : (s.shape.map (·.1)).Nodup := by
  have h := s.h_shape
  simp only [recObjectShapeOk, Bool.and_eq_true] at h
  have := h.1.1
  simpa [shape, selfFieldNamesOk] using this

/-- It really is recursive. -/
theorem uses_self (s : LeanRecObjectSchema α) : selfFieldsUseSelf s.shape = true := by
  have h := s.h_shape
  simp only [recObjectShapeOk, Bool.and_eq_true] at h
  exact h.1.2

/-- It is well-founded: every self occurrence is guarded by a possibly-empty
    container. -/
theorem is_base (s : LeanRecObjectSchema α) : selfFieldsAreBase s.shape = true := by
  have h := s.h_shape
  simp only [recObjectShapeOk, Bool.and_eq_true] at h
  exact h.2

end LeanRecObjectSchema

end
