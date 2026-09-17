module

public import LakeJs.Ty
public import LakeJs.Layout

@[expose] public section

namespace LakeJs

open LakeJs.Ty

/-!
# The seven shapes of a user-defined type, named — and what makes one well formed

`Ty` models a user-defined Lean declaration by one of seven shapes, and each of them
carries exactly the data that shape needs.  This module gives those payloads a name,
and says — as a decidable check — which payloads are the ones the backend can produce.

## The names

There is **no schema type parameter**: `Ty` is the type language, so the payload of
`Ty.record` is a list of `Ty`s and the payload of `Ty.recAlias` is an `RTy`.  Each name
below is therefore a plain alias for the payload of one constructor:

| shape                        | payload                                       |
| :--------------------------- | :-------------------------------------------- |
| `Ty.enum`                    | `LeanEnumSchema` = `Nat × Int`                 |
| `Ty.record`                  | `LeanRecordSchema` = `List Ty`                 |
| `Ty.taggedUnion`             | `LeanTaggedUnionSchema` = `List (List Ty)`     |
| `Ty.recTaggedUnion`          | `LeanRecTaggedUnionSchema` = `List (List RTy)` |
| `Ty.recObject`               | `LeanRecObjectSchema` = `List RTy`             |
| `Ty.recAlias`                | `LeanRecAliasSchema` = `RTy`                   |
| `Ty.mutualRecursiveFamily`   | `LeanMutualRecFamily` = `List FamMember × Nat` |

They are aliases, not wrappers: `Ty.record fs` takes a `LeanRecordSchema` and nothing
has to be unwrapped.  What they add is a name to talk about — `Ty.recordSchema?` reads
one off a `Ty`, `LeanRecordSchema.ok` says whether it is one the backend can produce,
and `LakeJs.TyMeta` reads one off a real Lean declaration.

## Which payloads are well formed

Only one of the conditions below is carried by `Ty` itself: `Ty.enum` takes a proof that
it has at least one constructor.  The rest are *shape* conditions the type does not
state, so they are written here as decidable predicates, one per shape, in two tiers.

`.ok` is the **structural** tier, which the translation in `LakeJs.FromLcnf` maintains
for every type it produces:

* a `record` has **at least two** fields — a one-field declaration is a newtype, whose
  wrapper is erased, and a field-less one is `enum 1`;
* a `taggedUnion` has **at least two** constructors, at least one of them with a field
  — otherwise it is an `enum`;
* a `recTaggedUnion` has at least two constructors and **mentions itself**
  (`RTy.self 0`; an index other than `0` has no binder to refer to);
* a `recObject` has at least two fields and mentions itself;
* a `recAlias` mentions itself — a wrapper that does not is erased into its field, and
  there is no `recAlias` for it;
* a `mutualRecursiveFamily` has at least two members, points at one of them, mentions
  only members it has, and each of its members is shaped like a member (a member with
  one constructor carrying one field is an `alias` member).

`.strict` adds the conditions that say the type has **values at all**:

* a recursive declaration has a constructor that can be built without a value of its
  own type — `recAlias (.self 0)` is the equation `T = T`, which no value satisfies,
  while `recAlias (.array (.self 0))` is an array, which may be empty;
* a family is **strongly connected**: two declarations that do not each reach the other
  are two separate types that happen to share a `mutual` block, not one family.

Those are true of every type a working program uses, but they are not maintained by the
current translation — Lean accepts an empty `inductive`, and it accepts a `mutual` block
whose members ignore each other — so they are a check to run, not a condition of being a
`Ty`.

`Ty.wf` and `Ty.wfStrict` are the two tiers at every node of a whole type, nested
recursive shapes included.  Both are deliberately *checks*, not indices: see
`TY_SCHEMA_ASSESSMENT.md` for what it would take to make each of these conditions a
constructor argument of `Ty`, and which of them is worth it.
-/

/-! ## The seven payloads -/

/-- The payload of `Ty.enum`: how many constructors the type has, and the number its
    first constructor prints as (`Ordering` is `(3, -1)`, an ordinary enum `(n, 0)`). -/
abbrev LeanEnumSchema := Nat × Int

/-- The payload of `Ty.record`: the types of the fields, in declaration order. -/
abbrev LeanRecordSchema := List Ty

/-- The payload of `Ty.taggedUnion`: one entry per constructor, in declaration order,
    each holding the types of that constructor's fields. -/
abbrev LeanTaggedUnionSchema := List (List Ty)

/-- The payload of `Ty.recTaggedUnion`: as `LeanTaggedUnionSchema`, but the field types
    may mention the declaration itself as `RTy.self 0`. -/
abbrev LeanRecTaggedUnionSchema := List (List Ty.RTy)

/-- The payload of `Ty.recObject`: the types of the fields of the single constructor,
    which may mention the declaration itself as `RTy.self 0`. -/
abbrev LeanRecObjectSchema := List Ty.RTy

/-- The payload of `Ty.recAlias`: the type the erased wrapper stands for, mentioning
    the declaration itself as `RTy.self 0`. -/
abbrev LeanRecAliasSchema := Ty.RTy

/-- The payload of `Ty.mutualRecursiveFamily`: the bodies of all the members of the
    block, in declaration order, and which of them the type is. -/
abbrev LeanMutualRecFamily := List Ty.FamMember × Nat

/-! ## Reading a payload off a type, and building a type from one -/

/-- The `LeanEnumSchema` of a type that is an enum. -/
def Ty.enumSchema? : Ty → Option LeanEnumSchema
  | .enum n _ s => some (n, s)
  | _ => none

/-- The `LeanRecordSchema` of a type that is a record. -/
def Ty.recordSchema? : Ty → Option LeanRecordSchema
  | .record fs => some fs
  | _ => none

/-- The `LeanTaggedUnionSchema` of a type that is a non-recursive tagged union. -/
def Ty.taggedUnionSchema? : Ty → Option LeanTaggedUnionSchema
  | .taggedUnion l => some l
  | _ => none

/-- The `LeanRecTaggedUnionSchema` of a type that is a recursive tagged union. -/
def Ty.recTaggedUnionSchema? : Ty → Option LeanRecTaggedUnionSchema
  | .recTaggedUnion l => some l
  | _ => none

/-- The `LeanRecObjectSchema` of a type that is a recursive record. -/
def Ty.recObjectSchema? : Ty → Option LeanRecObjectSchema
  | .recObject fs => some fs
  | _ => none

/-- The `LeanRecAliasSchema` of a type that is a recursive newtype. -/
def Ty.recAliasSchema? : Ty → Option LeanRecAliasSchema
  | .recAlias b => some b
  | _ => none

/-- The `LeanMutualRecFamily` of a type that is a member of a mutual family. -/
def Ty.mutualRecFamily? : Ty → Option LeanMutualRecFamily
  | .mutualRecursiveFamily ms i => some (ms, i)
  | _ => none

/-- The enum with this many constructors and this shift — `none` when it has none, as
    a type with no values has no representation. -/
def LeanEnumSchema.toTy? (s : LeanEnumSchema) : Option Ty :=
  if h : 0 < s.1 then some (.enum s.1 h s.2) else none

/-- The record with these fields. -/
def LeanRecordSchema.toTy (fs : LeanRecordSchema) : Ty := .record fs

/-- The tagged union with these constructors. -/
def LeanTaggedUnionSchema.toTy (l : LeanTaggedUnionSchema) : Ty := .taggedUnion l

/-- The recursive tagged union with these constructors. -/
def LeanRecTaggedUnionSchema.toTy (l : LeanRecTaggedUnionSchema) : Ty := .recTaggedUnion l

/-- The recursive record with these fields. -/
def LeanRecObjectSchema.toTy (fs : LeanRecObjectSchema) : Ty := .recObject fs

/-- The recursive newtype with this body. -/
def LeanRecAliasSchema.toTy (b : LeanRecAliasSchema) : Ty := .recAlias b

/-- The member of the family this payload describes. -/
def LeanMutualRecFamily.toTy (f : LeanMutualRecFamily) : Ty :=
  .mutualRecursiveFamily f.1 f.2

/-! ## A closed type, read inside a recursive declaration

`RTy` is everything a `Ty` can be and an occurrence of the declaration being defined, so
every closed type is a type of the inner layer as well — it simply mentions no `.self`.
`Ty.toRTy` is that embedding, and `instRTy_toRTy` says it is the inverse of resolving
the recursive occurrences (`LakeJs.Layout.instRTy`), whatever they are resolved to. -/

mutual

/-- A closed type, as a type of the layer inside a recursive declaration. -/
def Ty.toRTy : Ty → RTy
  | .prim p => .prim p
  | .typeParam => .typeParam
  | .shape s => .shape (Ty.toRTyShape s)
  | .enum n h sh => .enum n h sh
  | .record fs => .record (Ty.toRTyList fs)
  | .taggedUnion l => .taggedUnion (Ty.toRTyCtors l)
  | .recTaggedUnion l => .recTaggedUnion l
  | .recObject fs => .recObject fs
  | .recAlias b => .recAlias b
  | .mutualRecursiveFamily ms i => .mutualRecursiveFamily ms i

/-- `Ty.toRTy`, on one of the shared type formers. -/
def Ty.toRTyShape : Shape Ty → Shape RTy
  | .fn ps r => .fn (Ty.toRTyList ps) (Ty.toRTy r)
  | .fn_returnsProd ps r rs =>
      .fn_returnsProd (Ty.toRTyList ps) (Ty.toRTy r) (Ty.toRTyList rs)
  | .array a => .array (Ty.toRTy a)
  | .list a => .list (Ty.toRTy a)
  | .task a => .task (Ty.toRTy a)
  | .promise a => .promise (Ty.toRTy a)
  | .thunk a => .thunk (Ty.toRTy a)

/-- `Ty.toRTy`, on a list of types. -/
def Ty.toRTyList : List Ty → List RTy
  | [] => []
  | t :: ts => Ty.toRTy t :: Ty.toRTyList ts

/-- `Ty.toRTy`, on the constructors of a layout. -/
def Ty.toRTyCtors : List (List Ty) → List (List RTy)
  | [] => []
  | fs :: l => Ty.toRTyList fs :: Ty.toRTyCtors l

end

mutual

/-- An embedded closed type mentions no recursive occurrence, so resolving the
    occurrences gives it back. -/
theorem instRTy_toRTy (rep : Nat → Option Ty) :
    ∀ τ : Ty, LakeJs.Layout.instRTy rep (Ty.toRTy τ) = some τ
  | .prim _ => rfl
  | .typeParam => rfl
  | .shape s => by
      simp [Ty.toRTy, LakeJs.Layout.instRTy, instShape_toRTyShape rep s]
  | .enum _ _ _ => rfl
  | .record fs => by
      simp [Ty.toRTy, LakeJs.Layout.instRTy, instList_toRTyList rep fs]
  | .taggedUnion l => by
      simp [Ty.toRTy, LakeJs.Layout.instRTy, instCtors_toRTyCtors rep l]
  | .recTaggedUnion _ => rfl
  | .recObject _ => rfl
  | .recAlias _ => rfl
  | .mutualRecursiveFamily _ _ => rfl

/-- The same, for one of the shared type formers. -/
theorem instShape_toRTyShape (rep : Nat → Option Ty) :
    ∀ s : Shape Ty, LakeJs.Layout.instShape rep (Ty.toRTyShape s) = some s
  | .fn ps r => by
      simp [Ty.toRTyShape, LakeJs.Layout.instShape, instList_toRTyList rep ps,
        instRTy_toRTy rep r]
  | .fn_returnsProd ps r rs => by
      simp [Ty.toRTyShape, LakeJs.Layout.instShape, instList_toRTyList rep ps,
        instRTy_toRTy rep r, instList_toRTyList rep rs]
  | .array a => by simp [Ty.toRTyShape, LakeJs.Layout.instShape, instRTy_toRTy rep a]
  | .list a => by simp [Ty.toRTyShape, LakeJs.Layout.instShape, instRTy_toRTy rep a]
  | .task a => by simp [Ty.toRTyShape, LakeJs.Layout.instShape, instRTy_toRTy rep a]
  | .promise a => by simp [Ty.toRTyShape, LakeJs.Layout.instShape, instRTy_toRTy rep a]
  | .thunk a => by simp [Ty.toRTyShape, LakeJs.Layout.instShape, instRTy_toRTy rep a]

/-- The same, for a list of types. -/
theorem instList_toRTyList (rep : Nat → Option Ty) :
    ∀ ts : List Ty, LakeJs.Layout.instList rep (Ty.toRTyList ts) = some ts
  | [] => rfl
  | t :: ts => by
      simp [Ty.toRTyList, LakeJs.Layout.instList, instRTy_toRTy rep t,
        instList_toRTyList rep ts]

/-- The same, for the constructors of a layout. -/
theorem instCtors_toRTyCtors (rep : Nat → Option Ty) :
    ∀ l : List (List Ty), LakeJs.Layout.instCtors rep (Ty.toRTyCtors l) = some l
  | [] => rfl
  | fs :: l => by
      simp [Ty.toRTyCtors, LakeJs.Layout.instCtors, instList_toRTyList rep fs,
        instCtors_toRTyCtors rep l]

end

/-! ## Which members of a recursive declaration it mentions -/

mutual

/-- The members of the enclosing recursive declaration that this type mentions.  A
    *nested* recursive shape is not looked into: its `.self`s are its own. -/
def Ty.RTy.selfIdxs : RTy → List Nat
  | .self i => [i]
  | .shape s => RTy.selfIdxsShape s
  | .record fs => RTy.selfIdxsList fs
  | .taggedUnion l => RTy.selfIdxsCtors l
  | _ => []

/-- `RTy.selfIdxs`, on one of the shared type formers. -/
def Ty.RTy.selfIdxsShape : Shape RTy → List Nat
  | .fn ps r => RTy.selfIdxsList ps ++ RTy.selfIdxs r
  | .fn_returnsProd ps r rs =>
      RTy.selfIdxsList ps ++ RTy.selfIdxs r ++ RTy.selfIdxsList rs
  | .array a | .list a | .task a | .promise a | .thunk a => RTy.selfIdxs a

/-- `RTy.selfIdxs`, on a list of types. -/
def Ty.RTy.selfIdxsList : List RTy → List Nat
  | [] => []
  | t :: ts => RTy.selfIdxs t ++ RTy.selfIdxsList ts

/-- `RTy.selfIdxs`, on the constructors of a layout. -/
def Ty.RTy.selfIdxsCtors : List (List RTy) → List Nat
  | [] => []
  | fs :: l => RTy.selfIdxsList fs ++ RTy.selfIdxsCtors l

end

/-- The members of its family that one member mentions. -/
def Ty.FamMember.selfIdxs : FamMember → List Nat
  | .ctors l => RTy.selfIdxsCtors l
  | .alias b => RTy.selfIdxs b

/-- Does every `.self` here point at a member the declaration has? -/
def selfIdxsOk (numMembers : Nat) (idxs : List Nat) : Bool := idxs.all (· < numMembers)

/-! ## Which members have values at all

A recursive declaration may be *empty*: `inductive Bad | mk : Bad → Bad` has no value,
because building one needs one.  The check is a least fixed point — a member is
buildable when it has a constructor all of whose fields are buildable, where a field
that is a member is buildable only if that member already is, and a field that is an
array or a list always is, since the empty one carries no member at all. -/

mutual

/-- Can a value of this type be built when member `i` of the enclosing recursive
    declaration can be built exactly when `avail[i]!` says so? -/
def Ty.RTy.inhabWith (avail : List Bool) : RTy → Bool
  | .self i => (avail[i]?).getD false
  | .prim _ => true
  | .typeParam => true
  | .shape s => RTy.inhabWithShape avail s
  | .enum _ _ _ => true
  | .record fs => RTy.inhabWithAll avail fs
  | .taggedUnion l => RTy.inhabWithSome avail l
  -- a nested recursive shape opens a scope of its own, so it mentions no member of
  -- ours; whether *it* has values is checked where it is
  | .recTaggedUnion _ => true
  | .recObject _ => true
  | .recAlias _ => true
  | .mutualRecursiveFamily _ _ => true

/-- `RTy.inhabWith`, on one of the shared type formers. -/
def Ty.RTy.inhabWithShape (avail : List Bool) : Shape RTy → Bool
  -- a function needs no argument to exist, only a result
  | .fn _ r => RTy.inhabWith avail r
  | .fn_returnsProd _ r rs => RTy.inhabWith avail r && RTy.inhabWithAll avail rs
  -- the empty array and the empty list hold nothing
  | .array _ | .list _ => true
  | .task a | .promise a | .thunk a => RTy.inhabWith avail a

/-- `RTy.inhabWith`, on the fields of one constructor: it needs all of them. -/
def Ty.RTy.inhabWithAll (avail : List Bool) : List RTy → Bool
  | [] => true
  | t :: ts => RTy.inhabWith avail t && RTy.inhabWithAll avail ts

/-- `RTy.inhabWith`, on the constructors of a layout: it needs one of them. -/
def Ty.RTy.inhabWithSome (avail : List Bool) : List (List RTy) → Bool
  | [] => false
  | fs :: l => RTy.inhabWithAll avail fs || RTy.inhabWithSome avail l

end

/-- `RTy.inhabWith`, on one member of a family. -/
def Ty.FamMember.inhabWith (avail : List Bool) : FamMember → Bool
  | .ctors l => RTy.inhabWithSome avail l
  | .alias b => RTy.inhabWith avail b

/-- One step of the fixed point: which members are buildable, given which were. -/
def famInhabStep (ms : List Ty.FamMember) (avail : List Bool) : List Bool :=
  ms.map (Ty.FamMember.inhabWith avail)

/-- Iterate `famInhabStep`. -/
def famInhabIter : Nat → List Ty.FamMember → List Bool → List Bool
  | 0, _, avail => avail
  | n + 1, ms, avail => famInhabIter n ms (famInhabStep ms avail)

/-- Which members of a recursive declaration have values at all.  The step is monotone
    and there are `ms.length` members, so `ms.length` iterations from "none of them"
    reach the fixed point; one more is taken for good measure. -/
def famInhabited (ms : List Ty.FamMember) : List Bool :=
  famInhabIter (ms.length + 1) ms (ms.map fun _ => false)

/-- Does every member of this recursive declaration have values? -/
def famAllInhabited (ms : List Ty.FamMember) : Bool := (famInhabited ms).all id

/-! ## Strong connectivity

A block of declarations is a *family* only when each of its members reaches every
other: two declarations that merely sit in the same `mutual` block, without mentioning
each other, are two independent types. -/

/-- Which members each member mentions. -/
def famEdges (ms : List Ty.FamMember) : List (List Nat) :=
  ms.map Ty.FamMember.selfIdxs

/-- Add to `acc` everything its members mention. -/
def famReachStep (edges : List (List Nat)) (acc : List Nat) : List Nat :=
  acc.foldl (fun a i => ((edges[i]?).getD []).foldl
    (fun a j => if a.contains j then a else j :: a) a) acc

/-- Iterate `famReachStep`. -/
def famReachIter : Nat → List (List Nat) → List Nat → List Nat
  | 0, _, acc => acc
  | n + 1, edges, acc => famReachIter n edges (famReachStep edges acc)

/-- The members reachable from member `i`, `i` itself included. -/
def famReach (ms : List Ty.FamMember) (i : Nat) : List Nat :=
  famReachIter (ms.length + 1) (famEdges ms) [i]

/-- Does every member of the block reach every member of the block? -/
def famStronglyConnected (ms : List Ty.FamMember) : Bool :=
  (List.range ms.length).all fun i =>
    let r := famReach ms i
    (List.range ms.length).all fun j => r.contains j

/-! ## Is a payload one the backend can produce?

Two tiers, because they are not the same question.

* `.ok` — the **structural** conditions, the ones the translation in
  `LakeJs.FromLcnf` maintains for every type it produces: how many constructors and
  fields a shape has, whether it mentions the declaration it belongs to, and whether
  every `.self` points at a member that exists.  A payload that fails one of these is
  one no declaration is read as, and the elaborators of `LakeJs.TyMeta` refuse it.
* `.strict` — those, **and** the conditions that say the type has values at all:
  every member of a recursive declaration is buildable, and a family is strongly
  connected (a block whose members do not each reach the other is two declarations, not
  one family).  These are true of the types a program actually uses, but the current
  translation does not maintain them — `mutual inductive A | mk : B → A; inductive B |
  mk : A → B end` declares two types with no values, and Lean accepts it — so they are
  offered as a check to run, not as a condition of being a `Ty`.  See
  `TY_SCHEMA_ASSESSMENT.md`.
-/

/-- An enum has at least one constructor — a type with none has no values.  (One is
    allowed: `Unit` is `enum 1 0`, the type whose single value is `{ tag: 0 }`.)  The
    condition is already carried by `Ty.enum`, so this only ever fails for a pair
    written by hand. -/
def LeanEnumSchema.ok (s : LeanEnumSchema) : Bool := 0 < s.1

/-- An enum always has values, so there is nothing to add. -/
def LeanEnumSchema.strict (s : LeanEnumSchema) : Bool := LeanEnumSchema.ok s

/-- A record has at least two fields: a one-field declaration is a newtype, which is
    erased into its field, and a field-less one is `enum 1`. -/
def LeanRecordSchema.ok (fs : LeanRecordSchema) : Bool := 2 ≤ fs.length

/-- A tagged union has at least two constructors, at least one of which has a field:
    with no field anywhere it is an enum, and with one constructor it is a record, a
    newtype or `enum 1`. -/
def LeanTaggedUnionSchema.ok (l : LeanTaggedUnionSchema) : Bool :=
  2 ≤ l.length && l.any (fun fs => !fs.isEmpty)

/-- A recursive tagged union has at least two constructors, at least one with a field,
    mentions itself — and only itself, since it has one member. -/
def LeanRecTaggedUnionSchema.ok (l : LeanRecTaggedUnionSchema) : Bool :=
  2 ≤ l.length && l.any (fun fs => !fs.isEmpty) && Ty.RTy.hasSelfCtors l
    && selfIdxsOk 1 (Ty.RTy.selfIdxsCtors l)

/-- As `ok`, and it has a constructor that can be built without a value of its own type, so
    that it has values at all: `inductive Bad | l : Bad → Bad | r : Bad → Bad` has
    none. -/
def LeanRecTaggedUnionSchema.strict (l : LeanRecTaggedUnionSchema) : Bool :=
  LeanRecTaggedUnionSchema.ok l && famAllInhabited [.ctors l]

/-- A recursive record has at least two fields — a one-field one is a newtype, i.e. a
    `recAlias` — and mentions itself. -/
def LeanRecObjectSchema.ok (fs : LeanRecObjectSchema) : Bool :=
  2 ≤ fs.length && Ty.RTy.hasSelfList fs && selfIdxsOk 1 (Ty.RTy.selfIdxsList fs)

/-- As `ok`, and every self occurrence in it is guarded, so that it has values:
    `structure S where s : S; n : Nat` has none. -/
def LeanRecObjectSchema.strict (fs : LeanRecObjectSchema) : Bool :=
  LeanRecObjectSchema.ok fs && famAllInhabited [.ctors [fs]]

/-- A recursive newtype mentions itself — otherwise the wrapper is erased into its
    field and there is no `recAlias` at all. -/
def LeanRecAliasSchema.ok (b : LeanRecAliasSchema) : Bool :=
  Ty.RTy.hasSelf b && selfIdxsOk 1 (Ty.RTy.selfIdxs b)

/-- As `ok`, and it does so guardedly, so that the equation it stands for has a solution:
    `recAlias (.self 0)` is `T = T`, which no value satisfies, while
    `recAlias (.array (.self 0))` is the empty array and more. -/
def LeanRecAliasSchema.strict (b : LeanRecAliasSchema) : Bool :=
  LeanRecAliasSchema.ok b && famAllInhabited [.alias b]

/-- Is this member of a family shaped like one?  A member with constructors has at
    least one; a member with exactly one constructor carrying exactly one field is a
    newtype, and a newtype member is an `alias` member, not a `ctors` one. -/
def Ty.FamMember.shapeOk : FamMember → Bool
  | .ctors [] => false
  | .ctors [[_]] => false
  | .ctors _ => true
  | .alias _ => true

/-- A family has at least two members, points at one of them, mentions only members it
    has, and each of its members is shaped like a member. -/
def LeanMutualRecFamily.ok (f : LeanMutualRecFamily) : Bool :=
  2 ≤ f.1.length && f.2 < f.1.length
    && f.1.all (fun m => selfIdxsOk f.1.length (Ty.FamMember.selfIdxs m)
        && Ty.FamMember.shapeOk m)

/-- As `ok`, and it is a family rather than a `mutual` block of unrelated declarations — each
    member reaches every member — and every member of it has values. -/
def LeanMutualRecFamily.strict (f : LeanMutualRecFamily) : Bool :=
  LeanMutualRecFamily.ok f && famStronglyConnected f.1 && famAllInhabited f.1

/-! ## Well-formedness of a whole type

Each shape of a type is checked by the predicate of its payload, and so is each shape
nested in it.  The traversal takes the tier as an argument: `Ty.wf` is the structural
one, `Ty.wfStrict` also asks that every recursive declaration in the type has values
and that every family in it is one. -/

mutual

/-- Is every shape in this closed type one the backend can produce?  With
    `strict := true`, is every recursive declaration in it one that has values? -/
def Ty.wfWith (strict : Bool) : Ty → Bool
  | .prim _ => true
  | .typeParam => true
  | .shape s => Ty.wfShapeWith strict s
  | .enum n _ _ => LeanEnumSchema.ok (n, 0)
  | .record fs => LeanRecordSchema.ok fs && Ty.wfListWith strict fs
  | .taggedUnion l => LeanTaggedUnionSchema.ok l && Ty.wfCtorsWith strict l
  | .recTaggedUnion l =>
      (if strict then LeanRecTaggedUnionSchema.strict l else LeanRecTaggedUnionSchema.ok l)
        && Ty.RTy.wfCtorsWith strict l
  | .recObject fs =>
      (if strict then LeanRecObjectSchema.strict fs else LeanRecObjectSchema.ok fs)
        && Ty.RTy.wfListWith strict fs
  | .recAlias b =>
      (if strict then LeanRecAliasSchema.strict b else LeanRecAliasSchema.ok b)
        && Ty.RTy.wfWith strict b
  | .mutualRecursiveFamily ms i =>
      (if strict then LeanMutualRecFamily.strict (ms, i)
       else LeanMutualRecFamily.ok (ms, i))
        && Ty.FamMember.wfListWith strict ms

/-- `Ty.wfWith`, on one of the shared type formers. -/
def Ty.wfShapeWith (strict : Bool) : Shape Ty → Bool
  | .fn ps r => Ty.wfListWith strict ps && Ty.wfWith strict r
  | .fn_returnsProd ps r rs =>
      Ty.wfListWith strict ps && Ty.wfWith strict r && Ty.wfListWith strict rs
  | .array a | .list a | .task a | .promise a | .thunk a => Ty.wfWith strict a

/-- `Ty.wfWith`, on a list of closed types. -/
def Ty.wfListWith (strict : Bool) : List Ty → Bool
  | [] => true
  | t :: ts => Ty.wfWith strict t && Ty.wfListWith strict ts

/-- `Ty.wfWith`, on the constructors of a closed layout. -/
def Ty.wfCtorsWith (strict : Bool) : List (List Ty) → Bool
  | [] => true
  | fs :: l => Ty.wfListWith strict fs && Ty.wfCtorsWith strict l

/-- `Ty.wfWith`, one layer down: this type may mention the declaration it sits in. -/
def Ty.RTy.wfWith (strict : Bool) : RTy → Bool
  | .self _ => true
  | .prim _ => true
  | .typeParam => true
  | .shape s => RTy.wfShapeWith strict s
  | .enum n _ _ => LeanEnumSchema.ok (n, 0)
  -- the same conditions as `LeanRecordSchema.ok` and `LeanTaggedUnionSchema.ok`, one
  -- layer down: these fields may mention the declaration they sit in
  | .record fs => 2 ≤ fs.length && RTy.wfListWith strict fs
  | .taggedUnion l =>
      2 ≤ l.length && l.any (fun fs => !fs.isEmpty) && RTy.wfCtorsWith strict l
  | .recTaggedUnion l =>
      (if strict then LeanRecTaggedUnionSchema.strict l else LeanRecTaggedUnionSchema.ok l)
        && RTy.wfCtorsWith strict l
  | .recObject fs =>
      (if strict then LeanRecObjectSchema.strict fs else LeanRecObjectSchema.ok fs)
        && RTy.wfListWith strict fs
  | .recAlias b =>
      (if strict then LeanRecAliasSchema.strict b else LeanRecAliasSchema.ok b)
        && RTy.wfWith strict b
  | .mutualRecursiveFamily ms i =>
      (if strict then LeanMutualRecFamily.strict (ms, i)
       else LeanMutualRecFamily.ok (ms, i))
        && Ty.FamMember.wfListWith strict ms

/-- `RTy.wfWith`, on one of the shared type formers. -/
def Ty.RTy.wfShapeWith (strict : Bool) : Shape RTy → Bool
  | .fn ps r => RTy.wfListWith strict ps && RTy.wfWith strict r
  | .fn_returnsProd ps r rs =>
      RTy.wfListWith strict ps && RTy.wfWith strict r && RTy.wfListWith strict rs
  | .array a | .list a | .task a | .promise a | .thunk a => RTy.wfWith strict a

/-- `RTy.wfWith`, on a list of types. -/
def Ty.RTy.wfListWith (strict : Bool) : List RTy → Bool
  | [] => true
  | t :: ts => RTy.wfWith strict t && RTy.wfListWith strict ts

/-- `RTy.wfWith`, on the constructors of a layout. -/
def Ty.RTy.wfCtorsWith (strict : Bool) : List (List RTy) → Bool
  | [] => true
  | fs :: l => RTy.wfListWith strict fs && RTy.wfCtorsWith strict l

/-- `RTy.wfWith`, on one member of a family. -/
def Ty.FamMember.wfWith (strict : Bool) : FamMember → Bool
  | .ctors l => Ty.RTy.wfCtorsWith strict l
  | .alias b => Ty.RTy.wfWith strict b

/-- `RTy.wfWith`, on the members of a family. -/
def Ty.FamMember.wfListWith (strict : Bool) : List FamMember → Bool
  | [] => true
  | m :: ms => Ty.FamMember.wfWith strict m && Ty.FamMember.wfListWith strict ms

end

/-- Is every shape in this type one the backend can produce? -/
def Ty.wf (t : Ty) : Bool := Ty.wfWith false t

/-- `Ty.wf`, and in addition: every recursive declaration in the type has values, and
    every mutual family in it really is one. -/
def Ty.wfStrict (t : Ty) : Bool := Ty.wfWith true t

/-- `Ty.wf`, one layer down. -/
def Ty.RTy.wf (t : RTy) : Bool := Ty.RTy.wfWith false t

/-- `Ty.wfStrict`, one layer down. -/
def Ty.RTy.wfStrict (t : RTy) : Bool := Ty.RTy.wfWith true t

end LakeJs

end
