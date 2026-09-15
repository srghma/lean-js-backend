module

public import LakeJs.Ty

open NonEmpty.String

@[expose] public section

/-!
# The seven user-type shapes are pairwise disjoint

This module answers the question: *are the schema constructors of `Ty`
(`enum`, `record`, `taggedUnion`, `recTaggedUnion`, `recObject`, `recAlias`,
`mutualRecursiveFamily`) completely disjoint?*

The answer is **yes**, in the only sense in which the question has content, and **no**
in the literal reading "there is no function from one of the schema types to another".

* Literally, functions do exist: the schema types are all nonempty, so there are
  plenty of maps between them — for instance the constant map of
  `constant_map_exists` below.  Nonemptiness alone gives that, and it says nothing
  about the *classification*.
* What is true is that the seven describe **disjoint sets of Lean declarations**:
  every schema pins down five observable facts about the declaration it describes,

  | | mutual? | recursive? | how many constructors? | any fields? | a wrapper? |
  | :-- | :-- | :-- | :-- | :-- | :-- |
  | `LeanEnumSchema`           | no  | no  | ≥ 2 | no     | no  |
  | `LeanRecordSchema`         | no  | no  | 1   | yes    | no  |
  | `LeanTaggedUnionSchema`    | no  | no  | ≥ 2 | yes    | no  |
  | `LeanRecTaggedUnionSchema` | no  | yes | ≥ 2 | yes    | no  |
  | `LeanRecObjectSchema`      | no  | yes | 1   | yes    | no  |
  | `LeanRecAliasSchema`       | no  | yes | 1   | yes    | yes |
  | `LeanMutualRecFamily`      | yes | yes | any | any    | any |

  and these seven rows are pairwise incompatible.  That is what
  `SchemaOf.descriptor_ne` states, and it is proved from the schemas' own structural
  invariants (`≥ 2` constructors and `≥ 2` fields are index patterns, "some
  constructor has a field", "some field mentions the type itself" and "the block is
  strongly connected" are the `by decide` obligations), not assumed.
* The fifth observable is what "no newtypes" adds: *is the declaration a wrapper*, i.e.
  one constructor carrying exactly one field.  A wrapper has no object of its own, so
  a non-recursive one is not a shape at all (`class?` returns `none`: it is erased into
  its field's `Ty`), and a recursive one is `LeanRecAliasSchema`, which is how
  `Ty.recObject` and `Ty.recAlias` stay disjoint even though they agree on the other
  four observables.
* Consequently there is no *faithful* conversion from one shape to another: no
  function between two different schema types can preserve the observables
  (`no_descriptor_preserving_map`).  Any function between them must misreport at
  least one of "mutual?", "recursive?", "how many constructors?", "any fields?",
  "a wrapper?", i.e. it must describe a different declaration.
-/

namespace LakeJs.SchemaDisjoint

/-! ## The five observables -/

/-- The five facts about a Lean declaration that every schema fixes.

`numCtors` counts the constructors of the declaration (a `structure` has one),
`hasFields` says whether *some* constructor carries at least one field, and
`isWrapper` says whether the declaration is a newtype: exactly one constructor,
carrying exactly one field. -/
structure ShapeDescriptor where
  isMutual : Bool
  isRecursive : Bool
  numCtors : Nat
  hasFields : Bool
  isWrapper : Bool
  deriving Repr, DecidableEq

/-- A name for each of the seven shapes. -/
inductive ShapeClass where
  | enum
  | record
  | taggedUnion
  | recTaggedUnion
  | recObject
  | recAlias
  | mutualFamily
  deriving Repr, DecidableEq

/-- Which shape a descriptor describes, if any.  The five observables are enough to
    decide this, which is exactly the disjointness claim.

    `none` means "no shape of its own": a non-recursive wrapper is erased into its
    field's `Ty`. -/
def ShapeDescriptor.class? (d : ShapeDescriptor) : Option ShapeClass :=
  if d.isMutual then some .mutualFamily
  else if d.isWrapper then (if d.isRecursive then some .recAlias else none)
  else if d.isRecursive then
    some (if d.numCtors = 1 then .recObject else .recTaggedUnion)
  else if d.numCtors = 1 then some .record
  else if d.hasFields then some .taggedUnion
  else some .enum

/-! ## The observables of each schema

Each function below *computes* the five observables from the schema's own data; the
theorem after it pins the entries that the schema's invariants force. -/

variable {α : Type}

/-- Is a declaration with these constructors a wrapper: exactly one constructor,
    carrying exactly one field? -/
def ctorsAreWrapper {β : Type} (cs : List (NonEmptyString × List β)) : Bool :=
  match cs with
  | [c] => decide (c.2.length = 1)
  | _   => false

/-- An enum: never mutual, never recursive, `≥ 2` constructors, no fields anywhere
    (the schema has no room for a field at all). -/
def enumDescriptor (s : LeanEnumSchema) : ShapeDescriptor where
  isMutual := false
  isRecursive := false
  numCtors := s.tags.length
  hasFields := false
  isWrapper := false

/-- A record: one constructor, at least two fields — so not a wrapper. -/
def recordDescriptor (s : LeanRecordSchema α) : ShapeDescriptor where
  isMutual := false
  isRecursive := false
  numCtors := 1
  hasFields := !s.names.isEmpty
  isWrapper := decide (s.names.length = 1)

/-- A non-recursive tagged union: `≥ 2` constructors, some of which has a field. -/
def taggedUnionDescriptor (s : LeanTaggedUnionSchema α) : ShapeDescriptor where
  isMutual := false
  isRecursive := false
  numCtors := (s.ctor1 :: s.ctor2 :: s.ctorRest).length
  hasFields := (s.ctor1 :: s.ctor2 :: s.ctorRest).any (fun c => !c.2.isEmpty)
  isWrapper := ctorsAreWrapper (s.ctor1 :: s.ctor2 :: s.ctorRest)

/-- A recursive tagged union: `≥ 2` constructors, and "recursive" is read off the
    shape — some constructor has a field mentioning the type being declared. -/
def recTaggedUnionDescriptor (s : LeanRecTaggedUnionSchema α) : ShapeDescriptor where
  isMutual := false
  isRecursive := (s.ctor1 :: s.ctor2 :: s.ctorRest).any (fun c => selfFieldsUseSelf c.2)
  numCtors := (s.ctor1 :: s.ctor2 :: s.ctorRest).length
  hasFields := (s.ctor1 :: s.ctor2 :: s.ctorRest).any (fun c => !c.2.isEmpty)
  isWrapper := ctorsAreWrapper (s.ctor1 :: s.ctor2 :: s.ctorRest)

/-- A recursive record: one constructor, at least two fields — so not a wrapper — and
    again "recursive" is read off the shape. -/
def recObjectDescriptor (s : LeanRecObjectSchema α) : ShapeDescriptor where
  isMutual := false
  isRecursive := selfFieldsUseSelf s.shape
  numCtors := 1
  hasFields := !s.shape.isEmpty
  isWrapper := decide (s.shape.length = 1)

/-- A recursive newtype: one constructor with exactly one field, which mentions the
    type being declared — both facts are indices of the schema's `body`. -/
def recAliasDescriptor (_s : LeanRecAliasSchema α) : ShapeDescriptor where
  isMutual := false
  isRecursive := true
  numCtors := 1
  hasFields := true
  isWrapper := true

/-- A member of a mutual family.  "Mutual" is read off the shape: at least two
    members whose reference graph is strongly connected.  Such a block is in
    particular recursive, so the same bit answers both questions; the constructor
    count and the presence of fields are those of the denoted member and may be
    anything. -/
def familyDescriptor (fam : LeanMutualRecFamily α) : ShapeDescriptor :=
  let genuinelyMutual :=
    decide (2 ≤ fam.shape.length) && famStronglyConnectedOk fam.shape
  { isMutual := genuinelyMutual
    isRecursive := genuinelyMutual
    numCtors :=
      match fam.shape[fam.member]? with
      | none => 0
      | some m => m.2.length
    hasFields :=
      match fam.shape[fam.member]? with
      | none => false
      | some m => m.2.any (fun c => !c.2.isEmpty)
    isWrapper :=
      match fam.shape[fam.member]? with
      | none => false
      | some m => ctorsAreWrapper m.2 }

/-! ## Each schema lands in its own class -/

theorem enum_class (s : LeanEnumSchema) : (enumDescriptor s).class? = some .enum := by
  simp [enumDescriptor, ShapeDescriptor.class?, LeanEnumSchema.tags]

theorem record_class (s : LeanRecordSchema α) :
    (recordDescriptor s).class? = some .record := by
  simp [recordDescriptor, ShapeDescriptor.class?, LeanRecordSchema.names]

theorem taggedUnion_class (s : LeanTaggedUnionSchema α) :
    (taggedUnionDescriptor s).class? = some .taggedUnion := by
  have h := s.h_shape
  simp only [taggedUnionShapeOk, Bool.and_eq_true] at h
  simp [taggedUnionDescriptor, ShapeDescriptor.class?, ctorsAreWrapper, h.2]

theorem recTaggedUnion_class (s : LeanRecTaggedUnionSchema α) :
    (recTaggedUnionDescriptor s).class? = some .recTaggedUnion := by
  have h := s.h_shape
  simp only [recTaggedUnionShapeOk, Bool.and_eq_true] at h
  simp [recTaggedUnionDescriptor, ShapeDescriptor.class?, ctorsAreWrapper, h.1.2]

theorem recObject_class (s : LeanRecObjectSchema α) :
    (recObjectDescriptor s).class? = some .recObject := by
  have h := s.h_shape
  simp only [recObjectShapeOk, Bool.and_eq_true] at h
  simp [recObjectDescriptor, ShapeDescriptor.class?, LeanRecObjectSchema.shape, h.1.2]

theorem recAlias_class (s : LeanRecAliasSchema α) :
    (recAliasDescriptor s).class? = some .recAlias := by
  simp [recAliasDescriptor, ShapeDescriptor.class?]

theorem family_class (fam : LeanMutualRecFamily α) :
    (familyDescriptor fam).class? = some .mutualFamily := by
  have hsc := fam.stronglyConnected
  have hlen : 2 ≤ fam.shape.length := by
    simpa using fam.two_le_numMembers
  simp [familyDescriptor, ShapeDescriptor.class?, hsc, hlen]

/-! ## Disjointness -/

/-- The schema type belonging to each shape. -/
def SchemaOf (α : Type) : ShapeClass → Type
  | .enum => LeanEnumSchema
  | .record => LeanRecordSchema α
  | .taggedUnion => LeanTaggedUnionSchema α
  | .recTaggedUnion => LeanRecTaggedUnionSchema α
  | .recObject => LeanRecObjectSchema α
  | .recAlias => LeanRecAliasSchema α
  | .mutualFamily => LeanMutualRecFamily α

/-- The five observables of an arbitrary schema. -/
def SchemaOf.descriptor : {c : ShapeClass} → SchemaOf α c → ShapeDescriptor
  | .enum, s => enumDescriptor s
  | .record, s => recordDescriptor s
  | .taggedUnion, s => taggedUnionDescriptor s
  | .recTaggedUnion, s => recTaggedUnionDescriptor s
  | .recObject, s => recObjectDescriptor s
  | .recAlias, s => recAliasDescriptor s
  | .mutualFamily, s => familyDescriptor s

/-- Every schema describes a declaration of its own shape. -/
theorem SchemaOf.class?_descriptor {c : ShapeClass} (s : SchemaOf α c) :
    (SchemaOf.descriptor s).class? = some c := by
  cases c with
  | enum => exact enum_class s
  | record => exact record_class s
  | taggedUnion => exact taggedUnion_class s
  | recTaggedUnion => exact recTaggedUnion_class s
  | recObject => exact recObject_class s
  | recAlias => exact recAlias_class s
  | mutualFamily => exact family_class s

/-- **Disjointness.**  Two schemas of different shapes never describe the same
    declaration: they disagree on "mutual?", "recursive?", "how many constructors?"
    or "any fields?". -/
theorem SchemaOf.descriptor_ne {c c' : ShapeClass} (h : c ≠ c')
    (s : SchemaOf α c) (t : SchemaOf α c') :
    SchemaOf.descriptor s ≠ SchemaOf.descriptor t := by
  intro he
  apply h
  have : some c = some c' := by
    rw [← SchemaOf.class?_descriptor s, ← SchemaOf.class?_descriptor t, he]
  exact Option.some.inj this

/-- **No faithful conversion.**  A function between two different shapes cannot
    preserve the four observables: whatever it returns describes a declaration of the
    target shape, which its argument is not.  (Functions between the schema types do
    exist — see `constant_map_exists` — they just cannot be descriptor-preserving.) -/
theorem no_descriptor_preserving_map {c c' : ShapeClass} (h : c ≠ c')
    (s : SchemaOf α c) (f : SchemaOf α c → SchemaOf α c') :
    ¬ (∀ x, SchemaOf.descriptor (f x) = SchemaOf.descriptor x) := by
  intro hf
  exact SchemaOf.descriptor_ne h s (f s) (hf s).symm

/-! ## The literal reading is false

Plain functions between the schema types do exist, so "disjoint" cannot mean "no
function exists".  Here is a witness: a constant map from enums to records. -/

/-- A record schema, so that `LeanRecordSchema Ty` is visibly nonempty. -/
def aRecord : LeanRecordSchema Ty :=
  { name := nes!"Point"
  , fields := .cons (nes!"x") .float (.cons (nes!"y") .float .nil) }

/-- There *is* a function from one schema type to another — it simply does not
    preserve the four observables. -/
theorem constant_map_exists :
    ∃ f : LeanEnumSchema → LeanRecordSchema Ty, ∀ s, f s = aRecord :=
  ⟨fun _ => aRecord, fun _ => rfl⟩

/-- The constant map, seen as a map between the two shapes. -/
def constEnumToRecord : SchemaOf Ty .enum → SchemaOf Ty .record := fun _ => aRecord

/-- Concretely: the constant map above is not descriptor-preserving. -/
example (s : SchemaOf Ty .enum) :
    ¬ (∀ x, SchemaOf.descriptor (constEnumToRecord x) = SchemaOf.descriptor x) :=
  no_descriptor_preserving_map (by decide) s constEnumToRecord

/-! ## Inside `Ty`

At the level of `Ty` itself the six are distinct constructors of one inductive type,
so a `Ty` built with one of them is never equal to a `Ty` built with another — for any
schemas whatsoever. -/

example (s : LeanEnumSchema) (t : LeanRecord) : Ty.enum s ≠ Ty.record t := by
  intro h; cases h

example (s : LeanRecTaggedUnion) (t : LeanMutualFamily) :
    Ty.recTaggedUnion s ≠ Ty.mutualRecursiveFamily t := by
  intro h; cases h

end LakeJs.SchemaDisjoint

end
