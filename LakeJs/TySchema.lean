module

public import LakeJs.Ty
public import LakeJs.RTyWf
public import LakeJs.Layout

@[expose] public section

namespace LakeJs

open LakeJs.Ty
open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-!
# The shapes of a user-defined type, named — and what makes one well formed

`Ty` models a user-defined Lean declaration by one of seven shapes, and each of them
carries exactly the data that shape needs.  This module names those payloads, reads one
off a type, builds a type from one, and says — as a decidable check — which of them
describe a type that **exists**.

## The names

The payloads are the schemas of `LakeJs.Schema`, instantiated at the two layers of the
type language:

| shape                        | payload                                          |
| :--------------------------- | :----------------------------------------------- |
| `Ty.enum`                    | `LeanEnumSchema`                                  |
| `Ty.record`                  | `LeanRecordSchema Ty`                             |
| `Ty.taggedUnion`             | `LeanTaggedUnionSchema Ty`                        |
| `Ty.recTaggedUnion`          | `LeanTaggedUnionSchema Ty.RTy`                 |
| `Ty.recObject`               | `LeanRecordSchema Ty.RTy`                      |
| `Ty.recAlias`                | `Ty.RTy`                       |
| `Ty.mutualRecursiveFamily`   | `LeanMutualRecFamily Ty.RTy`                      |

## What is checked here, and what is not

Every **counting** condition is carried by the payload's own type and needs no check:
an enum has three constructors or more, a record two fields or more, a tagged union two
constructors of which one has a field, a family two members and a member number in
range.  A degenerate shape is therefore not a `Ty` that fails a test — it is not a `Ty`.

What is left are the conditions that mention the *type language*, and so cannot be
fields of a schema that is parametrised by it:

* a recursive shape **mentions itself**: `Ty.recAlias ⟨.array .typeParam⟩` is a wrapper
  that does not, and a wrapper that does not is erased into its field;
* every `.self` points at a member the declaration **has**;
* the type **has values**: `inductive Bad | mk : Bad → Bad` is the equation `T = T`,
  which no value satisfies, and neither does `structure Worse where w : Worse; n : Nat`;
* a mutual family is **strongly connected**: two declarations that do not each reach
  the other are two types that happen to share a `mutual` block, not one family.

`RTy.wf` (in `LakeJs.RTyWf`) runs all four at the node that binds `.self`, and each
recursive constructor of `Ty` **carries** the result as a field, so a type that fails is
not a type at all rather than a type that fails a test.
`RTyWf.not_recAliasWf_selfLoop` and `RTyWf.not_recObjWf_selfField` are the two degenerate
recursive declarations, written out and refuted.
-/

/-! ## Reading a payload off a type, and building a type from one -/

/-- The `LeanEnumSchema` of a type that is an enum. -/
def Ty.enumSchema? : Ty → Option LeanEnumSchema
  | .enum s => some s
  | _ => none

/-- The `LeanRecordSchema` of a type that is a record. -/
def Ty.recordSchema? : Ty → Option (LeanRecordSchema Ty)
  | .record fs => some fs
  | _ => none

/-- The `LeanTaggedUnionSchema` of a type that is a non-recursive tagged union. -/
def Ty.taggedUnionSchema? : Ty → Option (LeanTaggedUnionSchema Ty)
  | .taggedUnion l => some l
  | _ => none

/-- The `LeanTaggedUnionSchema` of a type that is a recursive tagged union. -/
def Ty.recTaggedUnionSchema? : Ty → Option (LeanTaggedUnionSchema RTy)
  | .recTaggedUnion l _ => some l
  | _ => none

/-- The `LeanRecordSchema` of a type that is a recursive record. -/
def Ty.recObjectSchema? : Ty → Option (LeanRecordSchema RTy)
  | .recObject fs _ => some fs
  | _ => none

/-- The `LeanMutualRecFamily` of a type that is a member of a mutual family. -/
def Ty.mutualRecFamily? : Ty → Option (LeanMutualRecFamily RTy)
  | .mutualRecursiveFamily f _ => some f
  | _ => none

/-- The enum this payload describes. -/
def LeanEnumSchema.toTy (s : LeanEnumSchema) : Ty := .enum s

/-- The record with these fields. -/
def LeanRecordSchema.toTy (fs : LeanRecordSchema Ty) : Ty := .record fs

/-- The tagged union with these constructors. -/
def LeanTaggedUnionSchema.toTy (l : LeanTaggedUnionSchema Ty) : Ty := .taggedUnion l

/-- The recursive tagged union with these constructors — which has to describe a type
    that exists, since a `Ty` carries that proof. -/
def LeanTaggedUnionSchema.toRecTy (l : LeanTaggedUnionSchema RTy)
    (h : RTy.wf (.recTaggedUnion l) = true := by decide) : Ty := .recTaggedUnion l h

/-- The recursive record with these fields. -/
def LeanRecordSchema.toRecObjTy (fs : LeanRecordSchema RTy)
    (h : RTy.wf (.recObject fs) = true := by decide) : Ty := .recObject fs h

/-- The member of the family this payload describes. -/
def LeanMutualRecFamily.toTy (f : LeanMutualRecFamily RTy)
    (h : RTy.wf (.mutualRecursiveFamily f) = true := by decide) : Ty :=
  .mutualRecursiveFamily f h

/-! ## A closed type, read inside a recursive declaration

`RTy` is everything a `Ty` can be and an occurrence of the declaration being defined, so
every closed type is a type of the inner layer as well — it simply mentions no `.self`.
`Ty.toRTy` is that embedding, and `instRTy_toRTy` says it is the inverse of resolving
the recursive occurrences (`LakeJs.Layout.instRTy`), whatever they are resolved to. -/

mutual

/-- A closed type, as a type of the layer inside a recursive declaration. -/
def Ty.toRTy : Ty → RTy
  | .prim p => .prim p
  | .fn a b => .fn (Ty.toRTy a) (Ty.toRTy b)
  | .primCovariant s => .primCovariant (Ty.toRTyCov s)
  | .enum s => .enum s
  | .record fs => .record (Ty.toRTyA2 fs)
  | .taggedUnion l => .taggedUnion (Ty.toRTyTU l)
  | .recTaggedUnion l _ => .recTaggedUnion l
  | .recObject fs _ => .recObject fs
  | .recAlias b _ => .recAlias b
  | .mutualRecursiveFamily f _ => .mutualRecursiveFamily f

/-- `Ty.toRTy`, on an invariant type former. -/
def Ty.toRTyCov : LeanPrimTyCovariant Ty → LeanPrimTyCovariant RTy
  | .array a => .array (Ty.toRTy a)
  | .list a => .list (Ty.toRTy a)
  | .task a => .task (Ty.toRTy a)
  | .promise a => .promise (Ty.toRTy a)
  | .thunk a => .thunk (Ty.toRTy a)
  | .lazy a => .lazy (Ty.toRTy a)

/-- `Ty.toRTy`, on a list of types. -/
def Ty.toRTyList : List Ty → List RTy
  | [] => []
  | t :: ts => Ty.toRTy t :: Ty.toRTyList ts

/-- `Ty.toRTy`, on the constructors of a layout. -/
def Ty.toRTyCtors : List (List Ty) → List (List RTy)
  | [] => []
  | fs :: l => Ty.toRTyList fs :: Ty.toRTyCtors l

/-- `Ty.toRTy`, on the fields of a record. -/
def Ty.toRTyA2 : LeanRecordSchema Ty → LeanRecordSchema RTy
  | ⟨a, b, rest⟩ => ⟨Ty.toRTy a, Ty.toRTy b, Ty.toRTyList rest⟩

/-- `Ty.toRTy`, on the fields of a constructor that has at least one. -/
def Ty.toRTyNE : NonEmptyList Ty → NonEmptyList RTy
  | ⟨a, as⟩ => ⟨Ty.toRTy a, Ty.toRTyList as⟩

/-- `Ty.toRTy`, on the constructors of a tagged union. -/
def Ty.toRTyTU : LeanTaggedUnionSchema Ty → LeanTaggedUnionSchema RTy
  | .payloadFirst f n r => .payloadFirst (Ty.toRTyNE f) (Ty.toRTyList n) (Ty.toRTyCtors r)
  | .skip rest => .skip (Ty.toRTyCP rest)

/-- `Ty.toRTy`, on the constructors that follow a field-less one. -/
def Ty.toRTyCP : CtorsWithPayload Ty → CtorsWithPayload RTy
  | .here f r => .here (Ty.toRTyNE f) (Ty.toRTyCtors r)
  | .skip rest => .skip (Ty.toRTyCP rest)

end

mutual

/-- An embedded closed type mentions no recursive occurrence, so resolving the
    occurrences gives it back. -/
theorem instRTy_toRTy (rep : Nat → Option Ty) :
    ∀ τ : Ty, LakeJs.Layout.instRTy rep (Ty.toRTy τ) = some τ
  | .prim _ => rfl
  | .fn a b => by
      simp [Ty.toRTy, LakeJs.Layout.instRTy, instRTy_toRTy rep a, instRTy_toRTy rep b]
  | .primCovariant s => by simp [Ty.toRTy, LakeJs.Layout.instRTy, instCov_toRTyCov rep s]
  | .enum _ => rfl
  | .record fs => by simp [Ty.toRTy, LakeJs.Layout.instRTy, instA2_toRTyA2 rep fs]
  | .taggedUnion l => by simp [Ty.toRTy, LakeJs.Layout.instRTy, instTU_toRTyTU rep l]
  | .recTaggedUnion _ h => by simp [Ty.toRTy, LakeJs.Layout.instRTy, h]
  | .recObject _ h => by simp [Ty.toRTy, LakeJs.Layout.instRTy, h]
  | .recAlias _ h => by simp [Ty.toRTy, LakeJs.Layout.instRTy, h]
  | .mutualRecursiveFamily _ h => by simp [Ty.toRTy, LakeJs.Layout.instRTy, h]

/-- The same, for an invariant type former. -/
theorem instCov_toRTyCov (rep : Nat → Option Ty) :
    ∀ s : LeanPrimTyCovariant Ty, LakeJs.Layout.instCov rep (Ty.toRTyCov s) = some s
  | .array a => by simp [Ty.toRTyCov, LakeJs.Layout.instCov, instRTy_toRTy rep a]
  | .list a => by simp [Ty.toRTyCov, LakeJs.Layout.instCov, instRTy_toRTy rep a]
  | .task a => by simp [Ty.toRTyCov, LakeJs.Layout.instCov, instRTy_toRTy rep a]
  | .promise a => by simp [Ty.toRTyCov, LakeJs.Layout.instCov, instRTy_toRTy rep a]
  | .thunk a => by simp [Ty.toRTyCov, LakeJs.Layout.instCov, instRTy_toRTy rep a]
  | .lazy a => by simp [Ty.toRTyCov, LakeJs.Layout.instCov, instRTy_toRTy rep a]

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

/-- The same, for the fields of a record. -/
theorem instA2_toRTyA2 (rep : Nat → Option Ty) :
    ∀ fs : LeanRecordSchema Ty, LakeJs.Layout.instA2 rep (Ty.toRTyA2 fs) = some fs
  | ⟨a, b, rest⟩ => by
      simp [Ty.toRTyA2, LakeJs.Layout.instA2, instRTy_toRTy rep a, instRTy_toRTy rep b,
        instList_toRTyList rep rest]

/-- The same, for the fields of a constructor that has at least one. -/
theorem instNE_toRTyNE (rep : Nat → Option Ty) :
    ∀ f : NonEmptyList Ty, LakeJs.Layout.instNE rep (Ty.toRTyNE f) = some f
  | ⟨a, as⟩ => by
      simp [Ty.toRTyNE, LakeJs.Layout.instNE, instRTy_toRTy rep a,
        instList_toRTyList rep as]

/-- The same, for the constructors of a tagged union. -/
theorem instTU_toRTyTU (rep : Nat → Option Ty) :
    ∀ l : LeanTaggedUnionSchema Ty, LakeJs.Layout.instTU rep (Ty.toRTyTU l) = some l
  | .payloadFirst f n r => by
      simp [Ty.toRTyTU, LakeJs.Layout.instTU, instNE_toRTyNE rep f,
        instList_toRTyList rep n, instCtors_toRTyCtors rep r]
  | .skip rest => by simp [Ty.toRTyTU, LakeJs.Layout.instTU, instCP_toRTyCP rep rest]

/-- The same, for the constructors that follow a field-less one. -/
theorem instCP_toRTyCP (rep : Nat → Option Ty) :
    ∀ c : CtorsWithPayload Ty, LakeJs.Layout.instCP rep (Ty.toRTyCP c) = some c
  | .here f r => by
      simp [Ty.toRTyCP, LakeJs.Layout.instCP, instNE_toRTyNE rep f,
        instCtors_toRTyCtors rep r]
  | .skip rest => by simp [Ty.toRTyCP, LakeJs.Layout.instCP, instCP_toRTyCP rep rest]

end

end LakeJs

end
