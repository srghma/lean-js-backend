module

public import LakeJs.Ty
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

`Ty.wf` runs all four at every node of a whole type, and `WfTy` is the subtype of the
types that pass — the type of a type the backend can actually compile.  `Ty.not_wf_selfLoop`
and `Ty.not_wf_recObject_selfField` below are the two degenerate recursive declarations,
written out and refuted.
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
  | .recTaggedUnion l => some l
  | _ => none

/-- The `LeanRecordSchema` of a type that is a recursive record. -/
def Ty.recObjectSchema? : Ty → Option (LeanRecordSchema RTy)
  | .recObject fs => some fs
  | _ => none

/-- The `LeanMutualRecFamily` of a type that is a member of a mutual family. -/
def Ty.mutualRecFamily? : Ty → Option (LeanMutualRecFamily RTy)
  | .mutualRecursiveFamily f => some f
  | _ => none

/-- The enum this payload describes. -/
def LeanEnumSchema.toTy (s : LeanEnumSchema) : Ty := .enum s

/-- The record with these fields. -/
def LeanRecordSchema.toTy (fs : LeanRecordSchema Ty) : Ty := .record fs

/-- The tagged union with these constructors. -/
def LeanTaggedUnionSchema.toTy (l : LeanTaggedUnionSchema Ty) : Ty := .taggedUnion l

/-- The recursive tagged union with these constructors. -/
def LeanTaggedUnionSchema.toTy (l : LeanTaggedUnionSchema RTy) : Ty :=
  .recTaggedUnion l

/-- The recursive record with these fields. -/
def LeanRecordSchema.toTy (fs : LeanRecordSchema RTy) : Ty := .recObject fs

/-- The member of the family this payload describes. -/
def LeanMutualRecFamily.toTy (f : LeanMutualRecFamily RTy) : Ty :=
  .mutualRecursiveFamily f

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
  | .fnTy s => .fnTy (Ty.toRTyFn s)
  | .primCovariant s => .primCovariant (Ty.toRTyCov s)
  | .enum s => .enum s
  | .record fs => .record (Ty.toRTyA2 fs)
  | .taggedUnion l => .taggedUnion (Ty.toRTyTU l)
  | .recTaggedUnion l => .recTaggedUnion l
  | .recObject fs => .recObject fs
  | .recAlias b => .recAlias b
  | .mutualRecursiveFamily f => .mutualRecursiveFamily f

/-- `Ty.toRTy`, on a function type. -/
def Ty.toRTyFn : TyFn Ty → TyFn RTy
  | .fn ps r => .fn (Ty.toRTyList ps) (Ty.toRTy r)
  | .fn_returnsProd ps r rs =>
      .fn_returnsProd (Ty.toRTyList ps) (Ty.toRTy r) (Ty.toRTyList rs)

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
  | .typeParam => rfl
  | .fnTy s => by simp [Ty.toRTy, LakeJs.Layout.instRTy, instFn_toRTyFn rep s]
  | .primCovariant s => by simp [Ty.toRTy, LakeJs.Layout.instRTy, instCov_toRTyCov rep s]
  | .enum _ => rfl
  | .record fs => by simp [Ty.toRTy, LakeJs.Layout.instRTy, instA2_toRTyA2 rep fs]
  | .taggedUnion l => by simp [Ty.toRTy, LakeJs.Layout.instRTy, instTU_toRTyTU rep l]
  | .recTaggedUnion _ => rfl
  | .recObject _ => rfl
  | .recAlias _ => rfl
  | .mutualRecursiveFamily _ => rfl

/-- The same, for a function type. -/
theorem instFn_toRTyFn (rep : Nat → Option Ty) :
    ∀ s : TyFn Ty, LakeJs.Layout.instFn rep (Ty.toRTyFn s) = some s
  | .fn ps r => by
      simp [Ty.toRTyFn, LakeJs.Layout.instFn, instList_toRTyList rep ps,
        instRTy_toRTy rep r]
  | .fn_returnsProd ps r rs => by
      simp [Ty.toRTyFn, LakeJs.Layout.instFn, instList_toRTyList rep ps,
        instRTy_toRTy rep r, instList_toRTyList rep rs]

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

/-! ## Which members of a recursive declaration it mentions -/

mutual

/-- The members of the enclosing recursive declaration that this type mentions.  A
    *nested* recursive shape is not looked into: its `.self`s are its own. -/
def Ty.RTy.selfIdxs : RTy → List Nat
  | .self i => [i]
  | .fnTy s => RTy.selfIdxsFn s
  | .primCovariant s => RTy.selfIdxsCov s
  | .record fs => RTy.selfIdxsA2 fs
  | .taggedUnion l => RTy.selfIdxsTU l
  | _ => []

/-- `RTy.selfIdxs`, on a function type. -/
def Ty.RTy.selfIdxsFn : TyFn RTy → List Nat
  | .fn ps r => RTy.selfIdxsList ps ++ RTy.selfIdxs r
  | .fn_returnsProd ps r rs =>
      RTy.selfIdxsList ps ++ RTy.selfIdxs r ++ RTy.selfIdxsList rs

/-- `RTy.selfIdxs`, on an invariant type former. -/
def Ty.RTy.selfIdxsCov : LeanPrimTyCovariant RTy → List Nat
  | .array a | .list a | .task a | .promise a | .thunk a | .lazy a => RTy.selfIdxs a

/-- `RTy.selfIdxs`, on a list of types. -/
def Ty.RTy.selfIdxsList : List RTy → List Nat
  | [] => []
  | t :: ts => RTy.selfIdxs t ++ RTy.selfIdxsList ts

/-- `RTy.selfIdxs`, on the constructors of a layout. -/
def Ty.RTy.selfIdxsCtors : List (List RTy) → List Nat
  | [] => []
  | fs :: l => RTy.selfIdxsList fs ++ RTy.selfIdxsCtors l

/-- `RTy.selfIdxs`, on the fields of a record. -/
def Ty.RTy.selfIdxsA2 : LeanRecordSchema RTy → List Nat
  | ⟨a, b, rest⟩ => RTy.selfIdxs a ++ RTy.selfIdxs b ++ RTy.selfIdxsList rest

/-- `RTy.selfIdxs`, on the fields of a constructor that has at least one. -/
def Ty.RTy.selfIdxsNE : NonEmptyList RTy → List Nat
  | ⟨a, as⟩ => RTy.selfIdxs a ++ RTy.selfIdxsList as

/-- `RTy.selfIdxs`, on the constructors of a tagged union. -/
def Ty.RTy.selfIdxsTU : LeanTaggedUnionSchema RTy → List Nat
  | .payloadFirst f n r => RTy.selfIdxsNE f ++ RTy.selfIdxsList n ++ RTy.selfIdxsCtors r
  | .skip rest => RTy.selfIdxsCP rest

/-- `RTy.selfIdxs`, on the constructors that follow a field-less one. -/
def Ty.RTy.selfIdxsCP : CtorsWithPayload RTy → List Nat
  | .here f r => RTy.selfIdxsNE f ++ RTy.selfIdxsCtors r
  | .skip rest => RTy.selfIdxsCP rest

end

/-- The members of its family that one member mentions. -/
def Ty.FamMember.selfIdxs : FamMember → List Nat
  | .ctors l => RTy.selfIdxsTU l
  | .record fs => RTy.selfIdxsA2 fs
  | .alias b => RTy.selfIdxs b

/-- Does this member mention the declaration it belongs to at all? -/
def Ty.FamMember.hasSelf : FamMember → Bool
  | .ctors l => RTy.hasSelfTU l
  | .record fs => RTy.hasSelfA2 fs
  | .alias b => RTy.hasSelf b

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
  | .fnTy s => RTy.inhabWithFn avail s
  | .primCovariant s => RTy.inhabWithCov avail s
  | .enum _ => true
  | .record fs => RTy.inhabWithA2 avail fs
  | .taggedUnion l => RTy.inhabWithTU avail l
  -- a nested recursive shape opens a scope of its own, so it mentions no member of
  -- ours; whether *it* has values is checked where it is
  | .recTaggedUnion _ => true
  | .recObject _ => true
  | .recAlias _ => true
  | .mutualRecursiveFamily _ => true

/-- `RTy.inhabWith`, on a function type. -/
def Ty.RTy.inhabWithFn (avail : List Bool) : TyFn RTy → Bool
  -- a function needs no argument to exist, only a result
  | .fn _ r => RTy.inhabWith avail r
  | .fn_returnsProd _ r rs => RTy.inhabWith avail r && RTy.inhabWithAll avail rs

/-- `RTy.inhabWith`, on an invariant type former. -/
def Ty.RTy.inhabWithCov (avail : List Bool) : LeanPrimTyCovariant RTy → Bool
  -- the empty array and the empty list hold nothing
  | .array _ | .list _ => true
  | .task a | .promise a | .thunk a | .lazy a => RTy.inhabWith avail a

/-- `RTy.inhabWith`, on the fields of one constructor: it needs all of them. -/
def Ty.RTy.inhabWithAll (avail : List Bool) : List RTy → Bool
  | [] => true
  | t :: ts => RTy.inhabWith avail t && RTy.inhabWithAll avail ts

/-- `RTy.inhabWith`, on the constructors of a layout: it needs one of them. -/
def Ty.RTy.inhabWithSome (avail : List Bool) : List (List RTy) → Bool
  | [] => false
  | fs :: l => RTy.inhabWithAll avail fs || RTy.inhabWithSome avail l

/-- `RTy.inhabWith`, on the fields of a record: it needs all of them. -/
def Ty.RTy.inhabWithA2 (avail : List Bool) : LeanRecordSchema RTy → Bool
  | ⟨a, b, rest⟩ =>
      RTy.inhabWith avail a && RTy.inhabWith avail b && RTy.inhabWithAll avail rest

/-- `RTy.inhabWith`, on the fields of a constructor that has at least one. -/
def Ty.RTy.inhabWithNE (avail : List Bool) : NonEmptyList RTy → Bool
  | ⟨a, as⟩ => RTy.inhabWith avail a && RTy.inhabWithAll avail as

/-- `RTy.inhabWith`, on the constructors of a tagged union: it needs one of them. -/
def Ty.RTy.inhabWithTU (avail : List Bool) : LeanTaggedUnionSchema RTy → Bool
  | .payloadFirst f n r =>
      RTy.inhabWithNE avail f || RTy.inhabWithAll avail n || RTy.inhabWithSome avail r
  -- the first constructor has no fields at all, so it can always be built
  | .skip _ => true

end

/-- `RTy.inhabWith`, on one member of a family. -/
def Ty.FamMember.inhabWith (avail : List Bool) : FamMember → Bool
  | .ctors l => RTy.inhabWithTU avail l
  | .record fs => RTy.inhabWithA2 avail fs
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

/-! ## Is a payload one that describes a type?

The counting conditions are in the payloads' types, so what is left to check of one
payload is that it *is* recursive, that its recursive occurrences point at members it
has, and that the type it describes has values. -/

/-- A recursive tagged union mentions itself — and only itself, since it has one
    member — and has a constructor that can be built without a value of its own type, so
    that it has values at all: `inductive Bad | l : Bad → Bad | r : Bad → Bad` has
    none. -/
def LeanTaggedUnionSchema.wf (l : LeanTaggedUnionSchema RTy) : Bool :=
  RTy.hasSelfTU l.ctors && selfIdxsOk 1 (RTy.selfIdxsTU l.ctors)
    && famAllInhabited [.ctors l.ctors]

/-- A recursive record mentions itself, points only at itself, and has values:
    `structure S where s : S; n : Nat` has none. -/
def LeanRecordSchema.wf (fs : LeanRecordSchema RTy) : Bool :=
  RTy.hasSelfA2 fs.fields && selfIdxsOk 1 (RTy.selfIdxsA2 fs.fields)
    && famAllInhabited [.record fs.fields]

/-- A recursive newtype mentions itself — otherwise the wrapper is erased into its field
    and there is no `recAlias` at all — and does so guardedly, so that the equation it
    stands for has a solution: `recAlias ⟨.self 0⟩` is `T = T`, which no value
    satisfies, while `recAlias ⟨.array (.self 0)⟩` is the empty array and more. -/
def RTy.wf (b : RTy RTy) : Bool :=
  RTy.hasSelf b.body && selfIdxsOk 1 (RTy.selfIdxs b.body)
    && famAllInhabited [.alias b.body]

/-- A family mentions only members it has, is a family rather than a `mutual` block of
    unrelated declarations — each member reaches every member — and every member of it
    has values. -/
def LeanMutualRecFamily.wf (f : LeanMutualRecFamily RTy) : Bool :=
  f.members.all (fun m => selfIdxsOk f.members.length (Ty.FamMember.selfIdxs m))
    && famStronglyConnected f.members && famAllInhabited f.members

/-! ## Well-formedness of a whole type

Each recursive shape of a type is checked by the predicate of its payload, and so is
each shape nested in it. -/

mutual

/-- Does every recursive shape in this closed type describe a type that exists? -/
def Ty.wf : Ty → Bool
  | .prim _ => true
  | .typeParam => true
  | .fnTy s => Ty.wfFn s
  | .primCovariant s => Ty.wfCov s
  | .enum _ => true
  | .record fs => Ty.wfA2 fs
  | .taggedUnion l => Ty.wfTU l
  | .recTaggedUnion ⟨l⟩ => LeanTaggedUnionSchema.wf ⟨l⟩ && RTy.wfTU l
  | .recObject ⟨fs⟩ => LeanRecordSchema.wf ⟨fs⟩ && RTy.wfA2 fs
  | .recAlias ⟨b⟩ => RTy.wf ⟨b⟩ && RTy.wf b
  | .mutualRecursiveFamily f => LeanMutualRecFamily.wf f && Ty.FamMember.wfFamily f

/-- `Ty.wf`, on a function type. -/
def Ty.wfFn : TyFn Ty → Bool
  | .fn ps r => Ty.wfList ps && Ty.wf r
  | .fn_returnsProd ps r rs => Ty.wfList ps && Ty.wf r && Ty.wfList rs

/-- `Ty.wf`, on an invariant type former. -/
def Ty.wfCov : LeanPrimTyCovariant Ty → Bool
  | .array a | .list a | .task a | .promise a | .thunk a | .lazy a => Ty.wf a

/-- `Ty.wf`, on a list of closed types. -/
def Ty.wfList : List Ty → Bool
  | [] => true
  | t :: ts => Ty.wf t && Ty.wfList ts

/-- `Ty.wf`, on the constructors of a closed layout. -/
def Ty.wfCtors : List (List Ty) → Bool
  | [] => true
  | fs :: l => Ty.wfList fs && Ty.wfCtors l

/-- `Ty.wf`, on the fields of a record. -/
def Ty.wfA2 : LeanRecordSchema Ty → Bool
  | ⟨a, b, rest⟩ => Ty.wf a && Ty.wf b && Ty.wfList rest

/-- `Ty.wf`, on the fields of a constructor that has at least one. -/
def Ty.wfNE : NonEmptyList Ty → Bool
  | ⟨a, as⟩ => Ty.wf a && Ty.wfList as

/-- `Ty.wf`, on the constructors of a tagged union. -/
def Ty.wfTU : LeanTaggedUnionSchema Ty → Bool
  | .payloadFirst f n r => Ty.wfNE f && Ty.wfList n && Ty.wfCtors r
  | .skip rest => Ty.wfCP rest

/-- `Ty.wf`, on the constructors that follow a field-less one. -/
def Ty.wfCP : CtorsWithPayload Ty → Bool
  | .here f r => Ty.wfNE f && Ty.wfCtors r
  | .skip rest => Ty.wfCP rest

/-- `Ty.wf`, one layer down: this type may mention the declaration it sits in. -/
def Ty.RTy.wf : RTy → Bool
  | .self _ => true
  | .prim _ => true
  | .typeParam => true
  | .fnTy s => RTy.wfFn s
  | .primCovariant s => RTy.wfCov s
  | .enum _ => true
  | .record fs => RTy.wfA2 fs
  | .taggedUnion l => RTy.wfTU l
  | .recTaggedUnion ⟨l⟩ => LeanTaggedUnionSchema.wf ⟨l⟩ && RTy.wfTU l
  | .recObject ⟨fs⟩ => LeanRecordSchema.wf ⟨fs⟩ && RTy.wfA2 fs
  | .recAlias ⟨b⟩ => RTy.wf ⟨b⟩ && RTy.wf b
  | .mutualRecursiveFamily f => LeanMutualRecFamily.wf f && Ty.FamMember.wfFamily f

/-- `RTy.wf`, on a function type. -/
def Ty.RTy.wfFn : TyFn RTy → Bool
  | .fn ps r => RTy.wfList ps && RTy.wf r
  | .fn_returnsProd ps r rs => RTy.wfList ps && RTy.wf r && RTy.wfList rs

/-- `RTy.wf`, on an invariant type former. -/
def Ty.RTy.wfCov : LeanPrimTyCovariant RTy → Bool
  | .array a | .list a | .task a | .promise a | .thunk a | .lazy a => RTy.wf a

/-- `RTy.wf`, on a list of types. -/
def Ty.RTy.wfList : List RTy → Bool
  | [] => true
  | t :: ts => RTy.wf t && RTy.wfList ts

/-- `RTy.wf`, on the constructors of a layout. -/
def Ty.RTy.wfCtors : List (List RTy) → Bool
  | [] => true
  | fs :: l => RTy.wfList fs && RTy.wfCtors l

/-- `RTy.wf`, on the fields of a record. -/
def Ty.RTy.wfA2 : LeanRecordSchema RTy → Bool
  | ⟨a, b, rest⟩ => RTy.wf a && RTy.wf b && RTy.wfList rest

/-- `RTy.wf`, on the fields of a constructor that has at least one. -/
def Ty.RTy.wfNE : NonEmptyList RTy → Bool
  | ⟨a, as⟩ => RTy.wf a && RTy.wfList as

/-- `RTy.wf`, on the constructors of a tagged union. -/
def Ty.RTy.wfTU : LeanTaggedUnionSchema RTy → Bool
  | .payloadFirst f n r => RTy.wfNE f && RTy.wfList n && RTy.wfCtors r
  | .skip rest => RTy.wfCP rest

/-- `RTy.wf`, on the constructors that follow a field-less one. -/
def Ty.RTy.wfCP : CtorsWithPayload RTy → Bool
  | .here f r => RTy.wfNE f && RTy.wfCtors r
  | .skip rest => RTy.wfCP rest

/-- `RTy.wf`, on one member of a family. -/
def Ty.FamMember.wf : FamMember → Bool
  | .ctors l => Ty.RTy.wfTU l
  | .record fs => Ty.RTy.wfA2 fs
  | .alias b => Ty.RTy.wf b

/-- `RTy.wf`, on the members of a family. -/
def Ty.FamMember.wfList : List FamMember → Bool
  | [] => true
  | m :: ms => Ty.FamMember.wf m && Ty.FamMember.wfList ms

/-- `RTy.wf`, on every member of a family. -/
def Ty.FamMember.wfFamily : LeanMutualRecFamily RTy → Bool
  | .selectedThenMore before current next after =>
      Ty.FamMember.wfList before && Ty.FamMember.wf current && Ty.FamMember.wf next
        && Ty.FamMember.wfList after
  | .selectedLast first before current =>
      Ty.FamMember.wf first && Ty.FamMember.wfList before && Ty.FamMember.wf current

end

/-- A **well-formed type**: a `Ty` every recursive shape of which describes a type that
    exists.  The counting conditions are already true of every `Ty`, so this is the
    whole of what the backend asks of a type it is handed. -/
structure WfTy where
  /-- The type. -/
  ty : Ty
  /-- Its recursive shapes mention themselves, point only at members they have, and
      describe types that have values. -/
  wf : Ty.wf ty = true := by decide

namespace WfTy

/-- Two well-formed types are equal when their types are. -/
theorem ext : ∀ {a b : WfTy}, a.ty = b.ty → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance : DecidableEq WfTy := fun a b =>
  decidable_of_iff (a.ty = b.ty) ⟨WfTy.ext, fun h => h ▸ rfl⟩

end WfTy

/-! ## The degenerate recursive declarations, refuted

These are the two declarations Lean accepts and no compiled program can hold a value
of.  They are `Ty`s — nothing about their *shape* is wrong — and `Ty.wf` refuses
them. -/

/-- `inductive Bad | mk : Bad → Bad` is read as the recursive newtype whose body is the
    declaration itself, i.e. as the equation `T = T`.  No value satisfies it, so it is
    not well formed, and there is no `WfTy` for it. -/
theorem Ty.not_wf_selfLoop : Ty.wf (.recAlias ⟨.self 0⟩) = false := by decide

/-- `structure Worse where w : Worse; n : Nat` is the same mistake one shape along: a
    record needs *all* of its fields, and one of them is the record itself. -/
theorem Ty.not_wf_recObject_selfField :
    Ty.wf (.recObject ⟨⟨.self 0, .prim .nat, []⟩⟩) = false := by decide

/-- A recursive newtype that does *not* mention itself is not one either: its wrapper is
    erased into its field, and the type it describes is just that field. -/
theorem Ty.not_wf_recAlias_noSelf : Ty.wf (.recAlias ⟨.prim .nat⟩) = false := by decide

/-- A guarded recursive newtype — `structure Rose where kids : Array Rose` — *is* well
    formed: the empty array holds no `Rose`, so a `Rose` can be built. -/
theorem Ty.wf_recAlias_array : Ty.wf (.recAlias ⟨.array (.self 0)⟩) = true := by decide

/-- And so is a recursive sum with a base case: `inductive T | leaf | node : T → T → T`. -/
theorem Ty.wf_recTaggedUnion_tree :
    Ty.wf (.recTaggedUnion ⟨.skip (.here ⟨.self 0, [.self 0]⟩ [])⟩) = true := by decide

end LakeJs

end
