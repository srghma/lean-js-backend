module

public import LakeJs.Ty
public import LakeJs.TySchema

@[expose] public section

/-!
# The `Ty` of each proof-carrying specimen of `ExamplesProofFields.Shapes`

For every one of the seven shapes, this file writes down the type the backend gives the
proof-carrying Lean declaration, and checks by `decide` that it is well formed.  In every
case the `Ty` is the `Ty` of the **erased twin**: the proof fields contribute nothing, and
no schema mentions them.

Two of the seven are shape-*changing*, and they are the reason the question matters:

* `Rose` is written with two fields but has one runtime field, so it is a `recAlias`
  (a newtype) rather than a `recObject`;
* `Status` is written with three constructors carrying two proof fields between them,
  and is an `enum` of three constructors carrying nothing.

The last section adds the collapses that go one step further: a record with a single
surviving field is a newtype, a two-constructor sum with no surviving field is a
`Ty.bool`, and a declaration with nothing left at all has no `Ty` — it is erased.
-/

namespace ExamplesProofFields

open LakeJs

/-! ## 1. `Status` — `enum` -/

/-- `inductive Status (n : Nat) | ok | warn (h : n > 0) | error (h1 …) (h2 …)`:
    three constructors, no runtime field, numbered from `0`. -/
def statusTy : Ty := .enum ⟨0, 0⟩

example : statusTy.enumSchema?.map LeanEnumSchema.nOfConstructors = some 3 := by decide

/-! ## 2. `Window` — `record` -/

/-- `structure Window (cap) where lo hi : Nat; hlo : lo ≤ hi; hcap : hi ≤ cap`:
    the two proofs are gone, two `Nat` fields remain. -/
def windowTy : Ty := .record ⟨.prim .nat, .prim .nat, []⟩

example : windowTy.recordSchema?.map LeanRecordSchema.length = some 2 := by decide

/-! ## 3. `Reading` — `taggedUnion` -/

/-- `inductive Reading (cap) | missing (h : 0 < cap) | value (v : Nat) (h : v ≤ cap)`:
    `[[], [nat]]` — the same runtime type as `Option Nat`. -/
def readingTy : Ty := .taggedUnion (.skip (.here ⟨.prim .nat, []⟩ []))

example : readingTy = Ty.option (.prim .nat) := rfl

example : readingTy.taggedUnionSchema?.map LeanTaggedUnionSchema.toList
    = some [[], [Ty.prim .nat]] := rfl

/-! ## 4. `NTree` — `recTaggedUnion` -/

/-- `inductive NTree | leaf | node (n : Nat) (h : 0 < n) (l r : NTree)`:
    `[[], [nat, self 0, self 0]]`. -/
def ntreeSchema : LeanTaggedUnionSchema RTy :=
  .skip (.here ⟨.prim .nat, [.self 0, .self 0]⟩ [])

def ntreeTy : Ty := .recTaggedUnion ntreeSchema

example : RTy.wf (.recTaggedUnion ntreeSchema) = true := by decide

example : ntreeSchema.toList.map List.length = [0, 3] := by decide

/-! ## 5. `Tag` — `recObject` -/

/-- `structure Tag where n : Nat; h : 0 < n; kids : Array Tag`: two runtime fields. -/
def tagSchema : LeanRecordSchema RTy := ⟨.prim .nat, .array (.self 0), []⟩

def tagTy : Ty := .recObject tagSchema

example : RTy.wf (.recObject tagSchema) = true := by decide

example : tagSchema.length = 2 := by decide

/-! ## 6. `Rose` — `recAlias`, although it is written as a two-field structure -/

/-- `structure Rose (cap) where kids : Array (Rose cap); h : 0 < cap`: one runtime
    field, so the wrapper is erased and a `Rose` is an array of arrays of … -/
def roseTy : Ty := .recAlias (.array (.self 0))

example : RTy.wf (.recAlias (.array (.self 0))) = true := by decide

/-- The shape it is *not*: `Rose`'s source has two fields, but a `recObject` of two
    fields needs two of them to survive erasure, and here only one does. -/
example : roseTy ≠ tagTy := by
  intro h
  exact Ty.noConfusion h

/-! ## 7. `PNode` / `PForest` — `mutualRecursiveFamily` -/

/-- `PNode`: a label and the children; the proof field `h : label < cap` is gone. -/
def pnodeMember : Ty.FamMember := .record ⟨.prim .nat, .self 1, []⟩

/-- `PForest`: `nil` (whose proof field is gone, leaving a field-less constructor), or a
    node and a tail. -/
def pforestMember : Ty.FamMember := .ctors (.skip (.here ⟨.self 0, [.self 1]⟩ []))

def pFamily : List Ty.FamMember := [pnodeMember, pforestMember]

example : famStronglyConnected pFamily = true := by decide

example : (LeanMutualRecFamily.ofMembers? pFamily 0).map famWf = some true := by decide

/-- `PNode`: member `0` of the family. -/
def pnodeTy : Ty := .mutualRecursiveFamily (.selectedThenMore [] pnodeMember pforestMember [])

/-- `PForest`: member `1` of the same family. -/
def pforestTy : Ty := .mutualRecursiveFamily (.selectedLast pnodeMember [] pforestMember)

example : pnodeTy.mutualRecFamily?.map LeanMutualRecFamily.memberIdx = some 0 := rfl
example : pforestTy.mutualRecFamily?.map LeanMutualRecFamily.memberIdx = some 1 := rfl

example : pnodeMember.toCtors.map List.length = [2] := by decide
example : pforestMember.toCtors.map List.length = [0, 2] := by decide

/-! ## The collapses proof fields cause

Adding a proof field never changes a type.  Turning a *data* field into a proof always
can, because the schemas count runtime fields and runtime constructors:

| Lean                                                        | `Ty`                  |
| :---------------------------------------------------------- | :-------------------- |
| `structure Bounded (cap) where v : Nat; h : v ≤ cap`         | `.prim .nat` — newtype |
| `inductive Parity (n) \| even (h : n % 2 = 0) \| odd (h : …)` | `.prim .bool`         |
| `structure Proven (n) where h : 0 < n`                       | *none* — erased       |
| `structure Rose (cap) where kids : Array (Rose cap); h : …`  | `.recAlias …`          |

The first three are the three sizes below the smallest shape each schema admits, and the
type language makes them unwritable on purpose: `LeanRecordSchema` needs two fields,
`LeanEnumSchema` three constructors, and there is no unit type at all. -/

/-- `structure Bounded (cap : Nat) where v : Nat; h : v ≤ cap` — a newtype: its `Ty` is
    its surviving field's own `Ty`, indistinguishable from a bare `Nat`. -/
def boundedTy : Ty := .prim .nat

/-- `inductive Parity (n : Nat) | even (h : n % 2 = 0) | odd (h : n % 2 = 1)` — two
    constructors, neither with a runtime field: a boolean, not a two-case enum. -/
def parityTy : Ty := .prim .bool

/-! There is no `Ty` for `structure Proven (n : Nat) where h : 0 < n`: a value of it
carries nothing, so it is erased where it is a parameter, an argument or a field — and
the type language has no unit type to give it. -/

end ExamplesProofFields
