module

public import LakeJs.Ty
public import LakeJs.TySchema
public import LakeJs.TyPretty

@[expose] public section

/-!
# Worked examples: which Lean declaration becomes which `Ty`

Every definition below is checked when this file is elaborated, and every `example` is
closed by `rfl` or `decide`, so this file doubles as the test suite for the shapes of
`Ty` and for the well-formedness conditions of `LakeJs.TySchema`.

The type language carries **no names**: a constructor is a position in the list of
constructors and a field a position in the list of fields.  So the Lean declaration each
definition is named after is written in its docstring, and the `Ty` next to it is all the
backend keeps of it.

Two kinds of condition appear here.  One is carried by the *type* — `Ty.enum` takes a
proof that it has a constructor, so `.enum 0 …` does not elaborate at all.  The rest are
shape conditions, decided by `Ty.wf`; an ill-formed type is then a `Ty` that exists but
is rejected, and the examples show it being rejected.
-/

namespace LakeJs.TyExamples

open LakeJs.Ty

/-! ## Primitives

`BitVec 0` has exactly one value, so it is a unit type: `Ty.bitvec` takes a proof that
its width is positive, supplied by `by decide`, and `.bitvec 0` does not elaborate.

```lean
def bad : Ty := .bitvec 0   -- error: `decide` proved `0 < 0` is false
```

Every terminal type is a `LeanPrimTy`, and `Ty.nat`, `Ty.bitvec n`, … are abbreviations
for `Ty.prim`. -/

/-- `BitVec 32`. -/
def bv32 : Ty := .bitvec 32

example : Ty.bitvec 32 = Ty.prim (.bitvec 32) := rfl
example : Ty.wf bv32 = true := by decide
example : LeanPrimTy.isNumberConfigurable (.bitvec 16) = false := by decide
example : LeanPrimTy.isNumberConfigurable .nat = true := by decide

/-! ## Enum -/

/-- `inductive Direction | north | south | east | west` — four constructors, none with a
    field, numbered from `0`. -/
def direction : Ty := .enum 4 (shift := 0)

example : Ty.wf direction = true := by decide
example : direction.layout? = some [[], [], [], []] := rfl

/-- `Ordering` is the enum whose numbering starts at `-1`, so it prints as `-1 | 0 | 1`
    — the numbers the comparison functions of the runtime answer with. -/
example : Ty.ordering = .enum 3 (shift := -1) := rfl

/-- `Unit` is the enum with a single constructor: one value, `{ tag: 0 }`.  It is *not*
    erased by the type language — erasure happens to proofs and to types, one level up,
    when a declaration's fields are read. -/
def unitTy : Ty := .enum 1 (shift := 0)

example : Ty.wf unitTy = true := by decide

/-! A type with **no** constructors has no values, and is not writable: the proof
`0 < 0` that `.enum 0 …` needs cannot be given. -/
example : ¬ (0 < 0) := by decide

/-! ## Record -/

/-- `structure Point where x, y : Float`. -/
def point : Ty := .record [.float, .float]

/-- Nesting works: `structure Point3 where p : Point; z : Float`. -/
def point3 : Ty := .record [point, .float]

example : Ty.wf point = true := by decide
example : Ty.wf point3 = true := by decide
example : point3.layout? = some [[point, .float]] := rfl

/-! A record has at least two fields.  `structure Wrapper where x : Nat` is a *newtype*:
its wrapper has no runtime representation, and its `Ty` is the field's own — so
`.record [.nat]` is a type nothing reads off a declaration, and `Ty.wf` rejects it. -/

/-- `structure Wrapper where x : Nat` *is* `Ty.nat`. -/
def wrapper : Ty := .nat

example : LeanRecordSchema.ok [Ty.nat] = false := by decide
example : Ty.wf (.record [.nat]) = false := by decide

/-! A field-less record would be a unit type, which is `enum 1`, not a record. -/
example : Ty.wf (.record []) = false := by decide

/-! ## Tagged union -/

/-- `Option Char`. -/
def optChar : Ty := .option .char

/-- `Float × Int64`, which is a one-constructor record. -/
def pair : Ty := .prod .float .int64

example : optChar = .taggedUnion [[], [.char]] := rfl
example : pair = .record [.float, .int64] := rfl
example : Ty.wf optChar = true := by decide
example : Ty.wf pair = true := by decide

/-! A tagged union none of whose constructors carries a field is an *enum*, and has to
be written as one; and a one-constructor tagged union is a record, a newtype or
`enum 1`. -/
example : LeanTaggedUnionSchema.ok [[], []] = false := by decide
example : LeanTaggedUnionSchema.ok [[], [.char]] = true := by decide
example : Ty.wf (.taggedUnion [[.nat]]) = false := by decide

/-! ## Recursive tagged union

`RTy.self 0` is an occurrence of the declaration being defined. -/

/-- `inductive MyList | nil | cons (hd : Int) (tl : MyList)`. -/
def myList : Ty := .recTaggedUnion [[], [.prim .int, .self 0]]

/-- `inductive Tree | leaf (kids : Array Tree) | node (v : Int) (kid : Tree)`: `leaf` is
    a base constructor even though it mentions the type, because an array may be
    empty. -/
def tree : Ty :=
  .recTaggedUnion [[.array (.self 0)], [.prim .int, .self 0]]

/-- `inductive Chain | stop | link (next : Option Chain)`: an `Option` guards a self
    occurrence just as an array does — and it is an ordinary `taggedUnion` inside the
    recursive shape, not a scope of its own, so its `.self 0` is still `Chain`. -/
def chain : Ty := .recTaggedUnion [[], [.taggedUnion [[], [.self 0]]]]

/-- A function *returning* the declared type is fine: `inductive Stream | done | step
    (head : Int) (tail : Nat → Stream)`. -/
def lazyStream : Ty :=
  .recTaggedUnion [[], [.prim .int, .fn [.prim .nat] (.self 0)]]

example : Ty.wfStrict myList = true := by decide
example : Ty.wfStrict tree = true := by decide
example : Ty.wfStrict chain = true := by decide
example : Ty.wfStrict lazyStream = true := by decide

/-! Rejected: not actually recursive — that is a `Ty.taggedUnion`. -/
example : LeanRecTaggedUnionSchema.ok [[], [.prim .int]] = false := by decide

/-! Rejected by the strict tier: not well founded.  Every constructor of
`inductive Bad | l : Bad → Bad | r : Bad → Bad` needs a value of the type, so the type
has none — Lean accepts the declaration, and the backend reads it, which is why this is
`strict` rather than `ok`. -/
example : LeanRecTaggedUnionSchema.ok [[.self 0], [.self 0]] = true := by decide
example : LeanRecTaggedUnionSchema.strict [[.self 0], [.self 0]] = false := by decide

/-! A `Thunk` is no guard either: forcing it has to produce a value of the type. -/
example : LeanRecTaggedUnionSchema.strict [[.thunk (.self 0)], [.self 0]] = false := by
  decide

/-! ## Recursive record -/

/-- `structure Tree where v : Int; kids : Array Tree`. -/
def treeRecord : Ty := .recObject [.prim .int, .array (.self 0)]

example : Ty.wfStrict treeRecord = true := by decide

/-! Rejected by the strict tier: `structure S where s : S; n : Nat` is uninhabited — the
self occurrence is unguarded. -/
example : LeanRecObjectSchema.strict [.self 0, .prim .nat] = false := by decide

/-! Rejected: a "recursive" record that never mentions itself is a `Ty.record`. -/
example : LeanRecObjectSchema.ok [.prim .int, .prim .nat] = false := by decide

/-! Rejected: a one-field recursive record is a newtype, i.e. a `Ty.recAlias`. -/
example : LeanRecObjectSchema.ok [.array (.self 0)] = false := by decide

/-! ## Recursive newtype

One constructor with exactly one field is a wrapper, and wrappers are erased: a `Rose`
is *not* `{ _kids: […] }` but simply `[…]`, an array of arrays of … -/

/-- `structure Rose where kids : Array Rose`. -/
def rose : Ty := .recAlias (.array (.self 0))

example : Ty.wfStrict rose = true := by decide

/-- An alias has no layout of its own; a value of it is a value of what its body
    unfolds to. -/
example : rose.layout? = none := rfl
example : rose.aliasUnfold? = some (.array rose) := rfl

/-! Rejected: `structure S where s : S` is the equation `S = S`, which no value
satisfies; and `structure S where s : Thunk S` is `S = Thunk S`, which is no better. -/
example : LeanRecAliasSchema.strict (.self 0) = false := by decide
example : LeanRecAliasSchema.strict (.thunk (.self 0)) = false := by decide
example : Ty.wfStrict (.recAlias (.self 0)) = false := by decide

/-! The structural tier accepts it: the backend does read `structure S where s : S` as
this type, so it is not a shape nothing produces — it is a type with no values. -/
example : Ty.wf (.recAlias (.self 0)) = true := by decide

/-! Rejected: a wrapper that does *not* mention itself is erased completely
(`structure Wrapper where x : Nat` is `Ty.nat`), so there is no `recAlias` for it. -/
example : LeanRecAliasSchema.ok (.prim .nat) = false := by decide

/-! ## Mutual families -/

/-- The "fake mutual" block

```lean
mutual
  inductive Color | red | blue
  inductive Shape | circle | box
end
```

No field of either type mentions the other, so the block is **two** `Ty.enum`s.  The
member graph has no edges, so it is not strongly connected. -/
def colorShapeMembers : List Ty.FamMember :=
  [.ctors [[], []], .ctors [[], []]]

example : famStronglyConnected colorShapeMembers = false := by decide
example : LeanMutualRecFamily.strict (colorShapeMembers, 0) = false := by decide

/-! The current translation nevertheless reads such a block as a family — every `mutual`
block is one — so the structural tier accepts it. -/
example : LeanMutualRecFamily.ok (colorShapeMembers, 0) = true := by decide

/-- A genuinely mutual block:

```lean
mutual
  inductive Exp | lit (n : Int) | block (s : Stm)
  inductive Stm | nop | ret (e : Exp)
end
``` -/
def expStmMembers : List Ty.FamMember :=
  [.ctors [[.prim .int], [.self 1]], .ctors [[], [.self 0]]]

/-- Member `0` (`Exp`) of that block. -/
def expTy : Ty := .mutualRecursiveFamily expStmMembers 0

/-- Member `1` (`Stm`) of the same block: the same members, a different index. -/
def stmTy : Ty := .mutualRecursiveFamily expStmMembers 1

example : Ty.wfStrict expTy = true := by decide
example : Ty.wfStrict stmTy = true := by decide

/-! There is no member `2`. -/
example : LeanMutualRecFamily.ok (expStmMembers, 2) = false := by decide

/-! A member may be a **newtype**, and is then an *alias member*: it has no object of
its own, and a value of it is a value of its single field.  Dropping `Stm.nop` from the
block above makes `Stm` such a member, and the block is still accepted. -/
def expStmAliasMembers : List Ty.FamMember :=
  [.ctors [[.prim .int], [.self 1]], .alias (.self 0)]

example : LeanMutualRecFamily.strict (expStmAliasMembers, 0) = true := by decide

/-! An alias member must still be buildable: a cycle of unguarded aliases has no values
at all. -/
def aliasCycleMembers : List Ty.FamMember := [.alias (.self 1), .alias (.self 0)]

example : famAllInhabited aliasCycleMembers = false := by decide
example : LeanMutualRecFamily.strict (aliasCycleMembers, 0) = false := by decide

/-! Guarded, the same cycle is fine: `A = Array B`, `B = Array A`, i.e. nested JS
arrays, and `[]` is a value of either. -/
def aliasCycleGuardedMembers : List Ty.FamMember :=
  [.alias (.array (.self 1)), .alias (.array (.self 0))]

example : LeanMutualRecFamily.strict (aliasCycleGuardedMembers, 0) = true := by decide

/-! One direction only (`Wrap` mentions `Inner`, never the other way round) is two
independent declarations, not a family. -/
def oneWayMembers : List Ty.FamMember :=
  [.ctors [[.self 1], [.prim .nat]], .ctors [[.prim .int], [.prim .nat]]]

example : famStronglyConnected oneWayMembers = false := by decide

/-! A block in which no member can be built is refused: every constructor of `B` needs
an `A` and every constructor of `A` needs a `B`. -/
def uninhabitedMembers : List Ty.FamMember :=
  [.ctors [[.self 1], [.self 1]], .ctors [[.self 0], [.self 0]]]

example : famStronglyConnected uninhabitedMembers = true := by decide
example : famAllInhabited uninhabitedMembers = false := by decide
example : LeanMutualRecFamily.strict (uninhabitedMembers, 0) = false := by decide

/-! Guarding makes the same block well founded: a field holding an `Array B` may hold
the empty one. -/
def guardedMembers : List Ty.FamMember :=
  [.ctors [[.array (.self 1), .prim .nat], [.prim .nat]], .ctors [[.self 0], [.prim .int]]]

example : famAllInhabited guardedMembers = true := by decide
example : LeanMutualRecFamily.strict (guardedMembers, 0) = true := by decide

/-! A single declaration is not a family: it is `recTaggedUnion`, `recObject` or
`recAlias`. -/
example : LeanMutualRecFamily.ok ([.ctors [[], [.prim .int, .self 0]]], 0) = false := by
  decide

/-! ## Functions

`def foo : Unit → Int → Int` — the `Unit` parameter carries nothing, so the outer
function takes no parameters at all. -/
def unitToIntToInt : Ty := .nullary (.fn [.int] .int)

example : unitToIntToInt = .fn [] (.fn [.int] .int) := rfl
example : Ty.wf unitToIntToInt = true := by decide

/-! ## A closed type, read inside a recursive declaration

`Ty.toRTy` embeds a closed type into the layer that may mention `.self`, and resolving
the recursive occurrences of the result gives the type back — whatever they resolve
to. -/
example : Ty.toRTy pair = RTy.record [.prim .float, .prim .int64] := rfl
example : LakeJs.Layout.instRTy (fun _ => none) (Ty.toRTy point) = some point :=
  instRTy_toRTy _ point

/-! ## Rendering

`Ty.pretty` is a one-line rendering, for debugging and error messages.  (A rendering
that mentions a `.self` prints its member number, which goes through `toString`, so it
is checked by the examples of `LakeJs.TyMetaExamples` rather than by `decide` here.) -/

example : pair.pretty = "(record float int64)" := by decide
example : optChar.pretty = "(taggedUnion ()|(char))" := by decide
example : point3.pretty = "(record (record float float) float)" := by decide

end LakeJs.TyExamples

end
