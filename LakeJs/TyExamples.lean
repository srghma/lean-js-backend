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

Two kinds of condition appear here, and the first kind is the larger one.

* **Carried by the type.**  Every *counting* condition is a condition on the payload's
  own type (`LakeJs.Schema`), so a degenerate shape does not elaborate at all: there is
  no way to write an enum of fewer than three constructors, a record of fewer than two
  fields, a tagged union of fewer than two constructors or with no field anywhere, or a
  mutual family of fewer than two members or with a member number out of range.  Where
  one of those used to be a *rejected* example, the comment below says so and the type
  is simply not written.
* **Decided by `Ty.wf`.**  What is left are the conditions on a whole type: a recursive
  shape mentions itself, its `.self`s point at members it has, the type has values, and
  a family is strongly connected.  Those are checks, and the examples show a type being
  accepted or rejected by them.
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

/-! ## Enum

An enum has **at least three** constructors: the smaller field-less sums are other
types.  `LeanEnumSchema` holds the number of constructors *beyond* those three, so
`⟨1, 0⟩` is four constructors numbered from `0`. -/

/-- `inductive Direction | north | south | east | west` — four constructors, none with a
    field, numbered from `0`. -/
def direction : Ty := .enum ⟨1, 0⟩

example : direction.enumSchema?.map LeanEnumSchema.nOfConstructors = some 4 := rfl
example : Ty.wf direction = true := by decide
example : direction.layout? = some [[], [], [], []] := rfl

/-- `Ordering` is the enum whose numbering starts at `-1`, so it prints as `-1 | 0 | 1`
    — the numbers the comparison functions of the runtime answer with. -/
example : Ty.ordering = .enum ⟨0, -1⟩ := rfl

/-! The three smaller field-less sums are **not** enums, and none of them is writable as
one:

* `inductive Empty` has no values, so no compiled declaration mentions it;
* `Unit` has a single value, which carries no information, and is erased before a type
  is built;
* `inductive Direction | north | south` is a *boolean*: the backend models a
  two-constructor field-less sum as `Ty.bool`, so it prints as `true`/`false`.

`Ty.enumOrBool?` is that decision, as a function. -/
example : Ty.enumOrBool? 0 = none := rfl
example : Ty.enumOrBool? 1 = none := rfl
example : Ty.enumOrBool? 2 = some Ty.bool := rfl
example : Ty.enumOrBool? 3 = some (.enum ⟨0, 0⟩) := rfl
example : Ty.enumOrBool? 4 = some direction := rfl

/-- A boolean has the layout of the two-constructor sum it is. -/
example : Ty.bool.layout? = some [[], []] := rfl

/-! ## Record

A record has **at least two** fields, and the type says so: `LeanRecordSchema` is a
first field, a second, and the rest. -/

/-- `structure Point where x, y : Float`. -/
def point : Ty := .record ⟨.float, .float, []⟩

/-- Nesting works: `structure Point3 where p : Point; z : Float`. -/
def point3 : Ty := .record ⟨point, .float, []⟩

example : Ty.wf point = true := by decide
example : Ty.wf point3 = true := by decide
example : point3.layout? = some [[point, .float]] := rfl

/-! A one-field declaration is a *newtype*: its wrapper has no runtime representation,
and its `Ty` is the field's own.  A field-less one is a unit type.  Neither is a
record, and neither is writable as one — `LeanRecordSchema.ofList?` is the partial
function that says so. -/

/-- `structure Wrapper where x : Nat` *is* `Ty.nat`. -/
def wrapper : Ty := .nat

example : LeanRecordSchema.ofList? [Ty.nat] = none := rfl
example : LeanRecordSchema.ofList? ([] : List Ty) = none := rfl
example : (LeanRecordSchema.ofList? [Ty.float, Ty.float]).map LeanRecordSchema.toTy
    = some point := rfl

/-! ## Tagged union

A tagged union has at least two constructors, at least one of which carries a field —
both by construction.  The encoding names the *first* constructor with fields, so
`Option α` is "a field-less constructor, then one carrying an `α`". -/

/-- `Option Char`. -/
def optChar : Ty := .option .char

/-- `Float × Int64`, which is a one-constructor record. -/
def pair : Ty := .prod .float .int64

example : optChar = .taggedUnion (.skip (.here ⟨.char, []⟩ [])) := rfl
example : optChar.layout? = some [[], [.char]] := rfl
example : pair = .record ⟨.float, .int64, []⟩ := rfl
example : Ty.wf optChar = true := by decide
example : Ty.wf pair = true := by decide

/-! A sum none of whose constructors carries a field is an enum or a boolean, and a
one-constructor sum is a record, a newtype or a unit type; neither is writable as a
tagged union. -/
example : LeanTaggedUnionSchema.ofList? ([[], []] : List (List Ty)) = none := rfl
example : LeanTaggedUnionSchema.ofList? ([[.nat]] : List (List Ty)) = none := rfl
example : (LeanTaggedUnionSchema.ofList? ([[], [.char]] : List (List Ty))).map
    LeanTaggedUnionSchema.toTy = some optChar := rfl

/-! ## Recursive tagged union

`RTy.self 0` is an occurrence of the declaration being defined. -/

/-- `inductive MyList | nil | cons (hd : Int) (tl : MyList)`. -/
def myList : Ty := .recTaggedUnion ⟨.skip (.here ⟨.prim .int, [.self 0]⟩ [])⟩

/-- `inductive Tree | leaf (kids : Array Tree) | node (v : Int) (kid : Tree)`: `leaf` is
    a base constructor even though it mentions the type, because an array may be
    empty. -/
def tree : Ty :=
  .recTaggedUnion ⟨.payloadFirst ⟨.array (.self 0), []⟩ [.prim .int, .self 0] []⟩

/-- `inductive Chain | stop | link (next : Option Chain)`: an `Option` guards a self
    occurrence just as an array does — and it is an ordinary `taggedUnion` inside the
    recursive shape, not a scope of its own, so its `.self 0` is still `Chain`. -/
def chain : Ty :=
  .recTaggedUnion ⟨.skip (.here ⟨.taggedUnion (.skip (.here ⟨.self 0, []⟩ [])), []⟩ [])⟩

/-- A function *returning* the declared type is fine: `inductive Stream | done | step
    (head : Int) (tail : Nat → Stream)`. -/
def lazyStream : Ty :=
  .recTaggedUnion ⟨.skip (.here ⟨.prim .int, [.fn [.prim .nat] (.self 0)]⟩ [])⟩

example : Ty.wf myList = true := by decide
example : Ty.wf tree = true := by decide
example : Ty.wf chain = true := by decide
example : Ty.wf lazyStream = true := by decide

/-! Rejected: not actually recursive — that is a `Ty.taggedUnion`. -/
example :
    LeanTaggedUnionSchema.wf ⟨.skip (.here ⟨.prim .int, []⟩ [])⟩ = false := by decide

/-! Rejected: not well founded.  Every constructor of
`inductive Bad | l : Bad → Bad | r : Bad → Bad` needs a value of the type, so the type
has none — Lean accepts the declaration, and the backend reads it, which is why this is
a check rather than a condition of the shape. -/
example :
    LeanTaggedUnionSchema.wf ⟨.payloadFirst ⟨.self 0, []⟩ [.self 0] []⟩ = false := by
  decide

/-! A `Thunk` is no guard either: forcing it has to produce a value of the type. -/
example :
    LeanTaggedUnionSchema.wf ⟨.payloadFirst ⟨.thunk (.self 0), []⟩ [.self 0] []⟩
      = false := by decide

/-! ## Recursive record -/

/-- `structure Tree where v : Int; kids : Array Tree`. -/
def treeRecord : Ty := .recObject ⟨⟨.prim .int, .array (.self 0), []⟩⟩

example : Ty.wf treeRecord = true := by decide

/-! Rejected: `structure S where s : S; n : Nat` is uninhabited — the self occurrence is
unguarded. -/
example : LeanRecordSchema.wf ⟨⟨.self 0, .prim .nat, []⟩⟩ = false := by decide

/-! Rejected: a "recursive" record that never mentions itself is a `Ty.record`. -/
example : LeanRecordSchema.wf ⟨⟨.prim .int, .prim .nat, []⟩⟩ = false := by decide

/-! A one-field recursive record is a newtype, i.e. a `Ty.recAlias`, and is not writable
as a `recObject` at all: its payload would be a one-element `LeanRecordSchema`. -/
example : LeanRecordSchema.ofList? [RTy.array (.self 0)] = none := rfl

/-! ## Recursive newtype

One constructor with exactly one field is a wrapper, and wrappers are erased: a `Rose`
is *not* `{ _kids: […] }` but simply `[…]`, an array of arrays of … -/

/-- `structure Rose where kids : Array Rose`. -/
def rose : Ty := .recAlias ⟨.array (.self 0)⟩

example : Ty.wf rose = true := by decide

/-- An alias has no layout of its own; a value of it is a value of what its body
    unfolds to. -/
example : rose.layout? = none := rfl
example : rose.aliasUnfold? = some (.array rose) := rfl

/-! Rejected: `structure S where s : S` is the equation `S = S`, which no value
satisfies; and `structure S where s : Thunk S` is `S = Thunk S`, which is no better.
This is the `inductive Bad | mk : Bad → Bad` of the user's question, and the type
language *does* let it be written — nothing about its shape is wrong — so `Ty.wf` is
what refuses it. -/
example : RTy.wf ⟨.self 0⟩ = false := by decide
example : RTy.wf ⟨.thunk (.self 0)⟩ = false := by decide
example : Ty.wf (.recAlias ⟨.self 0⟩) = false := by decide

/-! Rejected: a wrapper that does *not* mention itself is erased completely
(`structure Wrapper where x : Nat` is `Ty.nat`), so there is no `recAlias` for it. -/
example : RTy.wf ⟨.prim .nat⟩ = false := by decide

/-! ## Mutual families

A family is a **zipper**: the members before the one this type is, that member, and the
members after it.  So a family of one member, and a member number that points at no
member, are both unwritable; what is left to check is that the block is strongly
connected and that its members have values. -/

/-- The "fake mutual" block

```lean
mutual
  inductive Color | red | blue
  inductive Shape | circle | box
end
```

No field of either type mentions the other — and, with two field-less constructors
each, neither is even a member shape: both are booleans.  The block is two `Ty.bool`s,
and the members below are the closest writable thing to it: two members that ignore
each other. -/
def colorShapeMembers : List Ty.FamMember :=
  [.ctors (.payloadFirst ⟨.prim .nat, []⟩ [] []),
   .ctors (.payloadFirst ⟨.prim .int, []⟩ [] [])]

example : famStronglyConnected colorShapeMembers = false := by decide
example :
    (LeanMutualRecFamily.ofMembers? colorShapeMembers 0).map LeanMutualRecFamily.wf
      = some false := by decide

/-- A genuinely mutual block:

```lean
mutual
  inductive Exp | lit (n : Int) | block (s : Stm)
  inductive Stm | nop | ret (e : Exp)
end
``` -/
def expMember : Ty.FamMember := .ctors (.payloadFirst ⟨.prim .int, []⟩ [.self 1] [])

/-- The second member of that block: `inductive Stm | nop | ret (e : Exp)`. -/
def stmMember : Ty.FamMember := .ctors (.skip (.here ⟨.self 0, []⟩ []))

/-- Both members, in declaration order. -/
def expStmMembers : List Ty.FamMember := [expMember, stmMember]

/-- Member `0` (`Exp`) of that block. -/
def expTy : Ty := .mutualRecursiveFamily (.selectedThenMore [] expMember stmMember [])

/-- Member `1` (`Stm`) of the same block: the same members, a different index. -/
def stmTy : Ty := .mutualRecursiveFamily (.selectedLast expMember [] stmMember)

example : Ty.wf expTy = true := by decide
example : Ty.wf stmTy = true := by decide
example : expTy.mutualRecFamily?.map LeanMutualRecFamily.memberIdx = some 0 := rfl
example : stmTy.mutualRecFamily?.map LeanMutualRecFamily.memberIdx = some 1 := rfl

/-! There is no member `2`, and there is no way to write a family that points at one. -/
example : LeanMutualRecFamily.ofMembers? expStmMembers 2 = none := rfl

/-! A member may be a **newtype**, and is then an *alias member*: it has no object of
its own, and a value of it is a value of its single field.  Dropping `Stm.nop` from the
block above makes `Stm` such a member, and the block is still accepted. -/
def expStmAliasMembers : List Ty.FamMember :=
  [.ctors (.payloadFirst ⟨.prim .int, []⟩ [.self 1] []), .alias (.self 0)]

example :
    (LeanMutualRecFamily.ofMembers? expStmAliasMembers 0).map LeanMutualRecFamily.wf
      = some true := by decide

/-! An alias member must still be buildable: a cycle of unguarded aliases has no values
at all. -/
def aliasCycleMembers : List Ty.FamMember := [.alias (.self 1), .alias (.self 0)]

example : famAllInhabited aliasCycleMembers = false := by decide
example :
    (LeanMutualRecFamily.ofMembers? aliasCycleMembers 0).map LeanMutualRecFamily.wf
      = some false := by decide

/-! Guarded, the same cycle is fine: `A = Array B`, `B = Array A`, i.e. nested JS
arrays, and `[]` is a value of either. -/
def aliasCycleGuardedMembers : List Ty.FamMember :=
  [.alias (.array (.self 1)), .alias (.array (.self 0))]

example :
    (LeanMutualRecFamily.ofMembers? aliasCycleGuardedMembers 0).map
        LeanMutualRecFamily.wf = some true := by decide

/-! One direction only (`Wrap` mentions `Inner`, never the other way round) is two
independent declarations, not a family. -/
def oneWayMembers : List Ty.FamMember :=
  [.ctors (.payloadFirst ⟨.self 1, []⟩ [.prim .nat] []),
   .ctors (.payloadFirst ⟨.prim .int, []⟩ [.prim .nat] [])]

example : famStronglyConnected oneWayMembers = false := by decide

/-! A block in which no member can be built is refused: every constructor of `B` needs
an `A` and every constructor of `A` needs a `B`. -/
def uninhabitedMembers : List Ty.FamMember :=
  [.ctors (.payloadFirst ⟨.self 1, []⟩ [.self 1] []),
   .ctors (.payloadFirst ⟨.self 0, []⟩ [.self 0] [])]

example : famStronglyConnected uninhabitedMembers = true := by decide
example : famAllInhabited uninhabitedMembers = false := by decide
example :
    (LeanMutualRecFamily.ofMembers? uninhabitedMembers 0).map LeanMutualRecFamily.wf
      = some false := by decide

/-! Guarding makes the same block well founded: a field holding an `Array B` may hold
the empty one. -/
def guardedMembers : List Ty.FamMember :=
  [.ctors (.payloadFirst ⟨.array (.self 1), [.prim .nat]⟩ [.prim .nat] []),
   .ctors (.payloadFirst ⟨.self 0, []⟩ [.prim .int] [])]

example : famAllInhabited guardedMembers = true := by decide
example :
    (LeanMutualRecFamily.ofMembers? guardedMembers 0).map LeanMutualRecFamily.wf
      = some true := by decide

/-! A single declaration is not a family: it is `recTaggedUnion`, `recObject` or
`recAlias`, and a one-member family cannot be written. -/
example :
    LeanMutualRecFamily.ofMembers?
      [LeanFamMemberSchema.ctors (.skip (.here ⟨RTy.prim .int, [.self 0]⟩ []))] 0
      = none := rfl

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
example : Ty.toRTy pair = RTy.record ⟨.prim .float, .prim .int64, []⟩ := rfl
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
