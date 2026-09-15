module

public import NonEmpty.String.Basic
public import LakeJs.PrimTy
public import LakeJs.Schemas

open NonEmpty.String

@[expose] public section

/-!
# `Ty`: the types that can be compiled to JavaScript

Four decisions are baked into `Ty`:

* **no unit types, no void types and no newtypes.**  A type with exactly one value
  carries no information and is erased before it ever reaches `Ty`; a type with no
  values at all has no runtime representation; and a one-field wrapper *is* its
  field, so it is erased too.  So there is no `Ty.unit`, no `Ty.void` and no one-field
  record: an enum needs ≥ 2 constructors, a record needs ≥ 2 fields, `bitvec n` needs
  `n ≥ 1`, every member of a mutual family must be inhabited and none of them may be a
  wrapper.  `structure Rose where kids : Array Rose` — a *recursive* wrapper — is not
  an object either: it is the fixed point `Rose = Array Rose`, i.e. a JS array of
  arrays of …, which is what `Ty.recAlias` denotes.

* **leaves live in `PrimTy`.**  Every terminal type (`bool`, `nat`, `uint32`,
  `bitvec n`, `string`, …) is a constructor of `LakeJs.PrimTy`, and `Ty` embeds them
  with `Ty.prim`.  `Ty.nat`, `Ty.uint32`, … remain available as abbreviations, so
  `.nat` still elaborates.

* **no hash containers inside `Ty`.**  The schemas used to spell `HashSet`/`HashMap`
  as fields of types mutually inductive with `Ty`.  The kernel rejects that: a nested
  occurrence of `Ty` under `HashMap` is not a legal nested inductive.  The schemas
  (`LakeJs.Schemas`) use the shape/row split instead.

* **every `Ty` is well-formed by construction.**  There is no `Ty.wf` predicate and no
  `{ t : Ty // t.wf }` subtype: the invariants are part of the *structure* of `Ty`, so
  an ill-formed type does not typecheck.

## The six shapes of a user-defined type

| Shape                                     | Mutual? | Recursive? | `Ty` constructor           |
| :---------------------------------------- | :------ | :--------- | :------------------------- |
| `inductive Direction \| north \| …`       | no      | no         | `Ty.enum`                  |
| `structure Point where x, y`              | no      | no         | `Ty.record`                |
| `inductive Option \| none \| some …`      | no      | no         | `Ty.taggedUnion`           |
| `inductive MyList \| nil \| cons …`       | no      | yes        | `Ty.recTaggedUnion`        |
| `structure Tree where n; kids : Array Tree` | no    | yes        | `Ty.recObject`             |
| `structure Rose where kids : Array Rose`  | no      | yes        | `Ty.recAlias`              |
| a genuinely mutual block                  | yes     | yes        | `Ty.mutualRecursiveFamily` |

A one-constructor, one-field declaration that is *not* recursive has no row at all:
`structure Wrapper where x : Nat` is `Ty.nat`.

They are disjoint: see `LakeJs.Schemas`.  `Option` and `Prod` are *derived*
(`Ty.option`, `Ty.prod`), not primitive.
-/

/-! ## `Ty` -/

inductive Ty where
  /-- A terminal type: a scalar or other built-in leaf.  See `PrimTy`. -/
  | prim : PrimTy → Ty
  /-- A JS function, taking 0 or more parameters and returning a value.  It compiles
      to an **uncurried** JS function, so Lean's `def foo : Unit → Int → Int` is
      `.fn [] (.fn [.int] .int)`.  A function returning nothing is unrepresentable:
      the only reason to have one is an effect, and the source language is pure. -/
  | fn        : List Ty → Ty → Ty
  /-- Always a JS array. -/
  | array     : Ty → Ty
  /-- IF `List Char` (or another primitive element) then a JS array; inside a
      user-defined recursive type it is `{ h: …, t: … } | undefined`. -/
  | list      : Ty → Ty
  /-- In JS: `Promise<α>` (async task / worker). -/
  | task      : Ty → Ty
  /-- In JS: `Promise<α>`. -/
  | promise   : Ty → Ty
  /-- In JS: `(fn) => { let r; return () => (r === undefined ? (r = fn()) : r); }`.
      A thunk never returns `undefined`, since all unit-like types are erased. -/
  | thunk     : Ty → Ty
  /-- Non-mutual, non-recursive enum (no fields).  In JS: `"north" | "south"` or
      `0 | 1`. -/
  | enum : LeanEnumSchema → Ty
  /-- Non-mutual, non-recursive single-constructor record with ≥ 2 fields.  In JS:
      `{ _x: …, _y: … }`.  A *one*-field record is a newtype: it is erased, and its
      `Ty` is the field's own `Ty`. -/
  | record : LeanRecordSchema Ty → Ty
  /-- Non-mutual, non-recursive sum type with fields (`Option`, `Except`, …).
      In JS: `{ tag: …, _1: … }`. -/
  | taggedUnion : LeanTaggedUnionSchema Ty → Ty
  /-- Non-mutual recursive sum type (`MyList`, a tree, …).  In JS: `{ tag: …, … }`.
      The built-in `List` uses `Ty.list`; a user-written `MyList` uses this. -/
  | recTaggedUnion : LeanRecTaggedUnionSchema Ty → Ty
  /-- Non-mutual recursive record with ≥ 2 fields
      (`structure Tree where n : Nat; kids : Array Tree`).
      In JS: `{ _n: …, _kids: […] }`. -/
  | recObject : LeanRecObjectSchema Ty → Ty
  /-- Non-mutual recursive **newtype**, with the wrapper erased
      (`structure Rose where kids : Array Rose`): the fixed point of the single
      field's type.  In JS a `Rose` is just `[…]`, an array of arrays of …, with no
      object wrapper — `[[], [[], []]]` is a `Rose`. -/
  | recAlias : LeanRecAliasSchema Ty → Ty
  /-- One member of a genuinely mutual recursive family.  A member that is a newtype
      is an *alias member*: like `Ty.recAlias`, it has no object of its own, and a
      value of it is a value of its single field (`famIsAliasMember`).  *Which*
      member, and the
      proof that it exists, are fields of the schema (`fam.member`,
      `fam.h_member`) rather than extra arguments here: see `LeanMutualRecFamily`
      for why the kernel rules out `… → (member : Nat) → (h : member < fam.numMembers)
      → Ty`.  Either way a `Ty` never points outside its family. -/
  | mutualRecursiveFamily : LeanMutualRecFamily Ty → Ty

/-! ## The terminal types, as `Ty` abbreviations

`Ty.prim` is the only leaf constructor, but writing `.prim .nat` everywhere is noise,
so each `PrimTy` is also available directly under the `Ty` namespace — which is what
makes `.nat`, `.uint32`, `.bitvec 32`, … keep working in a position expecting a
`Ty`. -/

namespace Ty

/-- In JS: `boolean`. -/
abbrev bool : Ty := .prim .bool
/-- In JS: configurable (`number` or `bigint`). -/
abbrev nat : Ty := .prim .nat
/-- In JS: configurable (`number` or `bigint`). -/
abbrev int : Ty := .prim .int
/-- A bit vector of `n` bits; `n` must be positive, since `BitVec 0` is a unit type. -/
abbrev bitvec (n : Nat) (h_pos : 0 < n := by decide) : Ty := .prim (.bitvec n h_pos)
/-- In JS: `number`. -/
abbrev uint8 : Ty := .prim .uint8
/-- In JS: `number`. -/
abbrev uint16 : Ty := .prim .uint16
/-- In JS: `number`. -/
abbrev uint32 : Ty := .prim .uint32
/-- In JS: configurable (`number` or `bigint`). -/
abbrev uint64 : Ty := .prim .uint64
/-- In JS: configurable (`number` or `bigint`). -/
abbrev usize : Ty := .prim .usize
/-- In JS: `number`. -/
abbrev int8 : Ty := .prim .int8
/-- In JS: `number`. -/
abbrev int16 : Ty := .prim .int16
/-- In JS: `number`. -/
abbrev int32 : Ty := .prim .int32
/-- In JS: configurable (`number` or `bigint`). -/
abbrev int64 : Ty := .prim .int64
/-- In JS: configurable (`number` or `bigint`). -/
abbrev isize : Ty := .prim .isize
/-- In JS: `string`. -/
abbrev char : Ty := .prim .char
/-- In JS: `string`. -/
abbrev string : Ty := .prim .string
/-- In JS: `Uint8Array`. -/
abbrev byteArray : Ty := .prim .byteArray
/-- A `Lean.Name`. In JS: `string`. -/
abbrev name : Ty := .prim .name
/-- A position in a string. -/
abbrev stringPos : Ty := .prim .stringPos
/-- In JS: `{ str, startPos, stopPos }`. -/
abbrev substring : Ty := .prim .substring
/-- A string slice. -/
abbrev stringSlice : Ty := .prim .stringSlice
/-- In JS: `number` (IEEE 754 64-bit). -/
abbrev float : Ty := .prim .float
/-- In JS: `number` (IEEE 754 32-bit). -/
abbrev float32 : Ty := .prim .float32
/-- In JS: `Float64Array`. -/
abbrev floatArray : Ty := .prim .floatArray
/-- In JS: `-1 | 0 | 1`. -/
abbrev ordering : Ty := .prim .ordering
/-- In JS (node only): a `ChildProcess` handle. -/
abbrev childProcess : Ty := .prim .childProcess
/-- In JS: `object` / `any`. -/
abbrev shareCommonObject : Ty := .prim .shareCommonObject
/-- In JS: a `Map` / cache object. -/
abbrev shareCommonState : Ty := .prim .shareCommonState
/-- Erased in JS, like a unit value. -/
abbrev taskPriority : Ty := .prim .taskPriority

/-- A one-parameter function type: `a ⇒ b` is `Ty.fn [a] b`.  Since `Ty.fn` takes a
    *list* of parameters (it compiles to an uncurried JS function), the infix arrow is
    the curried, one-argument special case, as in
    `.nat ⇒ .nat ⇒ .bool = .fn [.nat] (.fn [.nat] .bool)`. -/
abbrev arrow (a b : Ty) : Ty := Ty.fn [a] b

end Ty

infixr:70 " ⇒ " => Ty.arrow

/-- The record schema of a compiled Lean `structure`. -/
abbrev LeanRecord := LeanRecordSchema Ty
/-- The schema of a compiled non-recursive Lean sum type. -/
abbrev LeanTaggedUnion := LeanTaggedUnionSchema Ty
/-- The schema of a compiled non-mutual recursive Lean `inductive`. -/
abbrev LeanRecTaggedUnion := LeanRecTaggedUnionSchema Ty
/-- The schema of a compiled non-mutual recursive Lean `structure`. -/
abbrev LeanRecObject := LeanRecObjectSchema Ty
/-- The schema of a compiled non-mutual recursive Lean newtype, wrapper erased. -/
abbrev LeanRecAlias := LeanRecAliasSchema Ty
/-- The schema of one member of a compiled genuinely mutual block. -/
abbrev LeanMutualFamily := LeanMutualRecFamily Ty

/-! ## Derived types

`Option`, `Prod` and "nullary function" are **not** primitive constructors of `Ty`:
each is an ordinary type of one of the shapes above, so the backend needs no special
case for them.

`Ty.option` and `Ty.prod` are *generated* from Lean's own `Option` and `Prod`
declarations by the `derive_ty` command, and therefore live in `LakeJs.TyDerived`
(the command itself is `LakeJs.TyDerive`).  Only `Ty.nullary` is written by hand,
because it is not a declaration one could read a schema off: it is a notation for a
function type. -/

/-- `Unit → α` — a JS function of zero parameters.  `Unit` itself is erased, so a
    nullary function is `Ty.fn []`, not a function taking a unit value. -/
abbrev Ty.nullary (ret : Ty) : Ty := Ty.fn [] ret

/-! ## Printing

`Ty.pretty`, with the `Repr` and `ToString` instances it backs, is in
`LakeJs.TyPretty`. -/

-- `def HashSet α := HashMap α Unit`.
--  - `HashSet .somebasictype` is optimized to js Set. what to do with `TreeSet`?
--  - `HashSet nonbasictype` is optimized to js Map where key is hash.
-- TODO: what to do with `TreeSet`?

end
