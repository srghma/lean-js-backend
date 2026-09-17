module

public import LakeJs.LeanPrimTy
public import LakeJs.Schema

@[expose] public section

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LakeJs

/-!
# `Ty`: the types that can be compiled to JavaScript

`Ty` is a **tree of types**.  There are no schemas held on the side, no names and no
side tables: a type is built out of its own parts, and two types are equal when their
trees are equal.

Six decisions are baked into it.

* **no names anywhere.**  A constructor is a *position* in the list of constructors and
  a field is a *position* in the list of fields, so a value of a user-defined type is
  `{ tag: 0, _1: …, _2: … }` — a number and positional fields, never a string.

* **ordinary equality.**  `Ty` is a first-order inductive with a `DecidableEq` instance
  (`Ty.beq` and the lemmas below), so two types are compared with `=` and `decide`.

* **no degenerate type is writable.**  The payload of each shape is one of the schemas
  of `LakeJs.Schema`, and those carry their counting invariants in their *types*:

  | shape             | payload                          | what cannot be written              |
  | :---------------- | :------------------------------- | :---------------------------------- |
  | `Ty.enum`         | `LeanEnumSchema`                 | fewer than three constructors       |
  | `Ty.record`       | `LeanRecordSchema Ty`            | fewer than two fields               |
  | `Ty.taggedUnion`  | `LeanTaggedUnionSchema Ty`       | fewer than two constructors, or none with a field |
  | `Ty.recObject`    | `LeanRecordSchema RTy`        | fewer than two fields               |
  | `Ty.recTaggedUnion` | `LeanTaggedUnionSchema RTy` | fewer than two constructors, or none with a field |
  | `Ty.mutualRecursiveFamily` | `LeanMutualRecFamily RTy` | fewer than two members, or a member number out of range |

  So an `Empty`-like type (no values) and a `Unit`-like type (one value, carrying no
  information, erased before a type is built) have no `Ty`, and a `Bool`-like type — a
  sum of exactly two field-less constructors — is not an enum with two constructors but
  `Ty.bool`, so that it prints as `true`/`false`.  There is likewise no `Ty.void` and no
  `Ty.erased`, and `bitvec n` needs `n ≥ 1` because `BitVec 0` is a unit type.

* **no unmodelled type.**  There is no `dynamic`: every Lean type a compiled
  declaration mentions is either one of the shapes below or the declaration is refused.
  A parameterised declaration is modelled *at its instantiation* (`Except Nat String`
  is a `taggedUnion` of `[[nat], [string]]`), and a mutual block of declarations is
  modelled as a `mutualRecursiveFamily`.  The one type that stands for a value the
  backend does not know the shape of is `Ty.typeParam`, and it is *parametricity*, not
  ignorance: it is the type of a value whose Lean type is a type parameter of the
  enclosing declaration, which the compiled code can only pass around — **no** data
  operation of `Term` is available at it (`Ty.ctorFields?_typeParam`).

* **leaves live in `LeanPrimTy`.**  Every terminal type (`bool`, `nat`, `uint32`,
  `bitvec n`, `string`, …) is a constructor of `LakeJs.LeanPrimTy`, and `Ty` embeds them
  with `Ty.prim`.  `Ty.nat`, `Ty.uint32`, … remain available as abbreviations.

* **the shapes are language-independent.**  The schemas are parametrised by the type
  language (`LeanRecordSchema α`), so the *same* schema describes a record of `Ty`s and
  a record of `RTy`s — and will describe a record of the types of whatever further
  language is added next.  Only their instantiation lives here.

## The shapes a user-defined type can have

A Lean declaration is modelled by *which* of the following shapes it has, so a
traversal never has to ask a schema what kind of declaration it came from:

| Lean                                              | `Ty`                                   |
| :------------------------------------------------ | :------------------------------------- |
| `inductive Dir \| north \| south`                  | `.bool` — a two-constructor enum is a boolean |
| `inductive Dir3 \| n \| s \| e`                    | `.enum ⟨0, 0⟩` (three constructors, from `0`) |
| `structure Point where x y : Nat`                  | `.record ⟨.nat, .nat, []⟩`             |
| `structure Wrap where v : Nat` (a newtype)         | `.nat` — the wrapper is erased         |
| `Option Nat`                                       | `.option .nat`                         |
| `inductive T \| leaf \| node : T → T → T`          | `.recTaggedUnion (.skip (.here ⟨.self 0, [.self 0]⟩ []))` |
| `structure Tree where n : Nat; kids : Array Tree`  | `.recObject ⟨.nat, .array (.self 0), []⟩` |
| `structure Rose where kids : Array Rose`           | `.recAlias (.array (.self 0))`         |
| a mutual block                                     | `.mutualRecursiveFamily f`             |

## `.self` is available in the recursive shapes and nowhere else

The recursive shapes — `recTaggedUnion`, `recObject`, `recAlias` and
`mutualRecursiveFamily` — are the *binders* of the type language: their children are
`RTy`s, the types *inside a recursive declaration*, and `RTy.self i` is an occurrence of
member `i` of that declaration (`i = 0` unless the binder is a mutual family).  The
other shapes carry ordinary `Ty`s, which have no `.self` constructor at all, so a type
outside a recursive declaration cannot mention one.

`RTy` mirrors `Ty`, so anything may appear inside a recursive declaration — a `Nat`, an
`Option Tree`, an `Array Tree`.  Where an `RTy` is itself a *recursive* shape, it opens
a new scope: the `.self` of its children is that inner declaration, exactly as a nested
binder shadows an outer one.

That a recursive shape really does mention itself, and that the type it describes has
any values at all (`inductive Bad | mk : Bad → Bad` has none), are conditions on a whole
type rather than counting conditions on one payload, so they are not carried by the
constructors: they are the decidable predicates of `LakeJs.TySchema` (`Ty.Wf`), and the
subtype `WfTy` is the type of the types that satisfy them.

## The shared type formers

`array`, `list`, `task`, `promise` and `thunk` are the constructors of
`LeanPrimTyCovariant`, and `fn` and `fn_returnsProd` those of `TyFn`: neither group says
anything about recursion, and each makes sense at every layer, so both are parametrised
by the layer's own type and embedded by `Ty` and by `RTy` alike (`Ty.primCovariant`,
`Ty.fnTy`).  `Ty.fn`, `Ty.array`, … remain available — and usable in patterns — as
abbreviations.
-/

/-! ## `Ty`, `RTy` and the members of a mutual family -/

mutual

/-- A closed type: one that mentions no recursive declaration it is not itself part of.
    This is the type language the terms of `LakeJs.Expr` are indexed by. -/
inductive Ty where
  /-- A terminal type: a scalar or other built-in leaf.  See `LeanPrimTy`. -/
  | prim : LeanPrimTy → Ty
  /-- The type of a value whose Lean type is a **type parameter** of the enclosing
      declaration — the `α` of `def f (xs : List α) : Nat`.  Lean's type arguments are
      erased, so a compiled function is handed such a value and can pass it on, store
      it and return it, but never look inside it: no constructor, projection or
      dispatch of `Term` is available at this type (`Ty.ctorFields?_typeParam`).  It is
      parametricity, not an unmodelled type: there is nothing more to know about it. -/
  -- | typeParam : Ty -- TODO: CANNOT BE, ERASED ARE ERASED AND ARE UNREPRESENTABLE!!!
  /-- A function type: an uncurried JS function, or one answering with several values
      at once.  `Ty.fn` and `Ty.fn_returnsProd` abbreviate the two cases. -/
  | fnTy : TyFn Ty → Ty
  /-- A built-in type former that carries one type: an array, a list, a task, a promise
      or a thunk.  `Ty.array`, `Ty.list`, … abbreviate the cases. -/
  | primCovariant : LeanPrimTyCovariant Ty → Ty
  /-- A non-recursive sum whose constructors all have no fields, printed as the plain
      numbers `shift`, `shift + 1`, … — of which there are **at least three**, since the
      smaller cases are not enums: see `LeanEnumSchema`. -/
  | enum : LeanEnumSchema → Ty
  /-- A non-recursive single-constructor type with ≥ 2 fields, in declaration order.
      In JS: `{ tag: 0, _1: …, _2: … }`.  A *one*-field record is a newtype: it is
      erased, and its `Ty` is the field's own `Ty`. -/
  | record : LeanRecordSchema Ty → Ty
  /-- A non-recursive sum type with fields (`Option`, `Except`, …): one entry per
      constructor, in declaration order, each holding the types of that constructor's
      fields.  In JS: `{ tag: 1, _1: … }`. -/
  | taggedUnion : LeanTaggedUnionSchema Ty → Ty
  /-- A recursive sum type (`MyList`, a tree, …): one entry per constructor, each
      holding the types of its fields, in which `RTy.self 0` is an occurrence of the
      declaration itself.  In JS: `{ tag: …, … }`. -/
  | recTaggedUnion : LeanTaggedUnionSchema Ty.RTy → Ty
  /-- A recursive single-constructor type with ≥ 2 fields
      (`structure Tree where n : Nat; kids : Array Tree`), in which `RTy.self 0` is an
      occurrence of the declaration itself.  In JS: `{ tag: 0, _1: …, _2: … }`. -/
  | recObject : LeanRecordSchema Ty.RTy → Ty
  /-- A recursive **newtype**, with the wrapper erased
      (`structure Rose where kids : Array Rose`): the fixed point of the single field's
      type.  In JS a `Rose` is just `[…]`, an array of arrays of …, with no object
      wrapper — `[[], [[], []]]` is a `Rose`. -/
  | recAlias : Ty.RTy → Ty
  /-- One member of a genuinely mutual recursive family: the bodies of *all* of its
      members, in declaration order, and which of them this type is — held as a zipper,
      so the member number is in range and the family has two members or more by
      construction.  Inside the bodies, `RTy.self i` is an occurrence of member `i`, so
      a type never points outside its family. -/
  | mutualRecursiveFamily : LeanMutualRecFamily Ty.RTy → Ty

/-- A type **inside a recursive declaration**: everything a `Ty` can be, and in
    addition an occurrence of the declaration being defined.  This is the one layer
    where `.self` is available, which is what keeps a recursive type a *finite* tree. -/
inductive Ty.RTy where
  /-- An occurrence of the declaration whose body this type sits in — member `i` of it
      if that declaration is a mutual family, and `.self 0` otherwise. -/
  | self : Nat → Ty.RTy
  /-- A terminal type. -/
  | prim : LeanPrimTy → Ty.RTy
  /-- The type of a value of a type parameter; see `Ty.typeParam`. -/
  -- | typeParam : Ty.RTy -- TODO: CANNOT BE, ERASED ARE ERASED AND ARE UNREPRESENTABLE!!!
  /-- A function type over types that may mention `.self`. -/
  | fnTy : TyFn Ty.RTy → Ty.RTy
  /-- An array, list, task, promise or thunk of a type that may mention `.self`. -/
  | primCovariant : LeanPrimTyCovariant Ty.RTy → Ty.RTy
  /-- A non-recursive enum; see `Ty.enum`. -/
  | enum : LeanEnumSchema → Ty.RTy
  /-- A single-constructor record; see `Ty.record`.  Its fields may mention `.self`
      (`structure Pair where fst : Tree; snd : Tree` inside `Tree`). -/
  | record : LeanRecordSchema Ty.RTy → Ty.RTy
  /-- A sum type with fields; see `Ty.taggedUnion`. -/
  | taggedUnion : LeanTaggedUnionSchema Ty.RTy → Ty.RTy
  /-- A *nested* recursive sum type: it opens a new scope, so the `.self` of its own
      children is this inner declaration, not the enclosing one. -/
  | recTaggedUnion : LeanTaggedUnionSchema Ty.RTy → Ty.RTy
  /-- A nested recursive record; it opens a new scope, as `recTaggedUnion` does. -/
  | recObject : LeanRecordSchema Ty.RTy → Ty.RTy
  /-- A nested recursive newtype; it opens a new scope, as `recTaggedUnion` does. -/
  | recAlias : Ty.RTy → Ty.RTy
  /-- A nested mutual recursive family; it opens a new scope, as `recTaggedUnion`
      does. -/
  | mutualRecursiveFamily : LeanMutualRecFamily Ty.RTy → Ty.RTy

end

/-- One member of a mutual recursive family: a member with constructors, a
    single-constructor member with fields, or a newtype member. -/
abbrev Ty.FamMember := LeanFamMemberSchema Ty.RTy

namespace Ty

/-! ## Deciding equality

`Ty` holds schemas of types, and schemas of schemas of types, which no `deriving`
handler covers, so the instance is written out: a structural `Ty.beq` over the whole
family of types and schemas, and the two lemmas that make it equality. -/

mutual

/-- Structural equality of two closed types. -/
def beq : Ty → Ty → Bool
  | .prim p, .prim q => p == q
  | .typeParam, .typeParam => true
  | .fnTy s, .fnTy t => Ty.beqFn s t
  | .primCovariant s, .primCovariant t => Ty.beqCov s t
  | .enum a, .enum b => a == b
  | .record a, .record b => Ty.beqA2 a b
  | .taggedUnion a, .taggedUnion b => Ty.beqTU a b
  | .recTaggedUnion a, .recTaggedUnion b => RTy.beqRecTU a b
  | .recObject a, .recObject b => RTy.beqRecObj a b
  | .recAlias a, .recAlias b => RTy.beqAlias a b
  | .mutualRecursiveFamily a, .mutualRecursiveFamily b => RTy.beqFamily a b
  | _, _ => false

/-- Structural equality of two function types over closed types. -/
def beqFn : TyFn Ty → TyFn Ty → Bool
  | .fn ps r, .fn qs s => Ty.beqList ps qs && Ty.beq r s
  | .fn_returnsProd ps r rs, .fn_returnsProd qs s ss =>
      Ty.beqList ps qs && Ty.beq r s && Ty.beqList rs ss
  | _, _ => false

/-- Structural equality of two invariant type formers over closed types. -/
def beqCov : LeanPrimTyCovariant Ty → LeanPrimTyCovariant Ty → Bool
  | .array a, .array b => Ty.beq a b
  | .list a, .list b => Ty.beq a b
  | .task a, .task b => Ty.beq a b
  | .promise a, .promise b => Ty.beq a b
  | .thunk a, .thunk b => Ty.beq a b
  | .lazy a, .lazy b => Ty.beq a b
  | _, _ => false

/-- `Ty.beq`, on a list of closed types. -/
def beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false

/-- `Ty.beq`, on the constructors of a closed layout. -/
def beqCtors : List (List Ty) → List (List Ty) → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beqList a b && Ty.beqCtors as bs
  | _, _ => false

/-- `Ty.beq`, on the fields of a record of closed types. -/
def beqA2 : LeanRecordSchema Ty → LeanRecordSchema Ty → Bool
  | ⟨a1, a2, as⟩, ⟨b1, b2, bs⟩ => Ty.beq a1 b1 && Ty.beq a2 b2 && Ty.beqList as bs

/-- `Ty.beq`, on the fields of a constructor that has at least one. -/
def beqNE : NonEmptyList Ty → NonEmptyList Ty → Bool
  | ⟨a, as⟩, ⟨b, bs⟩ => Ty.beq a b && Ty.beqList as bs

/-- `Ty.beq`, on the constructors of a tagged union of closed types. -/
def beqTU : LeanTaggedUnionSchema Ty → LeanTaggedUnionSchema Ty → Bool
  | .payloadFirst f n r, .payloadFirst g m s =>
      Ty.beqNE f g && Ty.beqList n m && Ty.beqCtors r s
  | .skip a, .skip b => Ty.beqCP a b
  | _, _ => false

/-- `Ty.beq`, on the constructors that follow a field-less one. -/
def beqCP : CtorsWithPayload Ty → CtorsWithPayload Ty → Bool
  | .here f r, .here g s => Ty.beqNE f g && Ty.beqCtors r s
  | .skip a, .skip b => Ty.beqCP a b
  | _, _ => false

/-- Structural equality of two types inside a recursive declaration. -/
def RTy.beq : RTy → RTy → Bool
  | .self i, .self j => i == j
  | .prim p, .prim q => p == q
  | .typeParam, .typeParam => true
  | .fnTy s, .fnTy t => RTy.beqFn s t
  | .primCovariant s, .primCovariant t => RTy.beqCov s t
  | .enum a, .enum b => a == b
  | .record a, .record b => RTy.beqA2 a b
  | .taggedUnion a, .taggedUnion b => RTy.beqTU a b
  | .recTaggedUnion a, .recTaggedUnion b => RTy.beqRecTU a b
  | .recObject a, .recObject b => RTy.beqRecObj a b
  | .recAlias a, .recAlias b => RTy.beqAlias a b
  | .mutualRecursiveFamily a, .mutualRecursiveFamily b => RTy.beqFamily a b
  | _, _ => false

/-- `RTy.beq`, on a function type. -/
def RTy.beqFn : TyFn RTy → TyFn RTy → Bool
  | .fn ps r, .fn qs s => RTy.beqList ps qs && RTy.beq r s
  | .fn_returnsProd ps r rs, .fn_returnsProd qs s ss =>
      RTy.beqList ps qs && RTy.beq r s && RTy.beqList rs ss
  | _, _ => false

/-- `RTy.beq`, on an invariant type former. -/
def RTy.beqCov : LeanPrimTyCovariant RTy → LeanPrimTyCovariant RTy → Bool
  | .array a, .array b => RTy.beq a b
  | .list a, .list b => RTy.beq a b
  | .task a, .task b => RTy.beq a b
  | .promise a, .promise b => RTy.beq a b
  | .thunk a, .thunk b => RTy.beq a b
  | .lazy a, .lazy b => RTy.beq a b
  | _, _ => false

/-- `RTy.beq`, on a list of types. -/
def RTy.beqList : List RTy → List RTy → Bool
  | [], [] => true
  | a :: as, b :: bs => RTy.beq a b && RTy.beqList as bs
  | _, _ => false

/-- `RTy.beq`, on the constructors of a layout. -/
def RTy.beqCtors : List (List RTy) → List (List RTy) → Bool
  | [], [] => true
  | a :: as, b :: bs => RTy.beqList a b && RTy.beqCtors as bs
  | _, _ => false

/-- `RTy.beq`, on the fields of a record. -/
def RTy.beqA2 : LeanRecordSchema RTy → LeanRecordSchema RTy → Bool
  | ⟨a1, a2, as⟩, ⟨b1, b2, bs⟩ => RTy.beq a1 b1 && RTy.beq a2 b2 && RTy.beqList as bs

/-- `RTy.beq`, on the fields of a constructor that has at least one. -/
def RTy.beqNE : NonEmptyList RTy → NonEmptyList RTy → Bool
  | ⟨a, as⟩, ⟨b, bs⟩ => RTy.beq a b && RTy.beqList as bs

/-- `RTy.beq`, on the constructors of a tagged union. -/
def RTy.beqTU : LeanTaggedUnionSchema RTy → LeanTaggedUnionSchema RTy → Bool
  | .payloadFirst f n r, .payloadFirst g m s =>
      RTy.beqNE f g && RTy.beqList n m && RTy.beqCtors r s
  | .skip a, .skip b => RTy.beqCP a b
  | _, _ => false

/-- `RTy.beq`, on the constructors that follow a field-less one. -/
def RTy.beqCP : CtorsWithPayload RTy → CtorsWithPayload RTy → Bool
  | .here f r, .here g s => RTy.beqNE f g && RTy.beqCtors r s
  | .skip a, .skip b => RTy.beqCP a b
  | _, _ => false


/-- Structural equality of two members of a mutual family. -/
def RTy.beqFam : FamMember → FamMember → Bool
  | .ctors a, .ctors b => RTy.beqTU a b
  | .record a, .record b => RTy.beqA2 a b
  | .alias a, .alias b => RTy.beq a b
  | _, _ => false

/-- `RTy.beqFam`, on a list of members. -/
def RTy.beqFamList : List FamMember → List FamMember → Bool
  | [], [] => true
  | a :: as, b :: bs => RTy.beqFam a b && RTy.beqFamList as bs
  | _, _ => false

/-- Structural equality of two mutual families, the selected member included. -/
def RTy.beqFamily : LeanMutualRecFamily RTy → LeanMutualRecFamily RTy → Bool
  | .selectedThenMore b c n a, .selectedThenMore b' c' n' a' =>
      RTy.beqFamList b b' && RTy.beqFam c c' && RTy.beqFam n n' && RTy.beqFamList a a'
  | .selectedLast f b c, .selectedLast f' b' c' =>
      RTy.beqFam f f' && RTy.beqFamList b b' && RTy.beqFam c c'
  | _, _ => false

end

set_option maxHeartbeats 2000000 in
mutual

/-- Closed types that compare equal are equal. -/
theorem eq_of_beq : ∀ {a b : Ty}, Ty.beq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beq]
  case fnTy.fnTy => exact Ty.eq_of_beqFn h
  case primCovariant.primCovariant => exact Ty.eq_of_beqCov h
  case record.record => exact Ty.eq_of_beqA2 h
  case taggedUnion.taggedUnion => exact Ty.eq_of_beqTU h
  case recTaggedUnion.recTaggedUnion => exact RTy.eq_of_beqRecTU h
  case recObject.recObject => exact RTy.eq_of_beqRecObj h
  case recAlias.recAlias => exact RTy.eq_of_beqAlias h
  case mutualRecursiveFamily.mutualRecursiveFamily => exact RTy.eq_of_beqFamily h

/-- The same, for a function type over closed types. -/
theorem eq_of_beqFn : ∀ {a b : TyFn Ty}, Ty.beqFn a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqFn]
  · exact ⟨Ty.eq_of_beqList h.1, Ty.eq_of_beq h.2⟩
  · exact ⟨Ty.eq_of_beqList h.1.1, Ty.eq_of_beq h.1.2, Ty.eq_of_beqList h.2⟩

/-- The same, for an invariant type former over closed types. -/
theorem eq_of_beqCov : ∀ {a b : LeanPrimTyCovariant Ty}, Ty.beqCov a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqCov] <;> exact Ty.eq_of_beq h

/-- The same, for a list of closed types. -/
theorem eq_of_beqList : ∀ {a b : List Ty}, Ty.beqList a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqList]
  exact ⟨Ty.eq_of_beq h.1, Ty.eq_of_beqList h.2⟩

/-- The same, for the constructors of a closed layout. -/
theorem eq_of_beqCtors : ∀ {a b : List (List Ty)}, Ty.beqCtors a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqCtors]
  exact ⟨Ty.eq_of_beqList h.1, Ty.eq_of_beqCtors h.2⟩

/-- The same, for the fields of a record of closed types. -/
theorem eq_of_beqA2 : ∀ {a b : LeanRecordSchema Ty}, Ty.beqA2 a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqA2]
  exact ⟨Ty.eq_of_beq h.1.1, Ty.eq_of_beq h.1.2, Ty.eq_of_beqList h.2⟩

/-- The same, for the fields of a constructor that has at least one. -/
theorem eq_of_beqNE : ∀ {a b : NonEmptyList Ty}, Ty.beqNE a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqNE]
  exact ⟨Ty.eq_of_beq h.1, Ty.eq_of_beqList h.2⟩

/-- The same, for the constructors of a tagged union of closed types. -/
theorem eq_of_beqTU : ∀ {a b : LeanTaggedUnionSchema Ty}, Ty.beqTU a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqTU]
  case payloadFirst.payloadFirst =>
    exact ⟨Ty.eq_of_beqNE h.1.1, Ty.eq_of_beqList h.1.2, Ty.eq_of_beqCtors h.2⟩
  case skip.skip => exact Ty.eq_of_beqCP h

/-- The same, for the constructors that follow a field-less one. -/
theorem eq_of_beqCP : ∀ {a b : CtorsWithPayload Ty}, Ty.beqCP a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqCP]
  case here.here => exact ⟨Ty.eq_of_beqNE h.1, Ty.eq_of_beqCtors h.2⟩
  case skip.skip => exact Ty.eq_of_beqCP h

/-- Types inside a recursive declaration that compare equal are equal. -/
theorem RTy.eq_of_beq : ∀ {a b : RTy}, RTy.beq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beq]
  case fnTy.fnTy => exact RTy.eq_of_beqFn h
  case primCovariant.primCovariant => exact RTy.eq_of_beqCov h
  case record.record => exact RTy.eq_of_beqA2 h
  case taggedUnion.taggedUnion => exact RTy.eq_of_beqTU h
  case recTaggedUnion.recTaggedUnion => exact RTy.eq_of_beqRecTU h
  case recObject.recObject => exact RTy.eq_of_beqRecObj h
  case recAlias.recAlias => exact RTy.eq_of_beqAlias h
  case mutualRecursiveFamily.mutualRecursiveFamily => exact RTy.eq_of_beqFamily h

/-- The same, for a function type. -/
theorem RTy.eq_of_beqFn : ∀ {a b : TyFn RTy}, RTy.beqFn a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqFn]
  · exact ⟨RTy.eq_of_beqList h.1, RTy.eq_of_beq h.2⟩
  · exact ⟨RTy.eq_of_beqList h.1.1, RTy.eq_of_beq h.1.2, RTy.eq_of_beqList h.2⟩

/-- The same, for an invariant type former. -/
theorem RTy.eq_of_beqCov :
    ∀ {a b : LeanPrimTyCovariant RTy}, RTy.beqCov a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqCov] <;> exact RTy.eq_of_beq h

/-- The same, for a list of types. -/
theorem RTy.eq_of_beqList : ∀ {a b : List RTy}, RTy.beqList a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqList]
  exact ⟨RTy.eq_of_beq h.1, RTy.eq_of_beqList h.2⟩

/-- The same, for the constructors of a layout. -/
theorem RTy.eq_of_beqCtors : ∀ {a b : List (List RTy)}, RTy.beqCtors a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqCtors]
  exact ⟨RTy.eq_of_beqList h.1, RTy.eq_of_beqCtors h.2⟩

/-- The same, for the fields of a record. -/
theorem RTy.eq_of_beqA2 : ∀ {a b : LeanRecordSchema RTy}, RTy.beqA2 a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqA2]
  exact ⟨RTy.eq_of_beq h.1.1, RTy.eq_of_beq h.1.2, RTy.eq_of_beqList h.2⟩

/-- The same, for the fields of a constructor that has at least one. -/
theorem RTy.eq_of_beqNE : ∀ {a b : NonEmptyList RTy}, RTy.beqNE a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqNE]
  exact ⟨RTy.eq_of_beq h.1, RTy.eq_of_beqList h.2⟩

/-- The same, for the constructors of a tagged union. -/
theorem RTy.eq_of_beqTU :
    ∀ {a b : LeanTaggedUnionSchema RTy}, RTy.beqTU a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqTU]
  case payloadFirst.payloadFirst =>
    exact ⟨RTy.eq_of_beqNE h.1.1, RTy.eq_of_beqList h.1.2, RTy.eq_of_beqCtors h.2⟩
  case skip.skip => exact RTy.eq_of_beqCP h

/-- The same, for the constructors that follow a field-less one. -/
theorem RTy.eq_of_beqCP : ∀ {a b : CtorsWithPayload RTy}, RTy.beqCP a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqCP]
  case here.here => exact ⟨RTy.eq_of_beqNE h.1, RTy.eq_of_beqCtors h.2⟩
  case skip.skip => exact RTy.eq_of_beqCP h


/-- The same, for one member of a mutual family. -/
theorem RTy.eq_of_beqFam : ∀ {a b : FamMember}, RTy.beqFam a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqFam]
  · exact RTy.eq_of_beqTU h
  · exact RTy.eq_of_beqA2 h
  · exact RTy.eq_of_beq h

/-- The same, for a list of members. -/
theorem RTy.eq_of_beqFamList :
    ∀ {a b : List FamMember}, RTy.beqFamList a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqFamList]
  exact ⟨RTy.eq_of_beqFam h.1, RTy.eq_of_beqFamList h.2⟩

/-- The same, for two mutual families. -/
theorem RTy.eq_of_beqFamily :
    ∀ {a b : LeanMutualRecFamily RTy}, RTy.beqFamily a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqFamily]
  · exact ⟨RTy.eq_of_beqFamList h.1.1.1, RTy.eq_of_beqFam h.1.1.2, RTy.eq_of_beqFam h.1.2,
      RTy.eq_of_beqFamList h.2⟩
  · exact ⟨RTy.eq_of_beqFam h.1.1, RTy.eq_of_beqFamList h.1.2, RTy.eq_of_beqFam h.2⟩

end

set_option maxHeartbeats 2000000 in
mutual

/-- Every closed type compares equal to itself. -/
theorem beq_refl : ∀ (a : Ty), Ty.beq a a = true
  | .prim _ => by simp [Ty.beq]
  | .typeParam => by simp [Ty.beq]
  | .fnTy s => by simp [Ty.beq, Ty.beqFn_refl s]
  | .primCovariant s => by simp [Ty.beq, Ty.beqCov_refl s]
  | .enum _ => by simp [Ty.beq]
  | .record a => by simp [Ty.beq, Ty.beqA2_refl a]
  | .taggedUnion a => by simp [Ty.beq, Ty.beqTU_refl a]
  | .recTaggedUnion a => by simp [Ty.beq, RTy.beqRecTU_refl a]
  | .recObject a => by simp [Ty.beq, RTy.beqRecObj_refl a]
  | .recAlias a => by simp [Ty.beq, RTy.beqAlias_refl a]
  | .mutualRecursiveFamily a => by simp [Ty.beq, RTy.beqFamily_refl a]

/-- The same, for a function type over closed types. -/
theorem beqFn_refl : ∀ (a : TyFn Ty), Ty.beqFn a a = true
  | .fn ps r => by simp [Ty.beqFn, Ty.beqList_refl ps, Ty.beq_refl r]
  | .fn_returnsProd ps r rs => by
      simp [Ty.beqFn, Ty.beqList_refl ps, Ty.beq_refl r, Ty.beqList_refl rs]

/-- The same, for an invariant type former over closed types. -/
theorem beqCov_refl : ∀ (a : LeanPrimTyCovariant Ty), Ty.beqCov a a = true
  | .array a => by simp [Ty.beqCov, Ty.beq_refl a]
  | .list a => by simp [Ty.beqCov, Ty.beq_refl a]
  | .task a => by simp [Ty.beqCov, Ty.beq_refl a]
  | .promise a => by simp [Ty.beqCov, Ty.beq_refl a]
  | .thunk a => by simp [Ty.beqCov, Ty.beq_refl a]
  | .lazy a => by simp [Ty.beqCov, Ty.beq_refl a]

/-- The same, for a list of closed types. -/
theorem beqList_refl : ∀ (a : List Ty), Ty.beqList a a = true
  | [] => by simp [Ty.beqList]
  | a :: as => by simp [Ty.beqList, Ty.beq_refl a, Ty.beqList_refl as]

/-- The same, for the constructors of a closed layout. -/
theorem beqCtors_refl : ∀ (a : List (List Ty)), Ty.beqCtors a a = true
  | [] => by simp [Ty.beqCtors]
  | a :: as => by simp [Ty.beqCtors, Ty.beqList_refl a, Ty.beqCtors_refl as]

/-- The same, for the fields of a record of closed types. -/
theorem beqA2_refl : ∀ (a : LeanRecordSchema Ty), Ty.beqA2 a a = true
  | ⟨a1, a2, as⟩ => by
      simp [Ty.beqA2, Ty.beq_refl a1, Ty.beq_refl a2, Ty.beqList_refl as]

/-- The same, for the fields of a constructor that has at least one. -/
theorem beqNE_refl : ∀ (a : NonEmptyList Ty), Ty.beqNE a a = true
  | ⟨f, fs⟩ => by simp [Ty.beqNE, Ty.beq_refl f, Ty.beqList_refl fs]

/-- The same, for the constructors of a tagged union of closed types. -/
theorem beqTU_refl : ∀ (a : LeanTaggedUnionSchema Ty), Ty.beqTU a a = true
  | .payloadFirst f n r => by
      simp [Ty.beqTU, Ty.beqNE_refl f, Ty.beqList_refl n, Ty.beqCtors_refl r]
  | .skip a => by simp [Ty.beqTU, Ty.beqCP_refl a]

/-- The same, for the constructors that follow a field-less one. -/
theorem beqCP_refl : ∀ (a : CtorsWithPayload Ty), Ty.beqCP a a = true
  | .here f r => by simp [Ty.beqCP, Ty.beqNE_refl f, Ty.beqCtors_refl r]
  | .skip a => by simp [Ty.beqCP, Ty.beqCP_refl a]

/-- Every type inside a recursive declaration compares equal to itself. -/
theorem RTy.beq_refl : ∀ (a : RTy), RTy.beq a a = true
  | .self _ => by simp [RTy.beq]
  | .prim _ => by simp [RTy.beq]
  | .typeParam => by simp [RTy.beq]
  | .fnTy s => by simp [RTy.beq, RTy.beqFn_refl s]
  | .primCovariant s => by simp [RTy.beq, RTy.beqCov_refl s]
  | .enum _ => by simp [RTy.beq]
  | .record a => by simp [RTy.beq, RTy.beqA2_refl a]
  | .taggedUnion a => by simp [RTy.beq, RTy.beqTU_refl a]
  | .recTaggedUnion a => by simp [RTy.beq, RTy.beqRecTU_refl a]
  | .recObject a => by simp [RTy.beq, RTy.beqRecObj_refl a]
  | .recAlias a => by simp [RTy.beq, RTy.beqAlias_refl a]
  | .mutualRecursiveFamily a => by simp [RTy.beq, RTy.beqFamily_refl a]

/-- The same, for a function type. -/
theorem RTy.beqFn_refl : ∀ (a : TyFn RTy), RTy.beqFn a a = true
  | .fn ps r => by simp [RTy.beqFn, RTy.beqList_refl ps, RTy.beq_refl r]
  | .fn_returnsProd ps r rs => by
      simp [RTy.beqFn, RTy.beqList_refl ps, RTy.beq_refl r, RTy.beqList_refl rs]

/-- The same, for an invariant type former. -/
theorem RTy.beqCov_refl : ∀ (a : LeanPrimTyCovariant RTy), RTy.beqCov a a = true
  | .array a => by simp [RTy.beqCov, RTy.beq_refl a]
  | .list a => by simp [RTy.beqCov, RTy.beq_refl a]
  | .task a => by simp [RTy.beqCov, RTy.beq_refl a]
  | .promise a => by simp [RTy.beqCov, RTy.beq_refl a]
  | .thunk a => by simp [RTy.beqCov, RTy.beq_refl a]
  | .lazy a => by simp [RTy.beqCov, RTy.beq_refl a]

/-- The same, for a list of types. -/
theorem RTy.beqList_refl : ∀ (a : List RTy), RTy.beqList a a = true
  | [] => by simp [RTy.beqList]
  | a :: as => by simp [RTy.beqList, RTy.beq_refl a, RTy.beqList_refl as]

/-- The same, for the constructors of a layout. -/
theorem RTy.beqCtors_refl : ∀ (a : List (List RTy)), RTy.beqCtors a a = true
  | [] => by simp [RTy.beqCtors]
  | a :: as => by simp [RTy.beqCtors, RTy.beqList_refl a, RTy.beqCtors_refl as]

/-- The same, for the fields of a record. -/
theorem RTy.beqA2_refl : ∀ (a : LeanRecordSchema RTy), RTy.beqA2 a a = true
  | ⟨a1, a2, as⟩ => by
      simp [RTy.beqA2, RTy.beq_refl a1, RTy.beq_refl a2, RTy.beqList_refl as]

/-- The same, for the fields of a constructor that has at least one. -/
theorem RTy.beqNE_refl : ∀ (a : NonEmptyList RTy), RTy.beqNE a a = true
  | ⟨f, fs⟩ => by simp [RTy.beqNE, RTy.beq_refl f, RTy.beqList_refl fs]

/-- The same, for the constructors of a tagged union. -/
theorem RTy.beqTU_refl : ∀ (a : LeanTaggedUnionSchema RTy), RTy.beqTU a a = true
  | .payloadFirst f n r => by
      simp [RTy.beqTU, RTy.beqNE_refl f, RTy.beqList_refl n, RTy.beqCtors_refl r]
  | .skip a => by simp [RTy.beqTU, RTy.beqCP_refl a]

/-- The same, for the constructors that follow a field-less one. -/
theorem RTy.beqCP_refl : ∀ (a : CtorsWithPayload RTy), RTy.beqCP a a = true
  | .here f r => by simp [RTy.beqCP, RTy.beqNE_refl f, RTy.beqCtors_refl r]
  | .skip a => by simp [RTy.beqCP, RTy.beqCP_refl a]

/-- The same, for one member of a mutual family. -/
theorem RTy.beqFam_refl : ∀ (a : FamMember), RTy.beqFam a a = true
  | .ctors a => by simp [RTy.beqFam, RTy.beqTU_refl a]
  | .record a => by simp [RTy.beqFam, RTy.beqA2_refl a]
  | .alias a => by simp [RTy.beqFam, RTy.beq_refl a]

/-- The same, for a list of members. -/
theorem RTy.beqFamList_refl : ∀ (a : List FamMember), RTy.beqFamList a a = true
  | [] => by simp [RTy.beqFamList]
  | a :: as => by simp [RTy.beqFamList, RTy.beqFam_refl a, RTy.beqFamList_refl as]

/-- The same, for a mutual family. -/
theorem RTy.beqFamily_refl : ∀ (a : LeanMutualRecFamily RTy), RTy.beqFamily a a = true
  | .selectedThenMore b c n a => by
      simp [RTy.beqFamily, RTy.beqFamList_refl b, RTy.beqFam_refl c, RTy.beqFam_refl n,
        RTy.beqFamList_refl a]
  | .selectedLast f b c => by
      simp [RTy.beqFamily, RTy.beqFam_refl f, RTy.beqFamList_refl b, RTy.beqFam_refl c]

end

instance : DecidableEq Ty := fun a b =>
  decidable_of_iff (Ty.beq a b = true) ⟨Ty.eq_of_beq, fun h => h ▸ Ty.beq_refl a⟩

instance : BEq Ty := ⟨Ty.beq⟩

instance : DecidableEq RTy := fun a b =>
  decidable_of_iff (RTy.beq a b = true) ⟨RTy.eq_of_beq, fun h => h ▸ RTy.beq_refl a⟩

instance : BEq RTy := ⟨RTy.beq⟩

instance : Inhabited Ty := ⟨.typeParam⟩
instance : Inhabited RTy := ⟨.typeParam⟩

/-! ## The shared type formers, as abbreviations

`Ty.fnTy` and `Ty.primCovariant` are the only way to build a function, an array, a list,
a task, a promise or a thunk, but writing `.primCovariant (.array α)` everywhere is
noise, so each former is also available directly under `Ty` and `RTy`.  They are
`@[match_pattern]`, so `.array α` works in a pattern as well as in a term. -/

/-- An uncurried function type. -/
@[match_pattern] abbrev fn (params : List Ty) (ret : Ty) : Ty := .fnTy (.fn params ret)
/-- A function answering with several values at once. -/
@[match_pattern] abbrev fn_returnsProd (params : List Ty) (ret1 : Ty) (retRest : List Ty) :
    Ty := .fnTy (.fn_returnsProd params ret1 retRest)
/-- In JS: an array. -/
@[match_pattern] abbrev array (α : Ty) : Ty := .primCovariant (.array α)
/-- A cons list. -/
@[match_pattern] abbrev list (α : Ty) : Ty := .primCovariant (.list α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev task (α : Ty) : Ty := .primCovariant (.task α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev promise (α : Ty) : Ty := .primCovariant (.promise α)
/-- A thunk. -/
@[match_pattern] abbrev thunk (α : Ty) : Ty := .primCovariant (.thunk α)

/-- A JS function of no arguments answering with an `α`: what a Lean `Unit → α` is once
    its erased argument is dropped. -/
@[match_pattern] abbrev lazy (α : Ty) : Ty := .primCovariant (.lazy α)

namespace RTy

/-- An uncurried function type, inside a recursive declaration. -/
@[match_pattern] abbrev fn (params : List RTy) (ret : RTy) : RTy := .fnTy (.fn params ret)
/-- A function answering with several values at once. -/
@[match_pattern] abbrev fn_returnsProd (params : List RTy) (ret1 : RTy)
    (retRest : List RTy) : RTy := .fnTy (.fn_returnsProd params ret1 retRest)
/-- In JS: an array. -/
@[match_pattern] abbrev array (α : RTy) : RTy := .primCovariant (.array α)
/-- A cons list. -/
@[match_pattern] abbrev list (α : RTy) : RTy := .primCovariant (.list α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev task (α : RTy) : RTy := .primCovariant (.task α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev promise (α : RTy) : RTy := .primCovariant (.promise α)
/-- A thunk. -/
@[match_pattern] abbrev thunk (α : RTy) : RTy := .primCovariant (.thunk α)

/-- A JS function of no arguments; see `Ty.lazy`. -/
@[match_pattern] abbrev lazy (α : RTy) : RTy := .primCovariant (.lazy α)

end RTy

/-! ## The terminal types, as `Ty` abbreviations

`Ty.prim` is the only leaf constructor, but writing `.prim .nat` everywhere is noise,
so each `LeanPrimTy` is also available directly under the `Ty` namespace — which is what
makes `.nat`, `.uint32`, `.bitvec 32`, … keep working in a position expecting a
`Ty`. -/

/-- In JS: `boolean`.  Every two-constructor field-less sum is modelled as this. -/
abbrev bool : Ty := .prim .bool
/-- In JS: `number` or `bigint`. -/
abbrev nat : Ty := .prim .nat
/-- In JS: `number` or `bigint`. -/
abbrev int : Ty := .prim .int
/-- In JS: `number` or `bigint`, by width. -/
abbrev bitvec (n : Nat) (h_pos : 0 < n := by decide) : Ty := .prim (.bitvec n h_pos)
/-- In JS: `number`. -/
abbrev uint8 : Ty := .prim .uint8
/-- In JS: `number`. -/
abbrev uint16 : Ty := .prim .uint16
/-- In JS: `number`. -/
abbrev uint32 : Ty := .prim .uint32
/-- In JS: `number` or `bigint`. -/
abbrev uint64 : Ty := .prim .uint64
/-- In JS: `number` or `bigint`. -/
abbrev usize : Ty := .prim .usize
/-- In JS: `number`. -/
abbrev int8 : Ty := .prim .int8
/-- In JS: `number`. -/
abbrev int16 : Ty := .prim .int16
/-- In JS: `number`. -/
abbrev int32 : Ty := .prim .int32
/-- In JS: `number` or `bigint`. -/
abbrev int64 : Ty := .prim .int64
/-- In JS: `number` or `bigint`. -/
abbrev isize : Ty := .prim .isize
/-- In JS: `string`. -/
abbrev char : Ty := .prim .char
/-- In JS: `string`. -/
abbrev string : Ty := .prim .string
/-- In JS: `Uint8Array`. -/
abbrev byteArray : Ty := .prim .byteArray
/-- A `Lean.Name`. -/
abbrev name : Ty := .prim .name
/-- A position in a string. -/
abbrev stringPos : Ty := .prim .stringPos
/-- In JS: `{ str, startPos, stopPos }`. -/
abbrev substring : Ty := .prim .substring
/-- A slice of a string. -/
abbrev stringSlice : Ty := .prim .stringSlice
/-- In JS: `number` (IEEE 754 64-bit). -/
abbrev float : Ty := .prim .float
/-- In JS: `number` (IEEE 754 32-bit). -/
abbrev float32 : Ty := .prim .float32
/-- In JS: `Float64Array`. -/
abbrev floatArray : Ty := .prim .floatArray
/-- `Ordering` is the enum with three constructors whose numbering starts at `-1`, so
    it prints as `-1 | 0 | 1` — the numbering the comparison functions of the runtime
    answer with.  It is not a terminal type of its own: `Ty.enum` with a shift is what
    a specially numbered enum is. -/
abbrev ordering : Ty := .enum ⟨0, -1⟩
/-- In JS (node only): a `ChildProcess` handle. -/
abbrev childProcess : Ty := .prim .childProcess
/-- In JS: `object` / `any`. -/
abbrev shareCommonObject : Ty := .prim .shareCommonObject
/-- In JS: a `Map` / cache object. -/
abbrev shareCommonState : Ty := .prim .shareCommonState

/-- The enum with `n` constructors numbered from `shift` — `none` unless `n` is a number
    of constructors an enum can have, which is three or more: with none the type has no
    values, with one it is a unit type and is erased, and with two it is `Ty.bool`. -/
def enumOfCount? (n : Nat) (shift : Int := 0) : Option Ty :=
  (LeanEnumSchema.ofCount? n shift).map Ty.enum

/-- The type of a field-less sum with `n` constructors: `Ty.bool` for two of them and an
    enum for three or more.  `none` for the two degenerate cases, which have no type:
    a sum with no constructors has no values, and one with a single constructor is a
    unit type, which is erased. -/
def enumOrBool? (n : Nat) (shift : Int := 0) : Option Ty :=
  if n == 2 && shift == 0 then some Ty.bool else enumOfCount? n shift

namespace RTy

/-- The enum with `n` constructors numbered from `shift`, one layer down; `none` unless
    `n` is a number of constructors an enum can have. -/
def enumOfCount? (n : Nat) (shift : Int := 0) : Option RTy :=
  (LeanEnumSchema.ofCount? n shift).map RTy.enum

/-- The type of a field-less sum with `n` constructors, one layer down: `RTy.prim .bool`
    for two of them and an enum for three or more, and `none` for the degenerate
    cases. -/
def enumOrBool? (n : Nat) (shift : Int := 0) : Option RTy :=
  if n == 2 && shift == 0 then some (.prim .bool) else enumOfCount? n shift

end RTy

/-- A one-parameter function type: `a ⇒ b` is `Ty.fn [a] b`. -/
abbrev arrow (a b : Ty) : Ty := Ty.fn [a] b

/-- `Unit → α` — a JS function of zero parameters. -/
abbrev nullary (ret : Ty) : Ty := Ty.fn [] ret

/-- `Option α`: a non-recursive sum whose constructor `0` (`none`) carries nothing and
    whose constructor `1` (`some`) carries the value. -/
abbrev option (α : Ty) : Ty := .taggedUnion (.skip (.here ⟨α, []⟩ []))

/-- `α × β`: one constructor with two fields. -/
abbrev prod (α β : Ty) : Ty := .record ⟨α, β, []⟩

infixr:70 " ⇒ " => Ty.arrow

end Ty

end LakeJs

end
