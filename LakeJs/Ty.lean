module

public import LakeJs.LeanPrimTy

@[expose] public section

namespace LakeJs

/-!
# `Ty`: the types that can be compiled to JavaScript

`Ty` is a **tree of types**.  There are no schemas, no names and no side tables: a type
is built out of its own parts, and two types are equal when their trees are equal.

Five decisions are baked into it.

* **no names anywhere.**  A constructor is a *position* in the list of constructors and
  a field is a *position* in the list of fields, so a value of a user-defined type is
  `{ tag: 0, _1: …, _2: … }` — a number and positional fields, never a string.

* **ordinary equality.**  `Ty` is a first-order inductive with a `DecidableEq` instance
  (`Ty.beq` and the lemmas below), so two types are compared with `=` and `decide`.

* **nothing erased.**  A value that carries no information at run time — a proof, a
  type argument — has no `Ty` at all: it is dropped when LCNF is translated.  So there
  is no `Ty.unit`, no `Ty.void`, no `Ty.erased`, and `bitvec n` needs `n ≥ 1`.

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

## The shapes a user-defined type can have

A Lean declaration is modelled by *which* of the following shapes it has, so a
traversal never has to ask a schema what kind of declaration it came from:

| Lean                                              | `Ty`                                   |
| :------------------------------------------------ | :------------------------------------- |
| `inductive Dir \| north \| south`                  | `.enum 2 0`  (a proof of `2 > 0` is filled in) |
| `structure Point where x y : Nat`                  | `.record [.nat, .nat]`                 |
| `structure Wrap where v : Nat` (a newtype)         | `.nat` — the wrapper is erased         |
| `Option Nat`                                       | `.taggedUnion [[], [.nat]]`            |
| `inductive T \| leaf \| node : T → T → T`          | `.recTaggedUnion [[], [.self 0, .self 0]]` |
| `structure Tree where n : Nat; kids : Array Tree`  | `.recObject [.nat, .array (.self 0)]`  |
| `structure Rose where kids : Array Rose`           | `.recAlias (.array (.self 0))`         |
| a mutual block                                     | `.mutualRecursiveFamily members i`     |

## `.self` is available in the recursive shapes and nowhere else

The recursive shapes — `recTaggedUnion`, `recObject`, `recAlias` and
`mutualRecursiveFamily` — are the *binders* of the type language: their children are
`RTy`s, the types *inside a recursive declaration*, and `RTy.self i` is an occurrence of
member `i` of that declaration (`i = 0` unless the binder is a mutual family).  The
other shapes carry ordinary `Ty`s, which have no `.self` constructor at all, so a type
outside a recursive declaration cannot mention one: the old `Ty.selfRef`, which was
representable at the top level and meaningless there, is gone.

`RTy` mirrors `Ty`, so anything may appear inside a recursive declaration — a `Nat`, an
`Option Tree` (`.taggedUnion [[], [.self 0]]`), an `Array Tree`.  Where an `RTy` is
itself a *recursive* shape, it opens a new scope: the `.self` of its children is that
inner declaration, exactly as a nested binder shadows an outer one.

## The shared type formers

`fn`, `fn_returnsProd`, `array`, `list`, `task`, `promise` and `thunk` say nothing about
recursion, and each of them makes sense at every layer.  They are therefore *not*
constructors of `Ty` and of `RTy` twice over: they are the constructors of one
parameterised inductive, `Shape`, which both layers embed (`Ty.shape`, `RTy.shape`).
`Ty.fn`, `Ty.array`, … remain available — and usable in patterns — as abbreviations for
`Ty.shape (Shape.fn …)`, `Ty.shape (Shape.array …)`, and so on.
-/

/-! ## The shared type formers -/

namespace Ty

/-- The type formers that carry types but say nothing about recursion, and so are
    shared by every layer of the type language: `Ty` and `RTy` both embed them.

    `α` is the layer's own type: `Shape Ty` for a closed type, `Shape RTy` for a type
    inside a recursive declaration. -/
inductive Shape (α : Type) where
  /-- A JS function, taking 0 or more parameters and returning a value.  It compiles
      to an **uncurried** JS function, so Lean's `def foo : Int → Int → Int` is
      `.fn [.int] (.fn [.int] .int)`.  A function returning nothing is unrepresentable:
      the only reason to have one is an effect, and the source language is pure. -/
  | fn : List α → α → Shape α
  /-- A JS function answering with **several** values at once: it compiles to an
      uncurried function whose `return` is an array literal, so
      `def foo : Int × Float → Int × Float → Int × Float` is
      `.fn [.int, .float] (.fn_returnsProd [.int, .float] .int [.float])` and prints as
      `(v0, v1) => (v2, v3) => { return [1, 1.0]; }`.

      The list of results is non-empty by construction, spelled as a first result and
      the rest. -/
  | fn_returnsProd : (params : List α) → (ret1 : α) → (retRest : List α) → Shape α

end Ty

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
  | typeParam : Ty
  /-- One of the shared type formers: a function, an array, a list, a task, a promise
      or a thunk.  `Ty.fn`, `Ty.array`, … abbreviate the common cases. -/
  | shape : Ty.Shape Ty → Ty
  /-- A non-recursive sum whose constructors all have no fields: `n` of them, printed
      as the plain numbers `shift`, `shift + 1`, …, `shift + n - 1`.

      `shift` is what unites an ordinary enum with the ones whose numbering Lean fixes:
      `inductive Dir | north | south` is `.enum 2 0` and prints as `0 | 1`, while
      `Ordering` is `.enum 3 (-1)` and prints as `-1 | 0 | 1`, which is the numbering
      the runtime comparison functions answer with.

      `nOfConstructors` is **positive**: a type with no constructors at all has no
      values, so it is not a type a compiled declaration can mention, and `Empty`-like
      types are ruled out by construction.  The proof is an auto-param, so a literal
      number needs no extra argument: `.enum 2 0` elaborates. -/
  | enum : (nOfConstructors : Nat) → (h_nonEmpty : nOfConstructors > 0 := by decide) →
      (shift : Int) → Ty
  /-- A non-recursive single-constructor type with ≥ 2 fields, in declaration order.
      In JS: `{ tag: 0, _1: …, _2: … }`.  A *one*-field record is a newtype: it is
      erased, and its `Ty` is the field's own `Ty`. -/
  | record : List Ty → Ty
  /-- A non-recursive sum type with fields (`Option`, `Except`, …): one entry per
      constructor, in declaration order, each holding the types of that constructor's
      fields.  In JS: `{ tag: 1, _1: … }`. -/
  | taggedUnion : List (List Ty) → Ty
  /-- A recursive sum type (`MyList`, a tree, …): one entry per constructor, each
      holding the types of its fields, in which `RTy.self 0` is an occurrence of the
      declaration itself.  In JS: `{ tag: …, … }`. -/
  | recTaggedUnion : List (List Ty.RTy) → Ty
  /-- A recursive single-constructor type with ≥ 2 fields
      (`structure Tree where n : Nat; kids : Array Tree`), in which `RTy.self 0` is an
      occurrence of the declaration itself.  In JS: `{ tag: 0, _1: …, _2: … }`. -/
  | recObject : List Ty.RTy → Ty
  /-- A recursive **newtype**, with the wrapper erased
      (`structure Rose where kids : Array Rose`): the fixed point of the single field's
      type.  In JS a `Rose` is just `[…]`, an array of arrays of …, with no object
      wrapper — `[[], [[], []]]` is a `Rose`. -/
  | recAlias : Ty.RTy → Ty
  /-- One member of a genuinely mutual recursive family: the bodies of *all* of its
      members, in declaration order, and which of them this type is.  Inside them,
      `RTy.self i` is an occurrence of member `i`, so a type never points outside its
      family.  A member that is a newtype is an *alias member* (`FamMember.alias`):
      like `Ty.recAlias` it has no object of its own, and a value of it is a value of
      its single field. -/
  | mutualRecursiveFamily : (members : List Ty.FamMember) → (member : Nat) → Ty

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
  | typeParam : Ty.RTy
  /-- One of the shared type formers, over types that may mention `.self`. -/
  | shape : Ty.Shape Ty.RTy → Ty.RTy
  /-- A non-recursive enum; see `Ty.enum`.  As there, `nOfConstructors` is positive. -/
  | enum : (nOfConstructors : Nat) → (h_nonEmpty : nOfConstructors > 0 := by decide) →
      (shift : Int) → Ty.RTy
  /-- A single-constructor record; see `Ty.record`.  Its fields may mention `.self`
      (`structure Pair where fst : Tree; snd : Tree` inside `Tree`). -/
  | record : List Ty.RTy → Ty.RTy
  /-- A sum type with fields; see `Ty.taggedUnion`.  `Option Tree` inside `Tree` is
      `.taggedUnion [[], [.self 0]]`. -/
  | taggedUnion : List (List Ty.RTy) → Ty.RTy
  /-- A *nested* recursive sum type: it opens a new scope, so the `.self` of its own
      children is this inner declaration, not the enclosing one. -/
  | recTaggedUnion : List (List Ty.RTy) → Ty.RTy
  /-- A nested recursive record; it opens a new scope, as `recTaggedUnion` does. -/
  | recObject : List Ty.RTy → Ty.RTy
  /-- A nested recursive newtype; it opens a new scope, as `recTaggedUnion` does. -/
  | recAlias : Ty.RTy → Ty.RTy
  /-- A nested mutual recursive family; it opens a new scope, as `recTaggedUnion`
      does. -/
  | mutualRecursiveFamily : (members : List Ty.FamMember) → (member : Nat) → Ty.RTy

/-- One member of a mutual recursive family, as the body it contributes. -/
inductive Ty.FamMember where
  /-- A member with constructors: one entry per constructor, each holding the types of
      its fields.  A member with a single constructor and ≥ 2 fields is a record, and
      one whose constructors all have no fields is an enum; both are this. -/
  | ctors : List (List Ty.RTy) → Ty.FamMember
  /-- A member that is a newtype: it has no object of its own, and a value of it is a
      value of this, its single field. -/
  | alias : Ty.RTy → Ty.FamMember

end

namespace Ty

/-! ## Deciding equality

`Ty` holds lists of lists of types, and `Shape`s of them, which no `deriving` handler
covers, so the instance is written out: a structural `Ty.beq` over the whole mutual
family, and the two lemmas that make it equality. -/

mutual

/-- Structural equality of two closed types. -/
def beq : Ty → Ty → Bool
  | .prim p, .prim q => p == q
  | .typeParam, .typeParam => true
  | .shape s, .shape t => Ty.beqShape s t
  | .enum n _ s, .enum m _ t => n == m && s == t
  | .record a, .record b => Ty.beqList a b
  | .taggedUnion a, .taggedUnion b => Ty.beqCtors a b
  | .recTaggedUnion a, .recTaggedUnion b => RTy.beqCtors a b
  | .recObject a, .recObject b => RTy.beqList a b
  | .recAlias a, .recAlias b => RTy.beq a b
  | .mutualRecursiveFamily ms i, .mutualRecursiveFamily ns j =>
      FamMember.beqList ms ns && i == j
  | _, _ => false

/-- Structural equality of two shared type formers over closed types. -/
def beqShape : Shape Ty → Shape Ty → Bool
  | .fn ps r, .fn qs s => Ty.beqList ps qs && Ty.beq r s
  | .fn_returnsProd ps r rs, .fn_returnsProd qs s ss =>
      Ty.beqList ps qs && Ty.beq r s && Ty.beqList rs ss
  | .array a, .array b => Ty.beq a b
  | .list a, .list b => Ty.beq a b
  | .task a, .task b => Ty.beq a b
  | .promise a, .promise b => Ty.beq a b
  | .thunk a, .thunk b => Ty.beq a b
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

/-- Structural equality of two types inside a recursive declaration. -/
def RTy.beq : RTy → RTy → Bool
  | .self i, .self j => i == j
  | .prim p, .prim q => p == q
  | .typeParam, .typeParam => true
  | .shape s, .shape t => RTy.beqShape s t
  | .enum n _ s, .enum m _ t => n == m && s == t
  | .record a, .record b => RTy.beqList a b
  | .taggedUnion a, .taggedUnion b => RTy.beqCtors a b
  | .recTaggedUnion a, .recTaggedUnion b => RTy.beqCtors a b
  | .recObject a, .recObject b => RTy.beqList a b
  | .recAlias a, .recAlias b => RTy.beq a b
  | .mutualRecursiveFamily ms i, .mutualRecursiveFamily ns j =>
      FamMember.beqList ms ns && i == j
  | _, _ => false

/-- Structural equality of two shared type formers over types that may mention
    `.self`. -/
def RTy.beqShape : Shape RTy → Shape RTy → Bool
  | .fn ps r, .fn qs s => RTy.beqList ps qs && RTy.beq r s
  | .fn_returnsProd ps r rs, .fn_returnsProd qs s ss =>
      RTy.beqList ps qs && RTy.beq r s && RTy.beqList rs ss
  | .array a, .array b => RTy.beq a b
  | .list a, .list b => RTy.beq a b
  | .task a, .task b => RTy.beq a b
  | .promise a, .promise b => RTy.beq a b
  | .thunk a, .thunk b => RTy.beq a b
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

/-- Structural equality of two members of a mutual family. -/
def FamMember.beq : FamMember → FamMember → Bool
  | .ctors a, .ctors b => RTy.beqCtors a b
  | .alias a, .alias b => RTy.beq a b
  | _, _ => false

/-- `FamMember.beq`, on the members of a family. -/
def FamMember.beqList : List FamMember → List FamMember → Bool
  | [], [] => true
  | a :: as, b :: bs => FamMember.beq a b && FamMember.beqList as bs
  | _, _ => false

end

mutual

/-- Closed types that compare equal are equal. -/
theorem eq_of_beq : ∀ {a b : Ty}, Ty.beq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beq]
  · exact Ty.eq_of_beqShape h
  · exact Ty.eq_of_beqList h
  · exact Ty.eq_of_beqCtors h
  · exact RTy.eq_of_beqCtors h
  · exact RTy.eq_of_beqList h
  · exact RTy.eq_of_beq h
  · simp [FamMember.eq_of_beqList h.1]

/-- The same, for the shared type formers over closed types. -/
theorem eq_of_beqShape : ∀ {a b : Shape Ty}, Ty.beqShape a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqShape]
  · exact ⟨Ty.eq_of_beqList h.1, Ty.eq_of_beq h.2⟩
  · exact ⟨Ty.eq_of_beqList h.1.1, Ty.eq_of_beq h.1.2, Ty.eq_of_beqList h.2⟩
  · exact Ty.eq_of_beq h
  · exact Ty.eq_of_beq h
  · exact Ty.eq_of_beq h
  · exact Ty.eq_of_beq h
  · exact Ty.eq_of_beq h

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

/-- Types inside a recursive declaration that compare equal are equal. -/
theorem RTy.eq_of_beq : ∀ {a b : RTy}, RTy.beq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beq]
  · exact RTy.eq_of_beqShape h
  · exact RTy.eq_of_beqList h
  · exact RTy.eq_of_beqCtors h
  · exact RTy.eq_of_beqCtors h
  · exact RTy.eq_of_beqList h
  · exact RTy.eq_of_beq h
  · simp [FamMember.eq_of_beqList h.1]

/-- The same, for the shared type formers. -/
theorem RTy.eq_of_beqShape : ∀ {a b : Shape RTy}, RTy.beqShape a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqShape]
  · exact ⟨RTy.eq_of_beqList h.1, RTy.eq_of_beq h.2⟩
  · exact ⟨RTy.eq_of_beqList h.1.1, RTy.eq_of_beq h.1.2, RTy.eq_of_beqList h.2⟩
  · exact RTy.eq_of_beq h
  · exact RTy.eq_of_beq h
  · exact RTy.eq_of_beq h
  · exact RTy.eq_of_beq h
  · exact RTy.eq_of_beq h

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

/-- The same, for one member of a mutual family. -/
theorem FamMember.eq_of_beq : ∀ {a b : FamMember}, FamMember.beq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [FamMember.beq]
  · exact RTy.eq_of_beqCtors h
  · exact RTy.eq_of_beq h

/-- The same, for the members of a family. -/
theorem FamMember.eq_of_beqList :
    ∀ {a b : List FamMember}, FamMember.beqList a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [FamMember.beqList]
  exact ⟨FamMember.eq_of_beq h.1, FamMember.eq_of_beqList h.2⟩

end

mutual

/-- Every closed type compares equal to itself. -/
theorem beq_refl : ∀ (a : Ty), Ty.beq a a = true
  | .prim _ => by simp [Ty.beq]
  | .typeParam => by simp [Ty.beq]
  | .shape s => by simp [Ty.beq, Ty.beqShape_refl s]
  | .enum _ _ _ => by simp [Ty.beq]
  | .record a => by simp [Ty.beq, Ty.beqList_refl a]
  | .taggedUnion a => by simp [Ty.beq, Ty.beqCtors_refl a]
  | .recTaggedUnion a => by simp [Ty.beq, RTy.beqCtors_refl a]
  | .recObject a => by simp [Ty.beq, RTy.beqList_refl a]
  | .recAlias a => by simp [Ty.beq, RTy.beq_refl a]
  | .mutualRecursiveFamily ms _ => by simp [Ty.beq, FamMember.beqList_refl ms]

/-- The same, for the shared type formers over closed types. -/
theorem beqShape_refl : ∀ (a : Shape Ty), Ty.beqShape a a = true
  | .fn ps r => by simp [Ty.beqShape, Ty.beqList_refl ps, Ty.beq_refl r]
  | .fn_returnsProd ps r rs => by
      simp [Ty.beqShape, Ty.beqList_refl ps, Ty.beq_refl r, Ty.beqList_refl rs]
  | .array a => by simp [Ty.beqShape, Ty.beq_refl a]
  | .list a => by simp [Ty.beqShape, Ty.beq_refl a]
  | .task a => by simp [Ty.beqShape, Ty.beq_refl a]
  | .promise a => by simp [Ty.beqShape, Ty.beq_refl a]
  | .thunk a => by simp [Ty.beqShape, Ty.beq_refl a]

/-- The same, for a list of closed types. -/
theorem beqList_refl : ∀ (a : List Ty), Ty.beqList a a = true
  | [] => by simp [Ty.beqList]
  | a :: as => by simp [Ty.beqList, Ty.beq_refl a, Ty.beqList_refl as]

/-- The same, for the constructors of a closed layout. -/
theorem beqCtors_refl : ∀ (a : List (List Ty)), Ty.beqCtors a a = true
  | [] => by simp [Ty.beqCtors]
  | a :: as => by simp [Ty.beqCtors, Ty.beqList_refl a, Ty.beqCtors_refl as]

/-- Every type inside a recursive declaration compares equal to itself. -/
theorem RTy.beq_refl : ∀ (a : RTy), RTy.beq a a = true
  | .self _ => by simp [RTy.beq]
  | .prim _ => by simp [RTy.beq]
  | .typeParam => by simp [RTy.beq]
  | .shape s => by simp [RTy.beq, RTy.beqShape_refl s]
  | .enum _ _ _ => by simp [RTy.beq]
  | .record a => by simp [RTy.beq, RTy.beqList_refl a]
  | .taggedUnion a => by simp [RTy.beq, RTy.beqCtors_refl a]
  | .recTaggedUnion a => by simp [RTy.beq, RTy.beqCtors_refl a]
  | .recObject a => by simp [RTy.beq, RTy.beqList_refl a]
  | .recAlias a => by simp [RTy.beq, RTy.beq_refl a]
  | .mutualRecursiveFamily ms _ => by simp [RTy.beq, FamMember.beqList_refl ms]

/-- The same, for the shared type formers. -/
theorem RTy.beqShape_refl : ∀ (a : Shape RTy), RTy.beqShape a a = true
  | .fn ps r => by simp [RTy.beqShape, RTy.beqList_refl ps, RTy.beq_refl r]
  | .fn_returnsProd ps r rs => by
      simp [RTy.beqShape, RTy.beqList_refl ps, RTy.beq_refl r, RTy.beqList_refl rs]
  | .array a => by simp [RTy.beqShape, RTy.beq_refl a]
  | .list a => by simp [RTy.beqShape, RTy.beq_refl a]
  | .task a => by simp [RTy.beqShape, RTy.beq_refl a]
  | .promise a => by simp [RTy.beqShape, RTy.beq_refl a]
  | .thunk a => by simp [RTy.beqShape, RTy.beq_refl a]

/-- The same, for a list of types. -/
theorem RTy.beqList_refl : ∀ (a : List RTy), RTy.beqList a a = true
  | [] => by simp [RTy.beqList]
  | a :: as => by simp [RTy.beqList, RTy.beq_refl a, RTy.beqList_refl as]

/-- The same, for the constructors of a layout. -/
theorem RTy.beqCtors_refl : ∀ (a : List (List RTy)), RTy.beqCtors a a = true
  | [] => by simp [RTy.beqCtors]
  | a :: as => by simp [RTy.beqCtors, RTy.beqList_refl a, RTy.beqCtors_refl as]

/-- The same, for one member of a mutual family. -/
theorem FamMember.beq_refl : ∀ (a : FamMember), FamMember.beq a a = true
  | .ctors a => by simp [FamMember.beq, RTy.beqCtors_refl a]
  | .alias a => by simp [FamMember.beq, RTy.beq_refl a]

/-- The same, for the members of a family. -/
theorem FamMember.beqList_refl : ∀ (a : List FamMember), FamMember.beqList a a = true
  | [] => by simp [FamMember.beqList]
  | a :: as => by simp [FamMember.beqList, FamMember.beq_refl a, FamMember.beqList_refl as]

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

`Ty.shape` and `RTy.shape` are the only way to build a function, an array, a list, a
task, a promise or a thunk, but writing `.shape (.array α)` everywhere is noise, so each
former is also available directly under `Ty` and `RTy`.  They are `@[match_pattern]`, so
`.array α` works in a pattern as well as in a term. -/

/-- An uncurried function type. -/
@[match_pattern] abbrev fn (params : List Ty) (ret : Ty) : Ty := .shape (.fn params ret)
/-- A function answering with several values at once. -/
@[match_pattern] abbrev fn_returnsProd (params : List Ty) (ret1 : Ty) (retRest : List Ty) :
    Ty := .shape (.fn_returnsProd params ret1 retRest)
/-- In JS: an array. -/
@[match_pattern] abbrev array (α : Ty) : Ty := .shape (.array α)
/-- A cons list. -/
@[match_pattern] abbrev list (α : Ty) : Ty := .shape (.list α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev task (α : Ty) : Ty := .shape (.task α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev promise (α : Ty) : Ty := .shape (.promise α)
/-- A thunk. -/
@[match_pattern] abbrev thunk (α : Ty) : Ty := .shape (.thunk α)

namespace RTy

/-- An uncurried function type, inside a recursive declaration. -/
@[match_pattern] abbrev fn (params : List RTy) (ret : RTy) : RTy := .shape (.fn params ret)
/-- A function answering with several values at once. -/
@[match_pattern] abbrev fn_returnsProd (params : List RTy) (ret1 : RTy)
    (retRest : List RTy) : RTy := .shape (.fn_returnsProd params ret1 retRest)
/-- In JS: an array. -/
@[match_pattern] abbrev array (α : RTy) : RTy := .shape (.array α)
/-- A cons list. -/
@[match_pattern] abbrev list (α : RTy) : RTy := .shape (.list α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev task (α : RTy) : RTy := .shape (.task α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev promise (α : RTy) : RTy := .shape (.promise α)
/-- A thunk. -/
@[match_pattern] abbrev thunk (α : RTy) : RTy := .shape (.thunk α)

end RTy

/-! ## The terminal types, as `Ty` abbreviations

`Ty.prim` is the only leaf constructor, but writing `.prim .nat` everywhere is noise,
so each `LeanPrimTy` is also available directly under the `Ty` namespace — which is what
makes `.nat`, `.uint32`, `.bitvec 32`, … keep working in a position expecting a
`Ty`. -/

/-- In JS: `boolean`. -/
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
abbrev ordering : Ty := .enum 3 (shift := -1)
/-- In JS (node only): a `ChildProcess` handle. -/
abbrev childProcess : Ty := .prim .childProcess
/-- In JS: `object` / `any`. -/
abbrev shareCommonObject : Ty := .prim .shareCommonObject
/-- In JS: a `Map` / cache object. -/
abbrev shareCommonState : Ty := .prim .shareCommonState

/-- A one-parameter function type: `a ⇒ b` is `Ty.fn [a] b`. -/
abbrev arrow (a b : Ty) : Ty := Ty.fn [a] b

/-- `Unit → α` — a JS function of zero parameters. -/
abbrev nullary (ret : Ty) : Ty := Ty.fn [] ret

/-- `Option α`: a non-recursive sum whose constructor `0` (`none`) carries nothing and
    whose constructor `1` (`some`) carries the value. -/
abbrev option (α : Ty) : Ty := .taggedUnion [[], [α]]

/-- `α × β`: one constructor with two fields. -/
abbrev prod (α β : Ty) : Ty := .record [α, β]

infixr:70 " ⇒ " => Ty.arrow

end Ty

end LakeJs

end
