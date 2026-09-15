module

public import LakeJs.Ty
public import LakeJs.TyDerived
public import LakeJs.SchemaDisjoint

open NonEmpty.String
open LakeJs.SchemaDisjoint

@[expose] public section

/-!
# A model of the Lean declarations that `Ty` is supposed to cover

`LakeJs.TyMeta` reads a schema off a *real* Lean declaration, in `MetaM`.  Nothing
about a `MetaM` program can be proved, so the questions

* *is every Lean datatype (that is not unit-like and not void-like) representable in
  `Ty`?*, and
* *can one declaration be interpreted as two different `Ty`s?*

cannot even be stated against it.  This module states them, against an explicit model
of a declaration block:

* `SrcTy`   — the type of one field, as Lean's own elaborator would present it after
              the compiler front-end has already translated every *foreign* type
              (`Nat`, `Array Int`, another declaration, …) into a `Ty`;
* `SrcCtor`, `SrcMember`, `SrcBlock` — a whole `mutual` block, i.e. exactly the data
  of a list of `InductiveVal`s together with their `ConstructorVal`s, restricted to
  the first-order fragment (see *What the model deliberately excludes* below);
* `SrcDecl` — such a block together with the index of the member being translated.

`LakeJs.SourceToTy` then defines the **one** translation `SrcDecl → Except _ Ty` and
proves that it succeeds exactly on the declarations this compiler claims to support,
and that the shape it picks is forced by four observable facts about the declaration.

## What the model deliberately excludes

A `Ty` describes a JavaScript value, so the model covers the datatypes that *have* a
JavaScript value, and no others.  These Lean declarations are outside it, and no
extension of `FamFieldKind`-style grammars would bring them in:

* **type parameters** (`List α`, `Except ε α`).  A parameterised declaration is a
  *family* of types, not a type; it becomes a `Ty` only once its parameters are
  instantiated, which is what `derive_ty` does (`Ty.option : Ty → Ty`).
* **indices / dependency** (`Vector α n`, `Fin n`, `Eq`, any `inductive … : Nat →
  Type`).  Different indices are different types with the same constructors; the
  runtime value carries no index.
* **universe polymorphism and `Prop`**.  A `Prop` field is erased by the compiler
  before it reaches `Ty`, so `{ n : Nat // 0 < n }` arrives as a one-field record.
* **non-datatypes**: quotients, `Quot`, opaque and foreign types.
* **nested occurrences through another *user* declaration** (`inductive T | node :
  MyTree T → T`).  This is not a gap in the grammar but a different declaration:
  `MyTree T` mentions `T`, so `T` and `MyTree` form one mutual block and the pair is
  a `Ty.mutualRecursiveFamily`.
* **negative occurrences** (`inductive Bad | mk : (Bad → Bad) → Bad`).  Lean rejects
  these too, so the model loses nothing.

Everything else that Lean's positivity checker accepts — including infinitely
branching constructors such as `| lim : (Nat → Ord) → Ord` — is in the model.
-/

namespace LakeJs.Source

/-! ## The source language -/

/--
The type of one field of a constructor of the block being translated.

`ext t` is a type that does **not** mention the block: the front-end has already
turned it into a `Ty`.  `ref i` is an occurrence of member `i` of the block.  The
remaining constructors are the type formers a field may be built from, and they are
exactly those of `SelfTy` / `FamTy`, which is what makes the translation below total.

A member occurrence may not appear in a *parameter* of `fn`: that is a negative
occurrence, which Lean rejects as well.
-/
inductive SrcTy where
  /-- A type not mentioning the block; already translated. -/
  | ext (t : Ty)
  /-- An occurrence of member `member` of the block. -/
  | ref (member : Nat)
  /-- `Array _`. -/
  | array (elem : SrcTy)
  /-- `List _`. -/
  | list (elem : SrcTy)
  /-- `Option _`. -/
  | option (elem : SrcTy)
  /-- `Thunk _`. -/
  | thunk (val : SrcTy)
  /-- `Task _`. -/
  | task (val : SrcTy)
  /-- A promise. -/
  | promise (val : SrcTy)
  /-- A function; its parameters never mention the block. -/
  | fn (params : List Ty) (ret : SrcTy)
  /-- A pair. -/
  | prod (fst snd : SrcTy)

/-- One constructor: its runtime tag and its named fields, in declaration order. -/
structure SrcCtor where
  tag : NonEmptyString
  fields : List (NonEmptyString × SrcTy)

/-- One member of the block: its name and its constructors, in declaration order.
    This is the content of one `InductiveVal` plus its `ConstructorVal`s. -/
structure SrcMember where
  name : NonEmptyString
  ctors : List SrcCtor

/-- A `mutual` block; a single declaration is the one-element list. -/
abbrev SrcBlock := List SrcMember

/-- A block together with the member being translated. -/
structure SrcDecl where
  block : SrcBlock
  member : Nat

/-! ## The shape of a source field type

Every question the schemas ask about a field — which members it mentions, whether a
value of it can be produced without a value of some member — is answered by its
`FamFieldKind`, which is read off the source type by `SrcTy.kind`.  The two bits of
`SelfTy` are functions of the same kind (`kindUses`, `kindAvoids`), so the mutual and
the non-mutual shapes agree by construction on what "recursive" and "base" mean. -/

/-- How a field type uses the block. -/
def SrcTy.kind : SrcTy → FamFieldKind
  | .ext _     => .nonRec
  | .ref i     => .recAt i
  | .array t   => .array t.kind
  | .list t    => .list t.kind
  | .option t  => .option t.kind
  | .thunk t   => .thunk t.kind
  | .task t    => .task t.kind
  | .promise t => .promise t.kind
  | .fn _ r    => .fn r.kind
  | .prod a b  => .prod a.kind b.kind

/-- `!xs.any p` is `xs.all (!p ·)`; used to turn the "mentions" checks into
    "every field is fine" checks. -/
theorem not_any_eq_all_not {α : Type} (xs : List α) (p : α → Bool) :
    (!xs.any p) = xs.all (fun x => !p x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp_all

/-- Does a field of this kind mention the block at all?  This is `SelfTy`'s
    `usesSelf` for a one-member block. -/
def kindUses (k : FamFieldKind) : Bool := !k.targets.isEmpty

/-- Can a value of this kind be produced without a value of any member?  This is
    `SelfTy`'s `avoidsSelf`. -/
def kindAvoids (k : FamFieldKind) : Bool := k.requires.isEmpty

theorem isEmpty_append {α : Type} (xs ys : List α) :
    (xs ++ ys).isEmpty = (xs.isEmpty && ys.isEmpty) := by
  cases xs <;> simp

@[simp] theorem kindUses_prod (k₁ k₂ : FamFieldKind) :
    kindUses (.prod k₁ k₂) = (kindUses k₁ || kindUses k₂) := by
  simp [kindUses, FamFieldKind.targets, isEmpty_append]

@[simp] theorem kindAvoids_prod (k₁ k₂ : FamFieldKind) :
    kindAvoids (.prod k₁ k₂) = (kindAvoids k₁ && kindAvoids k₂) := by
  simp [kindAvoids, FamFieldKind.requires, isEmpty_append]

/-! ## Erasing unit-like and void-like types

No `Ty` is unit-like or void-like, so a field of such a type has no translation — but
that is not a reason to reject the declaration.  A unit-like field carries no
information and is **erased**; a void-like field makes its constructor impossible, so
the *constructor* is erased.  The same applies inside the built-in containers, where
erasing the element type changes the container:

| source type | erased to | why |
| :-- | :-- | :-- |
| `Array Unit`, `List Unit` | `Nat` | only the length is left |
| `Array Empty`, `List Empty` | unit-like | only the empty one exists |
| `Option Unit` | `Bool` | `none` or `some ()` |
| `Option Empty` | unit-like | only `none` exists |
| `Thunk Unit`, `Task Unit`, `α → Unit` | unit-like | the result is the only value |
| `Thunk Empty`, `Task Empty`, `α → Empty` | void-like | cannot be produced |
| `Unit × α` | `α` | the left component is determined |
| `Empty × α` | void-like | cannot be produced |

The *parameters* of `SrcTy.fn` are already `Ty`s, and no `Ty` is unit-like, so a
unit-typed parameter never reaches the model: `Unit → α` arrives as the zero-parameter
`Ty.nullary α`, which is what the front-end produces. -/

/--
The type of one field **before** erasure: the same grammar as `SrcTy`, plus the two
leaves that have no `Ty` at all.  This is what the front-end reads off a Lean
declaration; `RawTy.norm` turns it into a `SrcTy`, or reports that the field, or its
whole constructor, disappears.
-/
inductive RawTy where
  /-- A type not mentioning the block; already translated, so representable. -/
  | ext (t : Ty)
  /-- A **unit-like** type: exactly one value (`Unit`, `PUnit`, `True`, a
      one-constructor field-less declaration, …).  It carries no information, so it
      has no `Ty` and the field carrying it disappears. -/
  | unitLike
  /-- A **void-like** type: no values at all (`Empty`, `False`, a declaration with no
      constructor).  A constructor with such a field can never be applied. -/
  | voidLike
  /-- An occurrence of member `member` of the block. -/
  | ref (member : Nat)
  /-- `Array _`. -/
  | array (elem : RawTy)
  /-- `List _`. -/
  | list (elem : RawTy)
  /-- `Option _`. -/
  | option (elem : RawTy)
  /-- `Thunk _`. -/
  | thunk (val : RawTy)
  /-- `Task _`. -/
  | task (val : RawTy)
  /-- A promise. -/
  | promise (val : RawTy)
  /-- A function; its parameters never mention the block, and are already `Ty`s. -/
  | fn (params : List Ty) (ret : RawTy)
  /-- A pair. -/
  | prod (fst snd : RawTy)

/-- The result of erasing unit-like and void-like types from a field type. -/
inductive NormTy where
  /-- Unit-like: exactly one value, so the field disappears. -/
  | erased
  /-- Void-like: no values, so the enclosing constructor disappears. -/
  | void
  /-- Representable, as this (erased) source type. -/
  | keep (s : SrcTy)
  deriving Inhabited

/-- Erase unit-like and void-like types from a field type, rewriting the containers
    that survive with a different element type (`Array Unit` is a `Nat`). -/
def RawTy.norm : RawTy → NormTy
  | .ext t     => .keep (.ext t)
  | .unitLike  => .erased
  | .voidLike  => .void
  | .ref i     => .keep (.ref i)
  | .array t   =>
      match t.norm with
      | .void   => .erased
      | .erased => .keep (.ext .nat)
      | .keep s => .keep (.array s)
  | .list t    =>
      match t.norm with
      | .void   => .erased
      | .erased => .keep (.ext .nat)
      | .keep s => .keep (.list s)
  | .option t  =>
      match t.norm with
      | .void   => .erased
      | .erased => .keep (.ext .bool)
      | .keep s => .keep (.option s)
  | .thunk t   =>
      match t.norm with
      | .void   => .void
      | .erased => .erased
      | .keep s => .keep (.thunk s)
  | .task t    =>
      match t.norm with
      | .void   => .void
      | .erased => .erased
      | .keep s => .keep (.task s)
  | .promise t =>
      match t.norm with
      | .void   => .void
      | .erased => .erased
      | .keep s => .keep (.promise s)
  | .fn ps r   =>
      match r.norm with
      | .void   => .void
      | .erased => .erased
      | .keep s => .keep (.fn ps s)
  | .prod a b  =>
      match a.norm, b.norm with
      | .void, _        => .void
      | _, .void        => .void
      | .erased, .erased => .erased
      | .erased, .keep s => .keep s
      | .keep s, .erased => .keep s
      | .keep x, .keep y => .keep (.prod x y)

/-- One constructor before erasure. -/
structure RawCtor where
  tag : NonEmptyString
  fields : List (NonEmptyString × RawTy)

/-- One member of the block before erasure. -/
structure RawMember where
  name : NonEmptyString
  ctors : List RawCtor

/-- A `mutual` block before erasure. -/
abbrev RawBlock := List RawMember

/-- A block before erasure, together with the member being translated. -/
structure RawDecl where
  block : RawBlock
  member : Nat

/-- Erase the fields of one constructor; `none` when a field is void-like, which makes
    the constructor itself impossible. -/
def eraseFields :
    List (NonEmptyString × RawTy) → Option (List (NonEmptyString × SrcTy))
  | [] => some []
  | (n, t) :: rest =>
      match t.norm, eraseFields rest with
      | .void, _        => none
      | _, none         => none
      | .erased, some r => some r
      | .keep s, some r => some ((n, s) :: r)

/-- Erase one constructor: `none` when it can never be applied. -/
def RawCtor.erase (c : RawCtor) : Option SrcCtor :=
  (eraseFields c.fields).map fun fs => { tag := c.tag, fields := fs }

/-- Erase one member: impossible constructors go, and so do unit-like fields.  A
    member all of whose constructors disappear is void-like, and a member left with one
    field-less constructor is unit-like; both are rejected by the translation, which is
    where those two cases belong — as is the one left with a single one-field
    constructor, which is a newtype and is erased in turn. -/
def RawMember.erase (m : RawMember) : SrcMember :=
  { name := m.name, ctors := m.ctors.filterMap RawCtor.erase }

/-- Erase a whole block, member by member. -/
def eraseBlock (b : RawBlock) : SrcBlock := b.map RawMember.erase

/-- Erase a declaration.  Everything downstream — the shapes, the observables and the
    translation — reads the *erased* declaration, which is an ordinary `SrcDecl`. -/
def RawDecl.erase (d : RawDecl) : SrcDecl :=
  { block := eraseBlock d.block, member := d.member }

@[simp] theorem eraseBlock_length (b : RawBlock) : (eraseBlock b).length = b.length := by
  simp [eraseBlock]

/-- Every `SrcTy` is already erased: the embedding into `RawTy` normalises to itself. -/
def SrcTy.toRaw : SrcTy → RawTy
  | .ext t     => .ext t
  | .ref i     => .ref i
  | .array t   => .array t.toRaw
  | .list t    => .list t.toRaw
  | .option t  => .option t.toRaw
  | .thunk t   => .thunk t.toRaw
  | .task t    => .task t.toRaw
  | .promise t => .promise t.toRaw
  | .fn ps r   => .fn ps r.toRaw
  | .prod a b  => .prod a.toRaw b.toRaw

theorem norm_toRaw (s : SrcTy) : s.toRaw.norm = .keep s := by
  induction s with
  | ext t | ref i => rfl
  | array t ih | list t ih | option t ih | thunk t ih | task t ih | promise t ih =>
      simp [SrcTy.toRaw, RawTy.norm, ih]
  | fn ps r ih => simp [SrcTy.toRaw, RawTy.norm, ih]
  | prod a b iha ihb => simp [SrcTy.toRaw, RawTy.norm, iha, ihb]

/-! ## The shape of a block

`FamShape` is the common currency: the mutual schema is indexed by it, and the
observables of a *non-mutual* declaration are read off the same data. -/

/-- The fields of one constructor, as a `FamFieldShape`. -/
def ctorShape (c : SrcCtor) : FamCtorShape :=
  (c.tag, c.fields.map (fun f => (f.1, f.2.kind)))

/-- One member, as a `FamMemberShape`. -/
def memberShape (m : SrcMember) : FamMemberShape :=
  (m.name, m.ctors.map ctorShape)

/-- A whole block, as a `FamShape`. -/
def blockShape (b : SrcBlock) : FamShape := b.map memberShape

/-! ## Observables

These are the four facts of `ShapeDescriptor`, computed from the source. -/

/-- Is the block *genuinely* mutual: at least two members whose reference graph is
    strongly connected?  A block that is not genuinely mutual is a collection of
    independent declarations, each with its own `Ty`. -/
def isGenuinelyMutual (b : SrcBlock) : Bool :=
  decide (2 ≤ b.length) && famStronglyConnectedOk (blockShape b)

/-- Does member `i` mention member `j`? -/
def memberMentions (m : SrcMember) (j : Nat) : Bool :=
  m.ctors.any (fun c => c.fields.any (fun f => f.2.kind.targets.contains j))

/-- Does member `i` mention any member other than `self`?  For a declaration that is
    not part of a genuine mutual block this must be `false`: a reference to an
    independent sibling is written `SrcTy.ext`, with that sibling's own `Ty`. -/
def mentionsForeign (m : SrcMember) (self : Nat) : Bool :=
  m.ctors.any (fun c => c.fields.any (fun f => f.2.kind.targets.any (· != self)))

/-- Does some constructor of the member carry a field? -/
def memberHasFields (m : SrcMember) : Bool := m.ctors.any (fun c => !c.fields.isEmpty)

/-- Is the member a **newtype**: exactly one constructor, carrying exactly one field?
    Read on the *erased* member, so a declaration becomes a wrapper as soon as its
    other fields are unit-like. -/
def memberIsWrapper (m : SrcMember) : Bool :=
  match m.ctors with
  | [c] => c.fields.length == 1
  | _   => false

/-- The five observables of the denoted member of an **erased** declaration.  For a
    genuinely mutual block both `isMutual` and `isRecursive` are `true`, as in
    `familyDescriptor`. -/
def descriptor (d : SrcDecl) : Option ShapeDescriptor :=
  match d.block[d.member]? with
  | none   => none
  | some m =>
      let mut_ := isGenuinelyMutual d.block
      some { isMutual := mut_
           , isRecursive := mut_ || memberMentions m d.member
           , numCtors := m.ctors.length
           , hasFields := memberHasFields m
           , isWrapper := memberIsWrapper m }

/-- The observables of a declaration as the front-end reads it, i.e. after erasure. -/
def RawDecl.descriptor (d : RawDecl) : Option ShapeDescriptor := Source.descriptor d.erase

/--
**The classification algorithm**, on an already-erased declaration.  There is only
one, and it is a function of the five observables alone: `ShapeDescriptor.class?`.
`none` means "no shape of its own": the member index is out of range, the member is
*void* (no constructors), the member is *unit-like* (one constructor, no fields), or
the member is a non-recursive *wrapper*, in which case its `Ty` is its single field's
`Ty`.
-/
def classify (d : SrcDecl) : Option ShapeClass :=
  match descriptor d with
  | none => none
  | some desc =>
      if desc.isMutual then desc.class?
      else if desc.numCtors = 0 then none
      else if desc.numCtors = 1 && !desc.hasFields then none
      else desc.class?

/-- The classification of a declaration as the front-end reads it, erasure included. -/
def RawDecl.classify (d : RawDecl) : Option ShapeClass := Source.classify d.erase

/-- The classification of a member that is *not* part of a genuine mutual block —
    the same function of the same observables, with `isMutual := false`. -/
def singleClass (self : Nat) (m : SrcMember) : Option ShapeClass :=
  let desc : ShapeDescriptor :=
    { isMutual := false
      isRecursive := memberMentions m self
      numCtors := m.ctors.length
      hasFields := memberHasFields m
      isWrapper := memberIsWrapper m }
  if desc.numCtors = 0 then none
  else if desc.numCtors = 1 && !desc.hasFields then none
  else desc.class?

theorem classify_eq_singleClass (d : SrcDecl) (m : SrcMember)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = false) :
    classify d = singleClass d.member m := by
  simp [classify, descriptor, singleClass, hm, hmut]

theorem classify_eq_mutual (d : SrcDecl) (m : SrcMember)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = true) :
    classify d = some .mutualFamily := by
  simp [classify, descriptor, hm, hmut, ShapeDescriptor.class?]

/-! ## Unit-like, void-like and wrapper declarations are exactly the `none`s

The `none` cases above are the only ones a *well-formed* declaration can hit: a member
with no constructor has no values; a member with one field-less constructor has
exactly one value; and a non-recursive member with one constructor carrying one field
is its field.  All three are erased before `Ty`. -/

theorem classify_eq_none_of_void (d : SrcDecl) (m : SrcMember)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = false)
    (h : m.ctors = []) : classify d = none := by
  simp [classify, descriptor, hm, h, hmut]

theorem classify_eq_none_of_unitLike (d : SrcDecl) (m : SrcMember) (c : SrcCtor)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = false)
    (h : m.ctors = [c]) (hf : c.fields = []) :
    classify d = none := by
  simp [classify, descriptor, hm, h, hmut, memberHasFields, hf]

/-- A **newtype** that is not recursive has no shape of its own: it is erased into its
    single field's type. -/
theorem classify_eq_none_of_wrapper (d : SrcDecl) (m : SrcMember) (c : SrcCtor)
    (f : NonEmptyString × SrcTy)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = false)
    (h : m.ctors = [c]) (hf : c.fields = [f])
    (hrec : memberMentions m d.member = false) :
    classify d = none := by
  simp [classify, descriptor, hm, h, hmut, hrec, memberHasFields,
    memberIsWrapper, hf, ShapeDescriptor.class?]

/-- A **recursive** newtype is a `recAlias`: the wrapper is erased, but the fixed point
    it leaves behind is a shape. -/
theorem classify_eq_recAlias (d : SrcDecl) (m : SrcMember) (c : SrcCtor)
    (f : NonEmptyString × SrcTy)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = false)
    (h : m.ctors = [c]) (hf : c.fields = [f])
    (hrec : memberMentions m d.member = true) :
    classify d = some .recAlias := by
  simp [classify, descriptor, hm, h, hmut, hrec, memberHasFields,
    memberIsWrapper, hf, ShapeDescriptor.class?]

end LakeJs.Source

end
