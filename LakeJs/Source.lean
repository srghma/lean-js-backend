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

/-- The four observables of the denoted member.  For a genuinely mutual block both
    `isMutual` and `isRecursive` are `true`, as in `familyDescriptor`. -/
def descriptor (d : SrcDecl) : Option ShapeDescriptor :=
  match d.block[d.member]? with
  | none   => none
  | some m =>
      let mut_ := isGenuinelyMutual d.block
      some { isMutual := mut_
           , isRecursive := mut_ || memberMentions m d.member
           , numCtors := m.ctors.length
           , hasFields := memberHasFields m }

/--
**The classification algorithm.**  There is only one, and it is a function of the
four observables alone: `ShapeDescriptor.class?`.  `none` means "not representable":
the member index is out of range, the member is *void* (no constructors) or the
member is *unit-like* (one constructor, no fields).
-/
def classify (d : SrcDecl) : Option ShapeClass :=
  match descriptor d with
  | none => none
  | some desc =>
      if desc.isMutual then some desc.class?
      else if desc.numCtors = 0 then none
      else if desc.numCtors = 1 && !desc.hasFields then none
      else some desc.class?

/-- The classification of a member that is *not* part of a genuine mutual block —
    the same function of the same observables, with `isMutual := false`. -/
def singleClass (self : Nat) (m : SrcMember) : Option ShapeClass :=
  let desc : ShapeDescriptor :=
    { isMutual := false
      isRecursive := memberMentions m self
      numCtors := m.ctors.length
      hasFields := memberHasFields m }
  if desc.numCtors = 0 then none
  else if desc.numCtors = 1 && !desc.hasFields then none
  else some desc.class?

theorem classify_eq_singleClass (d : SrcDecl) (m : SrcMember)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = false) :
    classify d = singleClass d.member m := by
  simp [classify, descriptor, singleClass, hm, hmut]

theorem classify_eq_mutual (d : SrcDecl) (m : SrcMember)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = true) :
    classify d = some .mutualFamily := by
  simp [classify, descriptor, hm, hmut, ShapeDescriptor.class?]

/-! ## Unit-like and void-like declarations are exactly the `none`s

The two `none` cases above are the only ones a *well-formed* declaration can hit: a
member with no constructor has no values, and a member with one field-less
constructor has exactly one value, and both are erased before `Ty`. -/

theorem classify_eq_none_of_void (d : SrcDecl) (m : SrcMember)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = false)
    (h : m.ctors = []) : classify d = none := by
  simp [classify, descriptor, hm, h, hmut]

theorem classify_eq_none_of_unitLike (d : SrcDecl) (m : SrcMember) (c : SrcCtor)
    (hm : d.block[d.member]? = some m) (hmut : isGenuinelyMutual d.block = false)
    (h : m.ctors = [c]) (hf : c.fields = []) :
    classify d = none := by
  simp [classify, descriptor, hm, h, hmut, memberHasFields, hf]

end LakeJs.Source

end
