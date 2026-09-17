module

public import LakeJs.Ty

@[expose] public section

/-!
# The runtime layout of a type

A user-defined type is one of the shapes of `Ty` (`enum`, `record`, `taggedUnion`,
`recTaggedUnion`, `recObject`, `recAlias`, `mutualRecursiveFamily`).  Its **layout** is
what those shapes have in common as far as the emitted JavaScript is concerned: one
entry per constructor, in declaration order, each holding the types of that
constructor's fields, in declaration order.  `Ty.layout?` computes it, resolving the
occurrences of the declaration inside itself (`RTy.self`), and it is what the data
operations of `LakeJs.Expr` are checked against:

* `Term.ctor` may only use a constructor the layout has, and its arguments are the
  types the layout gives that constructor's fields — so a constructor cannot be built
  with a missing field, an extra field, a field in the wrong place or a field of the
  wrong type;
* `Term.proj` may only read a field the layout has, and the type of the term is the
  type the layout gives that field;
* `Term.caseTag` may only branch on constructors the layout has, and never twice on
  the same one.

A type with no layout has *no* data operation at all: a scalar, a function, an array,
a value of a type parameter (`Ty.typeParam`) — and an **alias**, which is a newtype
whose wrapper is erased.  A value of `Ty.recAlias b`, or of an alias member of a mutual
family, is a value of the type `b` unfolds to (`Ty.aliasUnfold?`), so there is nothing
to read out of it and nothing to build: the wrapper does not exist at run time.

Everything here is positional: a constructor is a number and a field is a number, and
that is exactly what the emitted JavaScript holds (`{ tag: 0, _1: … }`).
-/

namespace LakeJs.Layout

open LakeJs
open LakeJs.Ty

/-- The fields of one constructor, in declaration order. -/
abbrev FieldLayout := List Ty

/-- The constructors of an object type, in declaration order. -/
abbrev ObjLayout := List FieldLayout

mutual

/-- Does this type mention the recursive declaration whose body it sits in?  A *nested*
    recursive shape is not looked into: its `.self`s are its own. -/
def RTy.hasSelf : RTy → Bool
  | .self _ => true
  | .shape s => RTy.hasSelfShape s
  | .record fs => RTy.hasSelfList fs
  | .taggedUnion l => RTy.hasSelfCtors l
  | _ => false

/-- `RTy.hasSelf`, on one of the shared type formers. -/
def RTy.hasSelfShape : Shape RTy → Bool
  | .fn ps r => RTy.hasSelfList ps || RTy.hasSelf r
  | .fn_returnsProd ps r rs => RTy.hasSelfList ps || RTy.hasSelf r || RTy.hasSelfList rs
  | .array a | .list a | .task a | .promise a | .thunk a => RTy.hasSelf a

/-- `RTy.hasSelf`, on a list of types. -/
def RTy.hasSelfList : List RTy → Bool
  | [] => false
  | t :: ts => RTy.hasSelf t || RTy.hasSelfList ts

/-- `RTy.hasSelf`, on the constructors of a layout. -/
def RTy.hasSelfCtors : List (List RTy) → Bool
  | [] => false
  | fs :: l => RTy.hasSelfList fs || RTy.hasSelfCtors l

end

mutual

/-- Replace the occurrences of a recursive declaration inside its own body by the types
    they stand for: `RTy.self i` becomes `rep i`, and everything else is copied.

    A *nested* recursive shape is copied unchanged: its `.self`s belong to it, not to
    the declaration being resolved, which is why this recursion is finite and why a
    `Ty` is a finite tree even though the type it describes is not. -/
def instRTy (rep : Nat → Option Ty) : RTy → Option Ty
  | .self i => rep i
  | .prim p => some (.prim p)
  | .typeParam => some .typeParam
  | .shape s => (instShape rep s).map Ty.shape
  | .enum n h s => some (.enum n h s)
  | .record fs => (instList rep fs).map Ty.record
  | .taggedUnion l => (instCtors rep l).map Ty.taggedUnion
  | .recTaggedUnion l => some (.recTaggedUnion l)
  | .recObject fs => some (.recObject fs)
  | .recAlias b => some (.recAlias b)
  | .mutualRecursiveFamily ms i => some (.mutualRecursiveFamily ms i)

/-- `instRTy`, on one of the shared type formers. -/
def instShape (rep : Nat → Option Ty) : Shape RTy → Option (Shape Ty)
  | .fn ps r => do return .fn (← instList rep ps) (← instRTy rep r)
  | .fn_returnsProd ps r rs => do
      return .fn_returnsProd (← instList rep ps) (← instRTy rep r) (← instList rep rs)
  | .array a => do return .array (← instRTy rep a)
  | .list a => do return .list (← instRTy rep a)
  | .task a => do return .task (← instRTy rep a)
  | .promise a => do return .promise (← instRTy rep a)
  | .thunk a => do return .thunk (← instRTy rep a)

/-- `instRTy`, on a list of types. -/
def instList (rep : Nat → Option Ty) : List RTy → Option (List Ty)
  | [] => some []
  | t :: ts => do return (← instRTy rep t) :: (← instList rep ts)

/-- `instRTy`, on the constructors of a layout. -/
def instCtors (rep : Nat → Option Ty) : List (List RTy) → Option (List (List Ty))
  | [] => some []
  | fs :: l => do return (← instList rep fs) :: (← instCtors rep l)

end

/-- What `RTy.self i` stands for inside a single (non-mutual) recursive declaration:
    the declaration itself, which is member `0` and the only member. -/
def selfRep (τ : Ty) : Nat → Option Ty := fun i => if i == 0 then some τ else none

/-- What `RTy.self i` stands for inside a mutual family: member `i` of that family. -/
def famRep (ms : List FamMember) : Nat → Option Ty := fun i =>
  if i < ms.length then some (.mutualRecursiveFamily ms i) else none

/-- The layout of a type: one entry per constructor, each holding the types of that
    constructor's fields, with the recursive occurrences resolved — or `none` for a
    type that has no constructors at all (a scalar, a function, an array, a value of a
    type parameter) and for an alias, whose wrapper does not exist at run time. -/
def Ty.layout? : Ty → Option ObjLayout
  -- a cons list is the built-in recursive sum: `[]` is `{ tag: 0 }` and `x :: xs` is
  -- `{ tag: 1, _1: x, _2: xs }`
  | .list α => some [[], [α, .list α]]
  | .enum n _ _ => some (List.replicate n [])
  | .record fs => some [fs]
  | .taggedUnion l => some l
  | τ@(.recTaggedUnion l) => instCtors (selfRep τ) l
  | τ@(.recObject fs) => (instList (selfRep τ) fs).map ([·])
  | .mutualRecursiveFamily ms i =>
      match ms[i]? with
      | some (.ctors l) => instCtors (famRep ms) l
      | _ => none
  | _ => none

/-- The type a value of an **alias** really has: a newtype's wrapper is erased, so a
    value of `Ty.recAlias b` — or of an alias member of a mutual family — is a value of
    `b` with the recursive occurrences resolved.  `none` for every other type, which is
    how the translation tells an alias from a type with a layout. -/
def Ty.aliasUnfold? : Ty → Option Ty
  | τ@(.recAlias b) => instRTy (selfRep τ) b
  | .mutualRecursiveFamily ms i =>
      match ms[i]? with
      | some (.alias b) => instRTy (famRep ms) b
      | _ => none
  | _ => none

/-- Is this type an alias — a newtype whose wrapper is erased? -/
def Ty.isAlias (τ : Ty) : Bool := (Ty.aliasUnfold? τ).isSome

/-- Does this type describe an object with constructors? -/
def Ty.isTagged (τ : Ty) : Bool := (Ty.layout? τ).isSome

/-- How many constructors this type has. -/
def Ty.numCtors? (τ : Ty) : Option Nat := (Ty.layout? τ).map (·.length)

/-- **An enum has at least one constructor.**  `Ty.enum` carries a proof that its
    constructor count is positive, so an `Empty`-like type — one with no constructors,
    and hence no values — is not a `Ty` at all, and an enum always has a constructor to
    build. -/
theorem Ty.numCtors?_enum_pos (n : Nat) (h : n > 0) (s : Int) :
    Ty.numCtors? (.enum n h s) = some n ∧ 0 < n := by
  refine ⟨?_, h⟩
  simp [Ty.numCtors?, Ty.layout?]

/-- The fields of constructor number `i` of `τ`, if `τ` has that many constructors. -/
def Ty.ctorFields? (τ : Ty) (i : Nat) : Option FieldLayout :=
  match Ty.layout? τ with
  | none => none
  | some l => l[i]?

/-- The type of field number `j` of constructor number `i` of `τ`. -/
def Ty.fieldTy? (τ : Ty) (i j : Nat) : Option Ty :=
  match Ty.ctorFields? τ i with
  | none => none
  | some fs => fs[j]?

/-- May a case on a value of type `σ` have exactly these branch tags?  It may when `σ`
    is an object type, every tag is one of its constructors, and no tag is repeated.
    Exhaustiveness is not a condition because a case always has a default branch
    (`Alts.deflt`), so there is no way to fall off the end of one. -/
def Ty.caseOk (σ : Ty) (tags : List Nat) : Bool :=
  match Ty.numCtors? σ with
  | none => false
  | some n => tags.all (fun t => t < n) && decide tags.Nodup

/-- A function type has no constructors, so nothing can be built at one. -/
theorem Ty.ctorFields?_fn (params : List Ty) (ret : Ty) (i : Nat) :
    Ty.ctorFields? (Ty.fn params ret) i = none := rfl

/-- A function type has no fields, so nothing can be read out of one. -/
theorem Ty.fieldTy?_fn (params : List Ty) (ret : Ty) (i j : Nat) :
    Ty.fieldTy? (Ty.fn params ret) i j = none := rfl

/-- Nor can a case dispatch on a function. -/
theorem Ty.caseOk_fn (params : List Ty) (ret : Ty) (tags : List Nat) :
    Ty.caseOk (Ty.fn params ret) tags = false := rfl

/-- A scalar is not an object either: `n._1` is not emitted for a `Nat`. -/
theorem Ty.ctorFields?_prim (p : LeanPrimTy) (i : Nat) :
    Ty.ctorFields? (Ty.prim p) i = none := rfl

/-- **A value of a type parameter cannot be taken apart.**  `Ty.typeParam` is the type
    of a value whose Lean type is a type parameter of the enclosing declaration: the
    compiled code may pass it on, but the checked data operations — which are the only
    data operations there are, now that the unchecked ones are gone — are unavailable
    at it, so a compiled module never reads a field of a value it knows nothing
    about. -/
theorem Ty.ctorFields?_typeParam (i : Nat) : Ty.ctorFields? Ty.typeParam i = none := rfl

/-- Nor can a case dispatch on one. -/
theorem Ty.caseOk_typeParam (tags : List Nat) : Ty.caseOk Ty.typeParam tags = false := rfl

/-- An alias has no layout: its wrapper does not exist at run time, so there is no
    constructor to build and no field to read — a value of it *is* a value of the type
    it unfolds to. -/
theorem Ty.ctorFields?_recAlias (b : RTy) (i : Nat) :
    Ty.ctorFields? (Ty.recAlias b) i = none := rfl


end LakeJs.Layout

/-! The layout API, under the namespaces of the types it describes. -/

namespace LakeJs.Ty
export LakeJs.Layout.Ty
  (layout? aliasUnfold? isAlias isTagged numCtors? ctorFields? fieldTy? caseOk
   ctorFields?_fn fieldTy?_fn caseOk_fn ctorFields?_prim ctorFields?_typeParam
   caseOk_typeParam ctorFields?_recAlias numCtors?_enum_pos)
end LakeJs.Ty

namespace LakeJs.Ty.RTy
export LakeJs.Layout.RTy (hasSelf hasSelfShape hasSelfList hasSelfCtors)
end LakeJs.Ty.RTy

/-! ## Worked examples

Each shape of the type language, and the layout it has.  These are `example`s, so they
are checked whenever the module is built. -/

namespace LakeJs.Layout.Examples

open LakeJs
open LakeJs.Ty

/-- `inductive Dir | north | south` — two constructors, neither with a field.  It prints
    as `0 | 1`, since its shift is zero. -/
example : (Ty.enum 2 (shift := 0)).layout? = some [[], []] := rfl

/-- `Ordering` is the same shape with a shift of `-1`, so it has three constructors and
    prints as `-1 | 0 | 1`; the layout does not depend on the shift, which only moves the
    numbers the constructors are printed as. -/
example : (Ty.enum 3 (shift := -1)).layout? = some [[], [], []] := rfl

/-- `structure Point where x y : Nat`. -/
example : (Ty.record [.nat, .nat]).layout? = some [[.nat, .nat]] := rfl

/-- `Option Nat`: constructor `0` carries nothing, constructor `1` carries the value. -/
example : (Ty.option .nat).layout? = some [[], [.nat]] := rfl

/-- The built-in cons list is the recursive sum it is: `[]` is `{ tag: 0 }` and
    `x :: xs` is `{ tag: 1, _1: x, _2: xs }`. -/
example : (Ty.list .nat).layout? = some [[], [.nat, .list .nat]] := rfl

/-- `inductive T | leaf | node : T → T → T`: the recursive occurrences in the layout are
    resolved to the type itself, so reading a field of a `node` gives a `T` again. -/
example :
    (Ty.recTaggedUnion [[], [.self 0, .self 0]]).layout?
      = some [[], [Ty.recTaggedUnion [[], [RTy.self 0, RTy.self 0]],
                   Ty.recTaggedUnion [[], [RTy.self 0, RTy.self 0]]]] := rfl

/-- `structure Tree where n : Nat; kids : Array Tree` — one constructor, two fields, the
    second holding an array of the type itself. -/
example :
    (Ty.recObject [.prim .nat, .array (.self 0)]).layout?
      = some [[.nat, .array (Ty.recObject [.prim .nat, .array (RTy.self 0)])]] := rfl

/-- `structure Rose where kids : Array Rose` is a newtype: it has **no** layout, and a
    value of it is a value of what its single field unfolds to — an array of `Rose`s. -/
example : (Ty.recAlias (.array (.self 0))).layout? = none := rfl

example :
    (Ty.recAlias (.array (.self 0))).aliasUnfold?
      = some (.array (Ty.recAlias (.array (RTy.self 0)))) := rfl

/-- A mutual block `mutual inductive A | mk : B → A; inductive B | mk : A → B end`: two
    members, each pointing at the other, and neither pointing outside the family. -/
example :
    (Ty.mutualRecursiveFamily [.ctors [[.self 1]], .ctors [[.self 0]]] 0).layout?
      = some [[Ty.mutualRecursiveFamily
                 [FamMember.ctors [[RTy.self 1]], FamMember.ctors [[RTy.self 0]]] 1]] :=
  rfl

/-- `.self` is available inside a recursive shape and nowhere else: an `Option Tree`
    *inside* `Tree` still points at `Tree`, because a non-recursive shape does not open
    a scope of its own. -/
example :
    (Ty.recObject [.taggedUnion [[], [.self 0]]]).layout?
      = some [[Ty.option (Ty.recObject [.taggedUnion [[], [RTy.self 0]]])]] := rfl

/-- A value of a type parameter has no layout at all. -/
example : Ty.typeParam.layout? = none := rfl

end LakeJs.Layout.Examples

end
