module

public import LakeJs.Ty

@[expose] public section

/-!
# Printing a `Ty`

A one-line rendering, for debugging and error messages, and the `Repr` and `ToString`
instances it backs.  It lives in its own module rather than in `LakeJs.Ty`: the
*definition* of the type language and the *rendering* of it are independent concerns.

Everything here is defined in this module's own namespace, `LakeJs.TyPretty`, and then
`export`ed into the namespaces of the types it prints, so that `τ.pretty` keeps
working.
-/

namespace LakeJs.TyPretty

open LakeJs
open LakeJs.Ty
open NonEmpty.ListCorrectByConstruction (NonEmptyList)

mutual

/-- A one-line rendering of a closed type, for debugging and error messages. -/
def Ty.pretty : Ty → String
  | .prim p         => p.pretty
  | .fn a b         => "(fn " ++ Ty.pretty a ++ " " ++ Ty.pretty b ++ ")"

  | .primCovariant s => Ty.prettyCov s
  | .enum s         =>
      "(enum " ++ toString s.nOfConstructors ++ " " ++ toString s.shift ++ ")"
  | .record fs      => "(record " ++ Ty.prettyA2 fs ++ ")"
  | .taggedUnion l  => "(taggedUnion " ++ Ty.prettyTU l ++ ")"
  | .recTaggedUnion l _ => "(recTaggedUnion " ++ RTy.prettyTU l ++ ")"
  | .recObject fs _ => "(recObject " ++ RTy.prettyA2 fs ++ ")"
  | .recAlias b _   => "(recAlias " ++ RTy.pretty b ++ ")"
  | .mutualRecursiveFamily f _ => FamMember.prettyFamily f

/-- The invariant type formers, over closed types. -/
def Ty.prettyCov : LeanPrimTyCovariant Ty → String
  | .array t        => "(array " ++ Ty.pretty t ++ ")"
  | .list t         => "(list " ++ Ty.pretty t ++ ")"
  | .task t         => "(task " ++ Ty.pretty t ++ ")"
  | .promise t      => "(promise " ++ Ty.pretty t ++ ")"
  | .thunk t        => "(thunk " ++ Ty.pretty t ++ ")"
  | .lazy t         => "(lazy " ++ Ty.pretty t ++ ")"

/-- A list of closed types, separated by spaces. -/
def Ty.prettyList : List Ty → String
  | []      => ""
  | [t]     => Ty.pretty t
  | t :: ts => Ty.pretty t ++ " " ++ Ty.prettyList ts

/-- The constructors of a closed layout, separated by `|`. -/
def Ty.prettyCtors : List (List Ty) → String
  | []      => ""
  | [c]     => "(" ++ Ty.prettyList c ++ ")"
  | c :: cs => "(" ++ Ty.prettyList c ++ ")|" ++ Ty.prettyCtors cs

/-- The fields of a record of closed types. -/
def Ty.prettyA2 : LeanRecordSchema Ty → String
  | ⟨a, b, rest⟩ =>
      Ty.pretty a ++ " " ++ Ty.pretty b
        ++ (if rest.isEmpty then "" else " " ++ Ty.prettyList rest)

/-- The fields of a constructor that has at least one. -/
def Ty.prettyNE : NonEmptyList Ty → String
  | ⟨a, as⟩ => Ty.pretty a ++ (if as.isEmpty then "" else " " ++ Ty.prettyList as)

/-- The constructors of a tagged union of closed types, separated by `|`. -/
def Ty.prettyTU : LeanTaggedUnionSchema Ty → String
  | .payloadFirst f n r =>
      "(" ++ Ty.prettyNE f ++ ")|(" ++ Ty.prettyList n ++ ")"
        ++ (if r.isEmpty then "" else "|" ++ Ty.prettyCtors r)
  | .skip rest => "()|" ++ Ty.prettyCP rest

/-- The constructors that follow a field-less one, separated by `|`. -/
def Ty.prettyCP : CtorsWithPayload Ty → String
  | .here f r =>
      "(" ++ Ty.prettyNE f ++ ")" ++ (if r.isEmpty then "" else "|" ++ Ty.prettyCtors r)
  | .skip rest => "()|" ++ Ty.prettyCP rest

/-- A one-line rendering of a type inside a recursive declaration. -/
def RTy.pretty : RTy → String
  | .self i         => "self#" ++ toString i
  | .prim p         => p.pretty
  | .fn a b         => "(fn " ++ RTy.pretty a ++ " " ++ RTy.pretty b ++ ")"

  | .primCovariant s => RTy.prettyCov s
  | .enum s         =>
      "(enum " ++ toString s.nOfConstructors ++ " " ++ toString s.shift ++ ")"
  | .record fs      => "(record " ++ RTy.prettyA2 fs ++ ")"
  | .taggedUnion l  => "(taggedUnion " ++ RTy.prettyTU l ++ ")"
  | .recTaggedUnion l => "(recTaggedUnion " ++ RTy.prettyTU l ++ ")"
  | .recObject fs => "(recObject " ++ RTy.prettyA2 fs ++ ")"
  | .recAlias b   => "(recAlias " ++ RTy.pretty b ++ ")"
  | .mutualRecursiveFamily f => FamMember.prettyFamily f

/-- The invariant type formers, over types that may mention `.self`. -/
def RTy.prettyCov : LeanPrimTyCovariant RTy → String
  | .array t        => "(array " ++ RTy.pretty t ++ ")"
  | .list t         => "(list " ++ RTy.pretty t ++ ")"
  | .task t         => "(task " ++ RTy.pretty t ++ ")"
  | .promise t      => "(promise " ++ RTy.pretty t ++ ")"
  | .thunk t        => "(thunk " ++ RTy.pretty t ++ ")"
  | .lazy t         => "(lazy " ++ RTy.pretty t ++ ")"

/-- A list of types, separated by spaces. -/
def RTy.prettyList : List RTy → String
  | []      => ""
  | [t]     => RTy.pretty t
  | t :: ts => RTy.pretty t ++ " " ++ RTy.prettyList ts

/-- The constructors of a layout, separated by `|`. -/
def RTy.prettyCtors : List (List RTy) → String
  | []      => ""
  | [c]     => "(" ++ RTy.prettyList c ++ ")"
  | c :: cs => "(" ++ RTy.prettyList c ++ ")|" ++ RTy.prettyCtors cs

/-- The fields of a record. -/
def RTy.prettyA2 : LeanRecordSchema RTy → String
  | ⟨a, b, rest⟩ =>
      RTy.pretty a ++ " " ++ RTy.pretty b
        ++ (if rest.isEmpty then "" else " " ++ RTy.prettyList rest)

/-- The fields of a constructor that has at least one. -/
def RTy.prettyNE : NonEmptyList RTy → String
  | ⟨a, as⟩ => RTy.pretty a ++ (if as.isEmpty then "" else " " ++ RTy.prettyList as)

/-- The constructors of a tagged union, separated by `|`. -/
def RTy.prettyTU : LeanTaggedUnionSchema RTy → String
  | .payloadFirst f n r =>
      "(" ++ RTy.prettyNE f ++ ")|(" ++ RTy.prettyList n ++ ")"
        ++ (if r.isEmpty then "" else "|" ++ RTy.prettyCtors r)
  | .skip rest => "()|" ++ RTy.prettyCP rest

/-- The constructors that follow a field-less one, separated by `|`. -/
def RTy.prettyCP : CtorsWithPayload RTy → String
  | .here f r =>
      "(" ++ RTy.prettyNE f ++ ")" ++ (if r.isEmpty then "" else "|" ++ RTy.prettyCtors r)
  | .skip rest => "()|" ++ RTy.prettyCP rest

/-- One member of a mutual family. -/
def FamMember.pretty : FamMember → String
  | .ctors l => "{" ++ RTy.prettyTU l ++ "}"
  | .record fs => "{" ++ RTy.prettyA2 fs ++ "}"
  | .alias b => "{= " ++ RTy.pretty b ++ "}"

/-- The members of a mutual family, separated by spaces. -/
def FamMember.prettyList : List FamMember → String
  | []      => ""
  | [m]     => FamMember.pretty m
  | m :: ms => FamMember.pretty m ++ " " ++ FamMember.prettyList ms

/-- A mutual family, with the member this type is marked by its number. -/
def FamMember.prettyFamily : LeanMutualRecFamily RTy → String
  | .selectedThenMore before current next after =>
      "(family#" ++ toString before.length ++ " "
        ++ FamMember.prettyList before ++ (if before.isEmpty then "" else " ")
        ++ FamMember.pretty current ++ " " ++ FamMember.pretty next
        ++ (if after.isEmpty then "" else " " ++ FamMember.prettyList after) ++ ")"
  | .selectedLast first before current =>
      "(family#" ++ toString (before.length + 1) ++ " "
        ++ FamMember.pretty first ++ " "
        ++ FamMember.prettyList before ++ (if before.isEmpty then "" else " ")
        ++ FamMember.pretty current ++ ")"

end

instance : ToString Ty where
  toString := Ty.pretty

instance : Repr Ty where
  reprPrec t _ := Ty.pretty t

instance : ToString RTy where
  toString := RTy.pretty

instance : Repr RTy where
  reprPrec t _ := RTy.pretty t

end LakeJs.TyPretty

/-! The renderings, under the namespaces of the types they render. -/

namespace LakeJs.Ty
export LakeJs.TyPretty.Ty (pretty prettyCov prettyList prettyCtors prettyA2 prettyNE prettyTU prettyCP)
end LakeJs.Ty

namespace LakeJs.Ty.RTy
export LakeJs.TyPretty.RTy (pretty prettyCov prettyList prettyCtors prettyA2 prettyNE prettyTU prettyCP)
end LakeJs.Ty.RTy

namespace LakeJs.Ty.FamMember
export LakeJs.TyPretty.FamMember (pretty prettyList prettyFamily)
end LakeJs.Ty.FamMember

end
