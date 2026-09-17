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

mutual

/-- A one-line rendering of a closed type, for debugging and error messages. -/
def Ty.pretty : Ty → String
  | .prim p         => p.pretty
  | .typeParam      => "typeParam"
  | .shape s        => Ty.prettyShape s
  | .enum n _ sh    => "(enum " ++ toString n ++ " " ++ toString sh ++ ")"
  | .record fs      => "(record " ++ Ty.prettyList fs ++ ")"
  | .taggedUnion l  => "(taggedUnion " ++ Ty.prettyCtors l ++ ")"
  | .recTaggedUnion l => "(recTaggedUnion " ++ RTy.prettyCtors l ++ ")"
  | .recObject fs   => "(recObject " ++ RTy.prettyList fs ++ ")"
  | .recAlias b     => "(recAlias " ++ RTy.pretty b ++ ")"
  | .mutualRecursiveFamily ms i =>
      "(family#" ++ toString i ++ " " ++ FamMember.prettyList ms ++ ")"

/-- The shared type formers, over closed types. -/
def Ty.prettyShape : Shape Ty → String
  | .fn args ret    => "(fn [" ++ Ty.prettyList args ++ "] " ++ Ty.pretty ret ++ ")"
  | .fn_returnsProd args r1 rs =>
      "(fn [" ++ Ty.prettyList args ++ "] ["
        ++ Ty.pretty r1 ++ (if rs.isEmpty then "" else "," ++ Ty.prettyList rs) ++ "])"
  | .array t        => "(array " ++ Ty.pretty t ++ ")"
  | .list t         => "(list " ++ Ty.pretty t ++ ")"
  | .task t         => "(task " ++ Ty.pretty t ++ ")"
  | .promise t      => "(promise " ++ Ty.pretty t ++ ")"
  | .thunk t        => "(thunk " ++ Ty.pretty t ++ ")"

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

/-- A one-line rendering of a type inside a recursive declaration. -/
def RTy.pretty : RTy → String
  | .self i         => "self#" ++ toString i
  | .prim p         => p.pretty
  | .typeParam      => "typeParam"
  | .shape s        => RTy.prettyShape s
  | .enum n _ sh    => "(enum " ++ toString n ++ " " ++ toString sh ++ ")"
  | .record fs      => "(record " ++ RTy.prettyList fs ++ ")"
  | .taggedUnion l  => "(taggedUnion " ++ RTy.prettyCtors l ++ ")"
  | .recTaggedUnion l => "(recTaggedUnion " ++ RTy.prettyCtors l ++ ")"
  | .recObject fs   => "(recObject " ++ RTy.prettyList fs ++ ")"
  | .recAlias b     => "(recAlias " ++ RTy.pretty b ++ ")"
  | .mutualRecursiveFamily ms i =>
      "(family#" ++ toString i ++ " " ++ FamMember.prettyList ms ++ ")"

/-- The shared type formers, over types that may mention `.self`. -/
def RTy.prettyShape : Shape RTy → String
  | .fn args ret    => "(fn [" ++ RTy.prettyList args ++ "] " ++ RTy.pretty ret ++ ")"
  | .fn_returnsProd args r1 rs =>
      "(fn [" ++ RTy.prettyList args ++ "] ["
        ++ RTy.pretty r1 ++ (if rs.isEmpty then "" else "," ++ RTy.prettyList rs) ++ "])"
  | .array t        => "(array " ++ RTy.pretty t ++ ")"
  | .list t         => "(list " ++ RTy.pretty t ++ ")"
  | .task t         => "(task " ++ RTy.pretty t ++ ")"
  | .promise t      => "(promise " ++ RTy.pretty t ++ ")"
  | .thunk t        => "(thunk " ++ RTy.pretty t ++ ")"

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

/-- One member of a mutual family. -/
def FamMember.pretty : FamMember → String
  | .ctors l => "{" ++ RTy.prettyCtors l ++ "}"
  | .alias b => "{= " ++ RTy.pretty b ++ "}"

/-- The members of a mutual family, separated by spaces. -/
def FamMember.prettyList : List FamMember → String
  | []      => ""
  | [m]     => FamMember.pretty m
  | m :: ms => FamMember.pretty m ++ " " ++ FamMember.prettyList ms

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
export LakeJs.TyPretty.Ty (pretty prettyShape prettyList prettyCtors)
end LakeJs.Ty

namespace LakeJs.Ty.RTy
export LakeJs.TyPretty.RTy (pretty prettyShape prettyList prettyCtors)
end LakeJs.Ty.RTy

namespace LakeJs.Ty.FamMember
export LakeJs.TyPretty.FamMember (pretty prettyList)
end LakeJs.Ty.FamMember

end
