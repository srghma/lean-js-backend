module

public import LakeJs.Ty

open NonEmpty.String

@[expose] public section

/-!
# Printing a `Ty`

`Ty` cannot `deriving Repr`: its schemas hold rows, which are inductive families
indexed by their shape, and the derive handlers do not cover those.  So the printer is
written by hand, as an ordinary structural recursion over `Ty` and over every row type
of `LakeJs.Schemas`, and it backs the `Repr` and `ToString` instances.

It lives in its own module rather than in `LakeJs.Ty`: the *definition* of the type
language and the *rendering* of it are independent concerns, and a consumer that only
builds types (`LakeJs.Externs`, say) has no reason to depend on the printer.
-/


mutual

/-- A one-line rendering of a type, for debugging and error messages. -/
def Ty.pretty : Ty → String
  | .prim p         => p.pretty
  | .fn args ret    => "(fn [" ++ Ty.prettyList args ++ "] " ++ Ty.pretty ret ++ ")"
  | .array t        => "(array " ++ Ty.pretty t ++ ")"
  | .list t         => "(list " ++ Ty.pretty t ++ ")"
  | .task t         => "(task " ++ Ty.pretty t ++ ")"
  | .promise t      => "(promise " ++ Ty.pretty t ++ ")"
  | .thunk t        => "(thunk " ++ Ty.pretty t ++ ")"
  | .enum s =>
      "(enum " ++ s.name.toString ++ " "
        ++ String.intercalate "|" (s.tags.map (·.toString)) ++ ")"
  | .record { name := n, fields := fs, .. } =>
      "(record " ++ n.toString ++ " " ++ Ty.prettyFields fs ++ ")"
  | .taggedUnion { name := n, ctors := cs, .. } =>
      "(taggedUnion " ++ n.toString ++ " " ++ Ty.prettyCtors cs ++ ")"
  | .recTaggedUnion { name := n, ctors := cs, .. } =>
      "(recTaggedUnion " ++ n.toString ++ " " ++ Ty.prettyRecCtors cs ++ ")"
  | .recObject { name := n, fields := fs, .. } =>
      "(recObject " ++ n.toString ++ " " ++ Ty.prettySelfFields fs ++ ")"
  | .recAlias { name := n, body := b } =>
      "(recAlias " ++ n.toString ++ " " ++ Ty.prettySelf b ++ ")"
  | .mutualRecursiveFamily fam =>
      "(mutual " ++ fam.name.toString ++ "#" ++ toString fam.member ++ ")"

/-- The parameter types of a function type. -/
def Ty.prettyList : List Ty → String
  | []      => ""
  | [t]     => Ty.pretty t
  | t :: ts => Ty.pretty t ++ " " ++ Ty.prettyList ts

/-- The fields of a record or of one constructor. -/
def Ty.prettyFields {ks : FieldShape} : FieldRow Ty ks → String
  | .nil           => ""
  | .cons k v .nil => k.toString ++ ":" ++ Ty.pretty v
  | .cons k v rest => k.toString ++ ":" ++ Ty.pretty v ++ " " ++ Ty.prettyFields rest

/-- The constructors of a tagged union. -/
def Ty.prettyCtors {cs : TaggedUnionShape} : CtorRow Ty cs → String
  | .nil               => ""
  | .cons t fs .nil    => t.toString ++ "{" ++ Ty.prettyFields fs ++ "}"
  | .cons t fs rest    =>
      t.toString ++ "{" ++ Ty.prettyFields fs ++ "}|" ++ Ty.prettyCtors rest

/-- One field type of a recursive declaration. -/
def Ty.prettySelf {u a : Bool} : SelfTy Ty u a → String
  | .self         => "self"
  | .ty t         => Ty.pretty t
  | .array s      => "(array " ++ Ty.prettySelf s ++ ")"
  | .list s       => "(list " ++ Ty.prettySelf s ++ ")"
  | .option s     => "(option " ++ Ty.prettySelf s ++ ")"
  | .thunk s      => "(thunk " ++ Ty.prettySelf s ++ ")"
  | .task s       => "(task " ++ Ty.prettySelf s ++ ")"
  | .promise s    => "(promise " ++ Ty.prettySelf s ++ ")"
  | .fn ps r      => "(fn [" ++ Ty.prettyList ps ++ "] " ++ Ty.prettySelf r ++ ")"
  | .prod x y     => "(prod " ++ Ty.prettySelf x ++ " " ++ Ty.prettySelf y ++ ")"

/-- The fields of a recursive declaration or of one of its constructors. -/
def Ty.prettySelfFields {fs : SelfFieldShape} : SelfFieldRow Ty fs → String
  | .nil           => ""
  | .cons k v .nil => k.toString ++ ":" ++ Ty.prettySelf v
  | .cons k v rest => k.toString ++ ":" ++ Ty.prettySelf v ++ " " ++ Ty.prettySelfFields rest

/-- The constructors of a recursive tagged union. -/
def Ty.prettyRecCtors {cs : RecTaggedUnionShape} : RecCtorRow Ty cs → String
  | .nil            => ""
  | .cons t fs .nil => t.toString ++ "{" ++ Ty.prettySelfFields fs ++ "}"
  | .cons t fs rest =>
      t.toString ++ "{" ++ Ty.prettySelfFields fs ++ "}|" ++ Ty.prettyRecCtors rest

/-- One field type of a member of a mutual family. -/
def Ty.prettyFamTy {k : FamFieldKind} : FamTy Ty k → String
  | .ty t          => Ty.pretty t
  | .memberRef i   => "#" ++ toString i
  | .array f       => "(array " ++ Ty.prettyFamTy f ++ ")"
  | .list f        => "(list " ++ Ty.prettyFamTy f ++ ")"
  | .option f      => "(option " ++ Ty.prettyFamTy f ++ ")"
  | .thunk f       => "(thunk " ++ Ty.prettyFamTy f ++ ")"
  | .task f        => "(task " ++ Ty.prettyFamTy f ++ ")"
  | .promise f     => "(promise " ++ Ty.prettyFamTy f ++ ")"
  | .fn ps r       => "(fn [" ++ Ty.prettyList ps ++ "] " ++ Ty.prettyFamTy r ++ ")"
  | .prod x y      => "(prod " ++ Ty.prettyFamTy x ++ " " ++ Ty.prettyFamTy y ++ ")"

/-- The fields of one constructor of a family member. -/
def Ty.prettyFamFields {fs : FamFieldShape} : FamFieldRow Ty fs → String
  | .nil => ""
  | .cons k v rest => k.toString ++ ":" ++ Ty.prettyFamTy v ++ " " ++ Ty.prettyFamFields rest

/-- The constructors of one family member. -/
def Ty.prettyFamCtors {cs : List FamCtorShape} : FamCtorRow Ty cs → String
  | .nil => ""
  | .cons t fs rest =>
      t.toString ++ "{" ++ Ty.prettyFamFields fs ++ "}|" ++ Ty.prettyFamCtors rest

/-- The members of a family. -/
def Ty.prettyFamMembers {ms : FamShape} : FamMemberRow Ty ms → String
  | .nil => ""
  | .cons n cs rest =>
      n.toString ++ "(" ++ Ty.prettyFamCtors cs ++ ") " ++ Ty.prettyFamMembers rest

end

/-- The full rendering of a mutual family, members included. -/
def LeanMutualRecFamily.pretty (fam : LeanMutualFamily) : String :=
  "(mutual " ++ fam.name.toString ++ " " ++ Ty.prettyFamMembers fam.members ++ ")"

instance : Repr Ty where
  reprPrec t _ := Std.Format.text t.pretty

instance : ToString Ty where
  toString t := t.pretty

end
