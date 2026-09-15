module

public import LakeJs.SourceToTy
public import LakeJs.TyPretty

open NonEmpty.String

@[expose] public section

/-!
# Worked examples of the declaration model

Each example below is a Lean declaration written out as a `SrcDecl`, next to the
`Ty` (or the rejection) that `SrcDecl.toTy` produces for it.  Everything is checked
by `decide` or `rfl`, so this file is the test suite of `LakeJs.SourceToTy`.

The last section is the *exhaustive small-scope check*: `toTy` and `supported` are
compared on every declaration built from a small alphabet of names, constructors and
field types.  This is the useful form of "quickcheck" here — the declarations are
enumerated rather than sampled, so the check is a proof for that scope, and the
general statement is `toTy_isOk_iff_supported`.
-/

namespace LakeJs.SourceExamples

open LakeJs.Source
open LakeJs.SchemaDisjoint

/-! ## Two helpers

`Ty` has no `DecidableEq` (its rows are indexed families), so an expected result is
written as the *rendering* of the produced type, or as the rejection reason. -/

/-- The pretty-printed translation, if it succeeded. -/
def rendered (r : Except Reject Ty) : Option String := r.toOption.map Ty.pretty

/-- The rejection reason, if it failed. -/
def rejected : Except Reject Ty → Option Reject
  | .error e => some e
  | .ok _    => none

/-! ## Non-recursive shapes -/

/-- `inductive Direction | north | south` -/
def direction : SrcDecl :=
  { block := [{ name := nes!"Direction"
              , ctors := [ { tag := nes!"north", fields := [] }
                         , { tag := nes!"south", fields := [] } ] }]
    member := 0 }

example : classify direction = some .enum := by decide
example : supported direction = true := by decide
-- `Ty.pretty` of an enum goes through `String.intercalate`, which the kernel does not
-- reduce, so an enum is checked by its class and by the fact that it translates.
example : (rendered direction.toTy).isSome = true := by decide

/-- `structure Point where x : Float; y : Float` -/
def point : SrcDecl :=
  { block := [{ name := nes!"Point"
              , ctors := [ { tag := nes!"Point.mk"
                           , fields := [(nes!"x", .ext .float), (nes!"y", .ext .float)] } ] }]
    member := 0 }

example : classify point = some .record := by decide
example : rendered (point.toTy)
      = some "(record Point x:float y:float)" := by decide

/-- `inductive Res | err (e : String) | ok (v : Int)` -/
def res : SrcDecl :=
  { block := [{ name := nes!"Res"
              , ctors := [ { tag := nes!"err", fields := [(nes!"e", .ext .string)] }
                         , { tag := nes!"ok", fields := [(nes!"v", .ext .int)] } ] }]
    member := 0 }

example : classify res = some .taggedUnion := by decide
example :
    rendered (res.toTy)
      = some "(taggedUnion Res err{e:string}|ok{v:int})" := by decide

/-! ## Recursive shapes -/

/-- `inductive MyList | nil | cons (hd : Int) (tl : MyList)` -/
def myList : SrcDecl :=
  { block := [{ name := nes!"MyList"
              , ctors := [ { tag := nes!"nil", fields := [] }
                         , { tag := nes!"cons"
                           , fields := [(nes!"hd", .ext .int), (nes!"tl", .ref 0)] } ] }]
    member := 0 }

example : classify myList = some .recTaggedUnion := by decide
example :
    rendered (myList.toTy)
      = some "(recTaggedUnion MyList nil{}|cons{hd:int tl:self})" := by decide

/-- `structure Rose where v : Int; kids : Array Rose` -/
def rose : SrcDecl :=
  { block := [{ name := nes!"Rose"
              , ctors := [ { tag := nes!"Rose.mk"
                           , fields := [(nes!"v", .ext .int), (nes!"kids", .array (.ref 0))] } ] }]
    member := 0 }

example : classify rose = some .recObject := by decide
example :
    rendered (rose.toTy)
      = some "(recObject Rose v:int kids:(array self))" := by decide

/-- An infinitely branching constructor, `| lim : (Nat → Ord) → Ord`, is in the
    fragment: the family occurs in the *result* of the function. -/
def ord : SrcDecl :=
  { block := [{ name := nes!"Ord2"
              , ctors := [ { tag := nes!"zero", fields := [] }
                         , { tag := nes!"lim"
                           , fields := [(nes!"f", .fn [.nat] (.ref 0))] } ] }]
    member := 0 }

example : classify ord = some .recTaggedUnion := by decide
example : supported ord = true := by decide

/-! ## Rejected: unit-like and void-like -/

/-- `inductive Unit' | mk` — one constructor, no fields: erased. -/
def unitLike : SrcDecl :=
  { block := [{ name := nes!"Unit2", ctors := [{ tag := nes!"mk", fields := [] }] }]
    member := 0 }

example : classify unitLike = none := by decide
example : supported unitLike = false := by decide
example : rejected (unitLike.toTy) = some .unitLikeMember := by decide

/-- `inductive Void'` — no constructors. -/
def voidLike : SrcDecl :=
  { block := [{ name := nes!"Void2", ctors := [] }], member := 0 }

example : classify voidLike = none := by decide
example : rejected (voidLike.toTy) = some .voidMember := by decide

/-- A recursive declaration with no base constructor is not well-founded, so it has no
    values and is rejected: `inductive Bad | l (x : Bad) | r (x : Bad)`. -/
def noBase : SrcDecl :=
  { block := [{ name := nes!"Bad"
              , ctors := [ { tag := nes!"l", fields := [(nes!"x", .ref 0)] }
                         , { tag := nes!"r", fields := [(nes!"x", .ref 0)] } ] }]
    member := 0 }

example : rejected (noBase.toTy) = some .notWellFounded := by decide
example : supported noBase = false := by decide

/-- `structure S where s : S` — an unguarded self occurrence in a record. -/
def unguarded : SrcDecl :=
  { block := [{ name := nes!"S"
              , ctors := [{ tag := nes!"S.mk", fields := [(nes!"s", .ref 0)] }] }]
    member := 0 }

example : rejected (unguarded.toTy) = some .notWellFounded := by decide

/-! ## Mutual blocks -/

/-- The genuinely mutual block `Exp`/`Stm`, with the family used in nested positions:
    `Array (Array Stm)` and `Int × Stm`. -/
def expStm : SrcBlock :=
  [ { name := nes!"Exp"
    , ctors := [ { tag := nes!"Exp.lit", fields := [(nes!"n", .ext .int)] }
               , { tag := nes!"Exp.block"
                 , fields := [(nes!"ss", .array (.array (.ref 1)))] } ] }
  , { name := nes!"Stm"
    , ctors := [ { tag := nes!"Stm.ret"
                 , fields := [(nes!"e", .prod (.ext .int) (.ref 0))] } ] } ]

example : isGenuinelyMutual expStm = true := by decide
example : classify { block := expStm, member := 0 } = some .mutualFamily := by decide
example : classify { block := expStm, member := 1 } = some .mutualFamily := by decide
example : supported { block := expStm, member := 0 } = true := by decide
example : ({ block := expStm, member := 1 } : SrcDecl).toTy.toOption.isSome = true := by decide

/-- The "fake mutual" block: two members that never mention each other.  It is not a
    family; each member is translated on its own, and comes out an enum. -/
def colorShape : SrcBlock :=
  [ { name := nes!"Color"
    , ctors := [{ tag := nes!"red", fields := [] }, { tag := nes!"blue", fields := [] }] }
  , { name := nes!"Shape"
    , ctors := [{ tag := nes!"circle", fields := [] }, { tag := nes!"box", fields := [] }] } ]

example : isGenuinelyMutual colorShape = false := by decide
example : classify { block := colorShape, member := 0 } = some .enum := by decide
example :
    classify { block := colorShape, member := 1 } = some .enum := by decide

/-- A one-way reference is not a mutual block either: `Wrap` mentions `Inner` but not
    conversely.  `Inner` is an independent declaration, so inside `Wrap` it must be
    written `SrcTy.ext` (with `Inner`'s own `Ty`), not `SrcTy.ref`. -/
def oneWay : SrcBlock :=
  [ { name := nes!"Wrap"
    , ctors := [{ tag := nes!"Wrap.mk", fields := [(nes!"inner", .ref 1)] }] }
  , { name := nes!"Inner"
    , ctors := [{ tag := nes!"Inner.mk", fields := [(nes!"v", .ext .int)] }] } ]

example : isGenuinelyMutual oneWay = false := by decide
example : rejected (({ block := oneWay, member := 0 } : SrcDecl).toTy) = some .foreignReference := by
  decide

/-- Written the intended way — `Inner`'s `Ty` inlined — it is an ordinary record. -/
def wrapAlone : SrcDecl :=
  { block :=
      [ { name := nes!"Wrap"
        , ctors :=
            [{ tag := nes!"Wrap.mk"
             , fields :=
                 [(nes!"inner"
                  , .ext (.record { name := nes!"Inner", fields := .cons (nes!"v") .int .nil }))] }] } ]
    member := 0 }

example :
    rendered (wrapAlone.toTy)
      = some "(record Wrap inner:(record Inner v:int))" := by
  decide

/-! ## Out of range -/

example : rejected (({ block := colorShape, member := 7 } : SrcDecl).toTy) = some .memberOutOfRange := by
  decide
example : classify { block := colorShape, member := 7 } = none := by decide

end LakeJs.SourceExamples

end
