module

public import LakeJs.SourceToTy
public import LakeJs.TyMetaExamples
public import LakeJs.TyPretty

open NonEmpty.String

@[expose] public section

/-!
# The two translators agree

There are two translations into `Ty` in this library:

* `lean_ty%` (`LakeJs.TyMeta`) reads a schema off a **real** Lean declaration in
  `MetaM`.  It is the one the compiler runs, and nothing about it can be proved,
  because it is a metaprogram over an arbitrary environment.
* `SrcDecl.toTy` (`LakeJs.SourceToTy`) translates the **model** of a declaration.  It
  is an ordinary function, and the theorems `toTy_isOk_iff_supported` and
  `toTy_class` are about it.

The theorems are only interesting if the metaprogram computes the same thing.  This
module is the differential test: for each real declaration below, the schema
`lean_ty%` reads off the environment and the schema `SrcDecl.toTy` produces from the
declaration written out by hand as a `SrcDecl` are compared — by their rendering for
the non-mutual shapes, and by their `FamShape` for the mutual one.  Every check is
closed by `decide`.

This is the thing a random generator would be for.  Generating random *Lean
declarations*, elaborating them and comparing the two translations would extend
exactly these checks to more inputs; it could not replace the theorems, since it can
only sample, but it is the right tool for testing the metaprogram, which the theorems
cannot reach.
-/

namespace LakeJs.SourceAgreement

open LakeJs.Source
open LakeJs.TyMetaExamples

/-- The rendering of a translation result, as in `LakeJs.SourceExamples`. -/
def rendered (r : Except Reject Ty) : Option String := r.toOption.map Ty.pretty

/-! ## A record -/

/-- `structure Point where x : Float; y : Float`, written out as a `SrcDecl`. -/
def pointSrc : SrcDecl :=
  { block := [{ name := nes!"Point"
              , ctors := [{ tag := nes!"Point.mk"
                          , fields := [(nes!"x", .ext .float), (nes!"y", .ext .float)] }] }]
    member := 0 }

example : rendered pointSrc.toTy = some pointTy.pretty := by decide

/-! ## A tagged union -/

/-- `inductive Shape | circle (r : Float) | rect (w h : Float)`. -/
def shapeSrc : SrcDecl :=
  { block := [{ name := nes!"Shape"
              , ctors := [ { tag := nes!"circle", fields := [(nes!"r", .ext .float)] }
                         , { tag := nes!"rect"
                           , fields := [(nes!"w", .ext .float), (nes!"h", .ext .float)] } ] }]
    member := 0 }

example : rendered shapeSrc.toTy = some shapeTy.pretty := by decide

/-! ## A recursive tagged union -/

/-- `inductive MyList | nil | cons (hd : Int) (tl : MyList)`. -/
def myListSrc : SrcDecl :=
  { block := [{ name := nes!"MyList"
              , ctors := [ { tag := nes!"nil", fields := [] }
                         , { tag := nes!"cons"
                           , fields := [(nes!"hd", .ext .int), (nes!"tl", .ref 0)] } ] }]
    member := 0 }

example : rendered myListSrc.toTy = some myListTy.pretty := by decide

/-! ## A recursive record -/

/-- `structure Rose where v : Int; kids : Array Rose` — two fields, so a real object. -/
def roseSrc : SrcDecl :=
  { block := [{ name := nes!"Rose"
              , ctors := [{ tag := nes!"Rose.mk"
                          , fields := [(nes!"v", .ext .int), (nes!"kids", .array (.ref 0))] }] }]
    member := 0 }

example : rendered roseSrc.toTy = some roseTy.pretty := by decide

/-! ## A recursive newtype, and the erasures

The model's `RawDecl` is the declaration *before* erasure, which is what the
elaborator also sees; `RawDecl.toTy` erases and then translates. -/

/-- `structure Rose2 where kids : Array Rose2` — a newtype, so both translators
    produce the fixed point `Rose2 = Array Rose2`, with no object. -/
def rose2Src : SrcDecl :=
  { block := [{ name := nes!"Rose2"
              , ctors := [{ tag := nes!"Rose2.mk"
                          , fields := [(nes!"kids", .array (.ref 0))] }] }]
    member := 0 }

example : rendered rose2Src.toTy = some rose2Ty.pretty := by decide

/-- `structure UnitTree where val : Unit; kids : Array UnitTree` — the `Unit` field is
    erased, which turns the declaration into the newtype above. -/
def unitTreeSrc : RawDecl :=
  { block := [{ name := nes!"UnitTree"
              , ctors := [{ tag := nes!"UnitTree.mk"
                          , fields := [ (nes!"val", .unitLike)
                                      , (nes!"kids", .array (.ref 0)) ] }] }]
    member := 0 }

example : rendered unitTreeSrc.toTy = some (lean_ty% UnitTree).pretty := by decide

/-- `structure Wrapper where x : Nat` — a non-recursive newtype: both translators
    return `Nat` itself. -/
def wrapperSrc : SrcDecl :=
  { block := [{ name := nes!"Wrapper"
              , ctors := [{ tag := nes!"Wrapper.mk", fields := [(nes!"x", .ext .nat)] }] }]
    member := 0 }

example : rendered wrapperSrc.toTy = some (lean_ty% Wrapper).pretty := by decide

/-- `structure Counts where flags : Array Unit; opt : Option Unit; both : Unit × Int;
    empty : Array Empty` — the containers are rewritten and the last field is erased. -/
def countsSrc : RawDecl :=
  { block := [{ name := nes!"Counts"
              , ctors := [{ tag := nes!"Counts.mk"
                          , fields := [ (nes!"flags", .array .unitLike)
                                      , (nes!"opt", .option .unitLike)
                                      , (nes!"both", .prod .unitLike (.ext .int))
                                      , (nes!"empty", .array .voidLike) ] }] }]
    member := 0 }

example : rendered countsSrc.toTy = some (lean_ty% Counts).pretty := by decide

/-- `inductive OnlyGood | bad (x : Empty) (y : Int) | good (v : Int)` — the impossible
    constructor disappears, leaving a newtype, which is erased too. -/
def onlyGoodSrc : RawDecl :=
  { block := [{ name := nes!"OnlyGood"
              , ctors := [ { tag := nes!"bad"
                           , fields := [(nes!"x", .voidLike), (nes!"y", .ext .int)] }
                         , { tag := nes!"good", fields := [(nes!"v", .ext .int)] } ] }]
    member := 0 }

example : rendered onlyGoodSrc.toTy = some (lean_ty% OnlyGood).pretty := by decide

/-! ## A mutual family

`Ty.pretty` prints a family member as `(mutual Name#i)`, so the comparison here is on
the whole block: the `FamShape` the model computes is the `FamShape` the metaprogram
produced, field kinds included. -/

/-- The `Tm`/`Alt` block of `LakeJs.TyMetaExamples`, written out as a `SrcBlock`. -/
def tmSrc : SrcBlock :=
  [ { name := nes!"Tm"
    , ctors := [ { tag := nes!"Tm.var", fields := [(nes!"n", .ext .int)] }
               , { tag := nes!"Tm.branches"
                 , fields := [(nes!"bs", .array (.array (.ref 1)))] }
               , { tag := nes!"Tm.pairs"
                 , fields := [(nes!"ps", .list (.prod (.ext .int) (.ref 1)))] }
               , { tag := nes!"Tm.lazy", fields := [(nes!"f", .fn [.int] (.ref 1))] } ] }
  , { name := nes!"Alt"
    , ctors := [ { tag := nes!"Alt.mk"
                 , fields := [(nes!"guard", .option (.ref 0)), (nes!"body", .ref 0)] } ] } ]

example : blockShape tmSrc = tmFamily.shape := by decide

example : isGenuinelyMutual tmSrc = true := by decide
example : classify { block := tmSrc, member := 0 } = some .mutualFamily := by decide
example : supported { block := tmSrc, member := 1 } = true := by decide

/-! ## The "fake mutual" block

Both translators agree that it is two enums rather than a family. -/

def colorSrc : SrcBlock :=
  [ { name := nes!"Color"
    , ctors := [{ tag := nes!"red", fields := [] }, { tag := nes!"blue", fields := [] }] }
  , { name := nes!"Sha"
    , ctors := [{ tag := nes!"circle", fields := [] }, { tag := nes!"box", fields := [] }] } ]

example : isGenuinelyMutual colorSrc = false := by decide
example : classify { block := colorSrc, member := 0 } = some .enum := by decide

end LakeJs.SourceAgreement

end
