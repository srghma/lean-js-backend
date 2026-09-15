module

public import LakeJs.TyMeta
public meta import LakeJs.TyMeta
public import LakeJs.TyDerived
public meta import LakeJs.TyDerived
public import LakeJs.TyPretty

@[expose] public section

/-!
# Worked examples for `lean_…_schema%`

Each declaration below is a real Lean type; the schema next to it is read off the
environment at elaboration time, so this file is also the test suite of
`LakeJs.TyMeta`.  Every `example` is closed by `decide` or `rfl`, i.e. the generated
schema is compared against the one written by hand in `LakeJs.TyExamples`.
-/

open NonEmpty.String

namespace LakeJs.TyMetaExamples

/-! ## Enum -/

inductive Direction where
  | north | south | east | west
  deriving Repr

def directionSchema : LeanEnumSchema := lean_enum_schema% Direction
def directionTy : Ty := lean_ty% Direction

example : directionSchema.tags.map (·.toString) = ["north", "south", "east", "west"] := by
  decide

example : directionTy = .enum directionSchema := rfl

/-! ## Record -/

structure Point where
  x : Float
  y : Float

def pointSchema : LeanRecordSchema Ty := lean_record_schema% Point
def pointTy : Ty := lean_ty% Point

example : pointTy.pretty = "(record Point x:float y:float)" := by decide

/-- A record whose field is another user-defined type: the field's schema is expanded
    in place. -/
structure Segment where
  from_ : Point
  to_ : Point
  label : String

def segmentTy : Ty := lean_ty% Segment

example :
    segmentTy.pretty
      = "(record Segment from_:(record Point x:float y:float) "
        ++ "to_:(record Point x:float y:float) label:string)" := by decide

/-! ## Tagged union -/

inductive Shape where
  | circle (r : Float)
  | rect (w : Float) (h : Float)

def shapeSchema : LeanTaggedUnionSchema Ty := lean_tagged_union_schema% Shape
def shapeTy : Ty := lean_ty% Shape

example : shapeTy.pretty = "(taggedUnion Shape circle{r:float}|rect{w:float h:float})" := by
  decide

/-! ## Recursive tagged union -/

inductive MyList where
  | nil
  | cons (hd : Int) (tl : MyList)

def myListSchema : LeanRecTaggedUnionSchema Ty := lean_rec_tagged_union_schema% MyList
def myListTy : Ty := lean_ty% MyList

example : myListTy.pretty = "(recTaggedUnion MyList nil{}|cons{hd:int tl:self})" := by decide

/-- An `Option` guards a self occurrence, so `link` is a base constructor. -/
inductive Chain where
  | stop
  | link (next : Option Chain)

def chainTy : Ty := lean_ty% Chain

example : chainTy.pretty = "(recTaggedUnion Chain stop{}|link{next:(option self)})" := by
  decide

/-! ## Recursive record -/

structure Rose where
  v : Int
  kids : Array Rose

def roseSchema : LeanRecObjectSchema Ty := lean_rec_object_schema% Rose
def roseTy : Ty := lean_ty% Rose

example : roseTy.pretty = "(recObject Rose v:int kids:(array self))" := by decide

/-- A self occurrence may also sit inside a pair, as long as the pair is guarded: an
    `Array (Int × Forest)` may be empty, so `Forest` is still buildable. -/
structure Forest where
  label : String
  kids : Array (Int × Forest)

def forestTy : Ty := lean_ty% Forest

example :
    forestTy.pretty = "(recObject Forest label:string kids:(array (prod int self)))" := by
  decide

/-! ## Genuinely mutual family -/

mutual
  inductive Exp where
    | lit (n : Int)
    | block (s : Stm)
  inductive Stm where
    | ret (e : Exp)
    | seq (ss : List Stm) (tail : Exp)
end

def expFamily : LeanMutualRecFamily Ty := lean_mutual_rec_family% Exp
def stmFamily : LeanMutualRecFamily Ty := lean_mutual_rec_family% Stm

def expTy : Ty := lean_ty% Exp
def stmTy : Ty := lean_ty% Stm

example : expFamily.member = 0 := by decide
example : stmFamily.member = 1 := by decide
example : expFamily.tags.map (·.toString) = ["Exp.lit", "Exp.block", "Stm.ret", "Stm.seq"] := by
  decide
example : expFamily.numMembers = 2 := by decide
example : famShapeOk expFamily.shape = true := by decide

/-! ## A mutual family using the family in nested positions

A field of a family member may use the family wherever a field of a non-mutual
recursive declaration may use *itself*: under several containers, inside a pair, and
in the result of a function.  (Before `FamFieldKind` became a grammar, only a direct
occurrence and an occurrence under a single `Array`/`List`/`Option` could be
expressed.) -/

mutual
  inductive Tm where
    | var (n : Int)
    | branches (bs : Array (Array Alt))
    | pairs (ps : List (Int × Alt))
    | lazy (f : Int → Alt)
  inductive Alt where
    | mk (guard : Option Tm) (body : Tm)
end

def tmFamily : LeanMutualRecFamily Ty := lean_mutual_rec_family% Tm
def tmTy : Ty := lean_ty% Tm
def altTy : Ty := lean_ty% Alt

example : famShapeOk tmFamily.shape = true := by decide

/-- The field kinds recorded for the block are the nested ones. -/
example :
    tmFamily.shape.map (fun m => m.2.map (fun c => c.2.map (·.2)))
      = [ [ [.nonRec]
          , [.array (.array (.recAt 1))]
          , [.list (.prod .nonRec (.recAt 1))]
          , [.fn (.recAt 1)] ]
        , [ [.option (.recAt 0), .recAt 0] ] ] := by
  decide

/-- None of these kinds is expressible as "a member under a single guard", which is
    all the earlier three-case `FamFieldKind` could say. -/
example : ∀ (g : FamGuard) (i : Nat),
    FamFieldKind.recUnder g i ≠ .array (.array (.recAt 1))
      ∧ FamFieldKind.recUnder g i ≠ .list (.prod .nonRec (.recAt 1))
      ∧ FamFieldKind.recUnder g i ≠ .fn (.recAt 1) := by
  intro g i
  cases g <;> simp [FamFieldKind.recUnder]

/-- Both members are `Ty`s of the *same* block, differing only in `member`. -/
example : (lean_mutual_rec_family% Alt).member = 1 := by decide
example : (lean_mutual_rec_family% Alt).shape = tmFamily.shape := by decide

/-! ## The "fake mutual" block of `Types.md` is two enums, not a family -/

mutual
  inductive Color where | red | blue
  inductive Sha where | circle | box
end

def colorSchema : LeanEnumSchema := lean_enum_schema% Color
def colorTy : Ty := lean_ty% Color

example : colorTy = .enum colorSchema := rfl

/-! ## `derive_ty`: parameterised declarations

`lean_ty%` needs a *type*; a declaration with type parameters is a family of types, so
it becomes a function from `Ty` to `Ty` — one argument per type parameter — generated
by `derive_ty` (`LakeJs.TyDerive`).  This is how `Ty.option` and `Ty.prod` are defined
in `LakeJs.TyDerived`. -/

example : (Ty.option .char).pretty = "(taggedUnion Option none{}|some{val:char})" := by
  decide

example : (Ty.prod .float .int64).pretty = "(record Prod fst:float snd:int64)" := by
  decide

/-- A parameterised record. -/
structure Boxed (α : Type) where
  value : α
  label : String

derive_ty Boxed as Ty.boxed

example : (Ty.boxed .int).pretty = "(record Boxed value:int label:string)" := by decide

/-- A parameterised *recursive* declaration: the self occurrence is at the
    declaration's own parameter, which `derive_ty` recognises as `SelfTy.self`. -/
inductive MyListG (α : Type) where
  | nil
  | cons (hd : α) (tl : MyListG α)

derive_ty MyListG as Ty.myListG

example :
    (Ty.myListG .string).pretty = "(recTaggedUnion MyListG nil{}|cons{hd:string tl:self})" := by
  decide

/-- A parameterised sum type whose payload mentions the parameter twice. -/
inductive Choice (α β : Type) where
  | left (l : α)
  | right (r : β)
  | both (l : α) (r : β)

derive_ty Choice as Ty.choice

example :
    (Ty.choice .int .bool).pretty
      = "(taggedUnion Choice left{l:int}|right{r:bool}|both{l:int r:bool})" := by
  decide

/-! ## What `derive_ty` rejects

```lean
derive_ty Exp as Ty.exp        -- member of a mutual block
derive_ty Vector as Ty.vector  -- `n : Nat` is a value parameter, i.e. an index
derive_ty PUnit as Ty.punit    -- unit type: erased
```
-/

/-! ## What the elaborators reject

Each of these is an elaboration error, so it is shown commented out:

```lean
def bad1 : LeanEnumSchema := lean_enum_schema% Point        -- `Point` is a record
def bad2 : LeanRecordSchema Ty := lean_record_schema% Rose  -- `Rose` is recursive
def bad3 : Ty := lean_ty% PUnit                             -- unit type: erased
def bad4 : Ty := lean_ty% Empty                             -- void type
def bad5 : Ty := lean_ty% List                              -- takes a parameter
def bad6 : LeanMutualRecFamily Ty := lean_mutual_rec_family% Color  -- not mutual
```
-/

end LakeJs.TyMetaExamples

end
