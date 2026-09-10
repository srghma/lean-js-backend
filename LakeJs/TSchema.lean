module

public import Std.Data.HashSet

public import Lean.Elab.Term
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Meta.Basic
public meta import Lean.Meta.Eval
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name

@[expose] public section

/-!
# Recursion-aware ("strict") schemas for compiled Lean inductive types
-/

inductive LeanFieldKind where
  | nonRec
  | recAt (member : Nat)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

def LeanFieldKind.WF (numMembers : Nat) : LeanFieldKind → Prop
  | .nonRec   => True
  | .recAt i  => i < numMembers

instance (numMembers : Nat) (k : LeanFieldKind) : Decidable (k.WF numMembers) := by
  cases k with
  | nonRec  => exact .isTrue trivial
  | recAt i => exact inferInstanceAs (Decidable (i < numMembers))

def LeanFieldKind.isRec : LeanFieldKind → Bool
  | .nonRec  => false
  | .recAt _ => true

structure LeanRecCtorSchema where
  name       : String
  h_name_ne  : name != "" := by decide
  fieldKinds : List LeanFieldKind
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace LeanRecCtorSchema

def numFields (c : LeanRecCtorSchema) : Nat := c.fieldKinds.length

def kind (c : LeanRecCtorSchema) (i : Nat) : LeanFieldKind :=
  c.fieldKinds.getD i .nonRec

def isRecField (c : LeanRecCtorSchema) (i : Nat) : Bool := (c.kind i).isRec

def numRecFields (c : LeanRecCtorSchema) : Nat :=
  (c.fieldKinds.filter (·.isRec)).length

def recFieldIdxs (c : LeanRecCtorSchema) : List Nat :=
  (List.range c.numFields).filter (c.isRecField ·)

@[simp] theorem numFields_eq (c : LeanRecCtorSchema) : c.numFields = c.fieldKinds.length := rfl

instance : Inhabited LeanRecCtorSchema := ⟨{ name := "?", fieldKinds := [] }⟩

end LeanRecCtorSchema

structure LeanRecTypeSchema where
  typeName      : String
  h_typeName_ne : typeName != "" := by decide
  ctors         : List LeanRecCtorSchema
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

instance : Inhabited LeanRecTypeSchema := ⟨{ typeName := "?", ctors := [] }⟩

def leanRecAllCtors (members : List LeanRecTypeSchema) : List LeanRecCtorSchema :=
  members.flatMap (·.ctors)

def LeanRecTagsNodup (members : List LeanRecTypeSchema) : Prop :=
  ((leanRecAllCtors members).map (·.name)).Nodup

instance (members : List LeanRecTypeSchema) : Decidable (LeanRecTagsNodup members) :=
  inferInstanceAs (Decidable (List.Nodup _))

def LeanRecKindsWF.check (members : List LeanRecTypeSchema) : Bool :=
  (leanRecAllCtors members).all fun c =>
    c.fieldKinds.all fun k =>
      match k with
      | .nonRec  => true
      | .recAt i => if i < members.length then true else false

def LeanRecKindsWF (members : List LeanRecTypeSchema) : Prop :=
  LeanRecKindsWF.check members = true

instance (members : List LeanRecTypeSchema) : Decidable (LeanRecKindsWF members) :=
  instDecidableEqBool (LeanRecKindsWF.check members) true

structure LeanRecFamily where
  members       : List LeanRecTypeSchema
  h_nonempty    : members ≠ [] := by decide
  h_tags_nodup  : LeanRecTagsNodup members := by decide
  h_kinds_wf    : LeanRecKindsWF members := by decide
  deriving Repr, DecidableEq

instance : BEq LeanRecFamily where
  beq a b := a.members == b.members

instance : LawfulBEq LeanRecFamily where
  eq_of_beq {a b} h := by
    have hb : (a.members == b.members) = true := h
    have hm : a.members = b.members := eq_of_beq hb
    cases a; cases b; simp_all
  rfl {a} := by
    show (a.members == a.members) = true
    simp

namespace LeanRecFamily

def allCtors (fam : LeanRecFamily) : List LeanRecCtorSchema := leanRecAllCtors fam.members

def name (fam : LeanRecFamily) : String :=
  (fam.members.head?).elim "?" (·.typeName)

def findCtor? (fam : LeanRecFamily) (tag : String) : Option LeanRecCtorSchema :=
  fam.allCtors.find? (·.name == tag)

def hasCtor (fam : LeanRecFamily) (tag : String) : Bool := (fam.findCtor? tag).isSome

def getCtor (fam : LeanRecFamily) (tag : String) (h : fam.hasCtor tag := by decide) :
    LeanRecCtorSchema :=
  (fam.findCtor? tag).get h

def ctorNumFields (fam : LeanRecFamily) (tag : String) : Nat :=
  (fam.findCtor? tag).elim 0 (·.numFields)

def isLinear (fam : LeanRecFamily) : Bool :=
  fam.allCtors.all (fun c => c.numRecFields ≤ 1)

end LeanRecFamily

theorem leanRec_find?_name_eq_self {ctors : List LeanRecCtorSchema}
    (h_nodup : (ctors.map (·.name)).Nodup)
    {c : LeanRecCtorSchema} (h_mem : c ∈ ctors) :
    ctors.find? (·.name == c.name) = some c := by
  induction ctors with
  | nil => cases h_mem
  | cons d ds ih =>
    rw [List.map_cons, List.nodup_cons] at h_nodup
    obtain ⟨h_head, h_tail⟩ := h_nodup
    rcases List.mem_cons.mp h_mem with rfl | h_mem'
    · simp
    · have h_ne : (d.name == c.name) = false := by
        refine beq_eq_false_iff_ne.mpr ?_
        intro hde
        exact h_head (List.mem_map.mpr ⟨c, h_mem', hde.symm⟩)
      simp [h_ne, ih h_tail h_mem']

theorem LeanRecFamily.findCtor?_of_mem {fam : LeanRecFamily} {c : LeanRecCtorSchema}
    (h : c ∈ fam.allCtors) : fam.findCtor? c.name = some c :=
  leanRec_find?_name_eq_self fam.h_tags_nodup h

theorem LeanRecFamily.ctorNumFields_of_mem {fam : LeanRecFamily} {c : LeanRecCtorSchema}
    (h : c ∈ fam.allCtors) : fam.ctorNumFields c.name = c.numFields := by
  simp [LeanRecFamily.ctorNumFields, LeanRecFamily.findCtor?_of_mem h]

theorem LeanRecFamily.mem_of_contains {fam : LeanRecFamily} {c : LeanRecCtorSchema}
    (h : fam.allCtors.contains c = true) : c ∈ fam.allCtors :=
  List.contains_iff_mem.mp h

open Lean Meta in
/-- Read raw member schemas off the environment at compile time. -/
public meta def extractRecMembers (typeName : Name) : MetaM (List LeanRecTypeSchema) := do
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? typeName
    | throwError "'{typeName}' is not an inductive type"
  let allNames := indVal.all
  let multi := allNames.length > 1
  let mut members : List LeanRecTypeSchema := []
  for tn in allNames do
    let some (.inductInfo iv) := env.find? tn
      | throwError "'{tn}' is not an inductive type"
    let tnStr := tn.toString
    let tnShort := match tn with
      | .str _ s => s
      | _        => tnStr
    let mut ctors : List LeanRecCtorSchema := []
    for cn in iv.ctors do
      let some (.ctorInfo cv) := env.find? cn
        | throwError "constructor '{cn}' not found"
      let short := match cn with
        | .str _ s => s
        | _        => cn.toString
      let tag := if multi then tnShort ++ "." ++ short else short
      let kinds ← forallTelescopeReducing cv.type fun args _ => do
        let fields := args.toList.drop cv.numParams
        fields.mapM fun fv => do
          let ft ← whnf (← inferType fv)
          match ft.getAppFn with
          | .const c _ =>
              match allNames.findIdx? (· == c) with
              | some i => pure (LeanFieldKind.recAt i)
              | none   => pure LeanFieldKind.nonRec
          | _ => pure LeanFieldKind.nonRec
      if h : tag != "" then
        ctors := ctors ++ [{ name := tag, h_name_ne := h, fieldKinds := kinds }]
      else
        throwError "constructor '{cn}' has an empty name"
    if h : tnStr != "" then
      members := members ++ [{ typeName := tnStr, h_typeName_ne := h, ctors := ctors }]
    else
      throwError "type name of '{tn}' is empty"
  if members.isEmpty then
    throwError "the family of '{typeName}' is empty"
  return members

open Lean Elab Term in
/--
`lean_rec_family% <type>` expands into a literal `LeanRecFamily` describing the whole
mutual block of `<type>`, including which constructor fields are recursive.
-/
elab "lean_rec_family% " id:ident : term => do
  let typeName ← resolveGlobalConstNoOverload id
  let members ← extractRecMembers typeName
  let memberSyn ← members.toArray.mapM fun (m : LeanRecTypeSchema) => do
    let ctorSyn ← m.ctors.toArray.mapM fun (c : LeanRecCtorSchema) => do
      let kindSyn ← c.fieldKinds.toArray.mapM fun k =>
        match k with
        | .nonRec  => `(LeanFieldKind.nonRec)
        | .recAt i => `(LeanFieldKind.recAt $(quote i))
      `(LeanRecCtorSchema.mk $(quote c.name) (by decide) [ $[$kindSyn],* ])
    `(LeanRecTypeSchema.mk $(quote m.typeName) (by decide) [ $[$ctorSyn],* ])
  let term ← `(LeanRecFamily.mk [ $[$memberSyn],* ] (by decide) (by decide) (by decide))
  elabTerm term none

/-- The recursion-aware family of Lean's `List`: `nil` (no fields) and
    `cons` (one ordinary field and one recursive field). -/
def listFamily : LeanRecFamily := lean_rec_family% List

#print listFamily

end
