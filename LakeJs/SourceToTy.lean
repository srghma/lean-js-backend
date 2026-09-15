module

public import LakeJs.Source

open NonEmpty.String
open LakeJs.SchemaDisjoint

@[expose] public section

/-!
# The translation `SrcDecl → Ty`, and what it covers

This module contains **one** function, `SrcDecl.toTy`, from the declaration model of
`LakeJs.Source` into `Ty`, together with the two theorems that answer the questions
the model was built for:

* `toTy_isOk_iff_supported` — a declaration is representable **exactly** when it is
  `supported`, a decidable source-level predicate whose only non-structural exclusions
  are "void member" (no constructors) and "unit-like member" (one constructor, no
  fields).  So there is no need for a random generator to hunt for gaps: the gaps are
  named, and there are no others.  (A generator is still useful for a different
  purpose — see `LakeJs.SourceExamples`.)
* `toTy_class` — whenever the translation succeeds, the `Ty` constructor it produces
  is the one `classify` predicts, and `classify` is a function of the five
  observables of `ShapeDescriptor` alone.  Since `toTy` is a function, a declaration
  has exactly one translation; and since the shapes are pairwise distinguished by
  those observables (`LakeJs.SchemaDisjoint`), no other correct translation could
  choose a different shape.

## Two erasures happen first

`SrcDecl.toTy` erases the declaration (`SrcDecl.erase`) before doing anything else:
unit-like fields disappear, constructors with a void-like field disappear, and
containers of erased types are rewritten (`Array Unit` becomes `Nat`).  Everything
below therefore reads an *erased* declaration, which is also why the wrapper check is
meaningful: `structure UnitTree where val : Unit; kids : Array UnitTree` erases to
`structure Rose where kids : Array Rose`.

The second erasure is the **newtype** one, and it is part of the translation: a member
left with one constructor carrying one field has no object of its own
(`toWrapperTy`).  If that field does not mention the member, the member *is* the
field, and the translation returns the field's own `Ty` — no schema is built.  If it
does mention the member, the result is the fixed point `Ty.recAlias`.
-/

namespace LakeJs.Source

/-! ## Why a declaration can fail to be representable -/

/-- The reasons `toTy` rejects a declaration. -/
inductive Reject where
  /-- The member index is not a member of the block. -/
  | memberOutOfRange
  /-- A member with no constructors: a void type, which has no runtime value. -/
  | voidMember
  /-- A member with one field-less constructor: a unit type, which is erased. -/
  | unitLikeMember
  /-- A declaration that is not part of a genuine mutual block refers to another
      member of its block.  Such a sibling is an independent declaration: it has its
      own `Ty`, and must be referred to with `SrcTy.ext`. -/
  | foreignReference
  /-- Duplicate constructor tags or duplicate field names. -/
  | duplicateNames
  /-- A recursive declaration with no way to build a value: no base constructor, an
      unguarded self occurrence in a record, or a recursive newtype whose single field
      is an unguarded occurrence of the type itself (`structure S where s : S`). -/
  | notWellFounded
  /-- A mutual block failing one of the family invariants. -/
  | familyIllFormed
  deriving Repr, DecidableEq

/-! ## Shapes computed from the source -/

/-- The fields of a constructor of a *non-recursive* declaration: just the names. -/
def plainFieldShape (fs : List (NonEmptyString × SrcTy)) : FieldShape := fs.map (·.1)

/-- One constructor of a non-recursive tagged union. -/
def plainCtorShape (c : SrcCtor) : CtorShape := (c.tag, plainFieldShape c.fields)

/-- The fields of a constructor of a *recursive* declaration: name plus the two bits
    `SelfTy` is indexed by. -/
def selfFieldShape (fs : List (NonEmptyString × SrcTy)) : SelfFieldShape :=
  fs.map (fun f => (f.1, kindUses f.2.kind, kindAvoids f.2.kind))

/-- One constructor of a recursive tagged union. -/
def selfCtorShape (c : SrcCtor) : RecCtorShape := (c.tag, selfFieldShape c.fields)

/-! ## Building the field types -/

/-- A source type that does not mention the block *is* an ordinary `Ty`. -/
def SrcTy.toTy? : SrcTy → Option Ty
  | .ext t     => some t
  | .ref _     => none
  | .array t   => Ty.array <$> t.toTy?
  | .list t    => Ty.list <$> t.toTy?
  | .option t  => Ty.option <$> t.toTy?
  | .thunk t   => Ty.thunk <$> t.toTy?
  | .task t    => Ty.task <$> t.toTy?
  | .promise t => Ty.promise <$> t.toTy?
  | .fn ps r   => Ty.fn ps <$> r.toTy?
  | .prod a b  =>
      match a.toTy?, b.toTy? with
      | some x, some y => some (Ty.prod x y)
      | _, _ => none

/-- A source type, as the field type of a member of a mutual family.  Total: every
    source type has a `FamTy`, which is the sense in which the family grammar is no
    longer a restriction. -/
def SrcTy.toFamTy : (s : SrcTy) → FamTy Ty s.kind
  | .ext t     => .ty t
  | .ref i     => .memberRef i
  | .array t   => .array t.toFamTy
  | .list t    => .list t.toFamTy
  | .option t  => .option t.toFamTy
  | .thunk t   => .thunk t.toFamTy
  | .task t    => .task t.toFamTy
  | .promise t => .promise t.toFamTy
  | .fn ps r   => .fn ps r.toFamTy
  | .prod a b  => .prod a.toFamTy b.toFamTy

/-- `SelfTy.prod`, re-indexed: the indices it produces are *equal* to the ones the
    kind computes, but not definitionally so (`(xs ++ ys).isEmpty` does not reduce for
    variable `xs`). -/
def selfProd {u₁ a₁ u₂ a₂ u a : Bool} (x : SelfTy Ty u₁ a₁) (y : SelfTy Ty u₂ a₂)
    (hu : u = (u₁ || u₂)) (ha : a = (a₁ && a₂)) : SelfTy Ty u a :=
  cast (by rw [hu, ha]) (SelfTy.prod x y)

/-- A source type, as the field type of a **non-mutual** recursive declaration whose
    own member index is `self`.  Fails exactly when the type mentions another member
    of the block, which for a non-mutual declaration is not a recursive occurrence but
    a reference to an independent declaration. -/
def SrcTy.toSelfTy? (self : Nat) :
    (s : SrcTy) → Option (SelfTy Ty (kindUses s.kind) (kindAvoids s.kind))
  | .ext t     => some (.ty t)
  | .ref i     => if i = self then some .self else none
  | .array t   => SelfTy.array <$> t.toSelfTy? self
  | .list t    => SelfTy.list <$> t.toSelfTy? self
  | .option t  => SelfTy.option <$> t.toSelfTy? self
  | .thunk t   => SelfTy.thunk <$> t.toSelfTy? self
  | .task t    => SelfTy.task <$> t.toSelfTy? self
  | .promise t => SelfTy.promise <$> t.toSelfTy? self
  | .fn ps r   => SelfTy.fn ps <$> r.toSelfTy? self
  | .prod a b  =>
      match a.toSelfTy? self, b.toSelfTy? self with
      | some x, some y =>
          some (selfProd x y (kindUses_prod a.kind b.kind) (kindAvoids_prod a.kind b.kind))
      | _, _ => none

/-! ## Building the rows -/

/-- The fields of a non-recursive record or constructor. -/
def buildFields? : (fs : List (NonEmptyString × SrcTy)) → Option (FieldRow Ty (plainFieldShape fs))
  | [] => some .nil
  | (n, t) :: rest =>
      match t.toTy?, buildFields? rest with
      | some v, some r => some (.cons n v r)
      | _, _ => none

/-- The constructors of a non-recursive tagged union. -/
def buildCtors? : (cs : List SrcCtor) → Option (CtorRow Ty (cs.map plainCtorShape))
  | [] => some .nil
  | c :: rest =>
      match buildFields? c.fields, buildCtors? rest with
      | some fs, some r => some (.cons c.tag fs r)
      | _, _ => none

/-- The fields of a recursive record or constructor. -/
def buildSelfFields? (self : Nat) :
    (fs : List (NonEmptyString × SrcTy)) → Option (SelfFieldRow Ty (selfFieldShape fs))
  | [] => some .nil
  | (n, t) :: rest =>
      match t.toSelfTy? self, buildSelfFields? self rest with
      | some v, some r => some (.cons n v r)
      | _, _ => none

/-- The constructors of a recursive tagged union. -/
def buildRecCtors? (self : Nat) :
    (cs : List SrcCtor) → Option (RecCtorRow Ty (cs.map selfCtorShape))
  | [] => some .nil
  | c :: rest =>
      match buildSelfFields? self c.fields, buildRecCtors? self rest with
      | some fs, some r => some (.cons c.tag fs r)
      | _, _ => none

/-- The fields of one constructor of a family member — always defined. -/
def buildFamFields : (fs : List (NonEmptyString × SrcTy)) →
    FamFieldRow Ty (fs.map (fun f => (f.1, f.2.kind)))
  | [] => .nil
  | (n, t) :: rest => .cons n t.toFamTy (buildFamFields rest)

/-- The constructors of one family member. -/
def buildFamCtors : (cs : List SrcCtor) → FamCtorRow Ty (cs.map ctorShape)
  | [] => .nil
  | c :: rest => .cons c.tag (buildFamFields c.fields) (buildFamCtors rest)

/-- The members of a family. -/
def buildFamMembers : (b : SrcBlock) → FamMemberRow Ty (blockShape b)
  | [] => .nil
  | m :: rest => .cons m.name (buildFamCtors m.ctors) (buildFamMembers rest)

/-! ## The translation -/

/-- `SelfTy`, re-indexed along equalities of its two index bits. -/
def selfTyCast {u a u' a' : Bool} (x : SelfTy Ty u a) (hu : u = u') (ha : a = a') :
    SelfTy Ty u' a' :=
  cast (by rw [hu, ha]) x

/--
A member left with **one constructor carrying one field** — a newtype.  The wrapper has
no runtime representation, so:

* if the field does not mention the member, the member *is* the field: the result is
  the field's own `Ty`, and no schema is built at all
  (`structure Wrapper where x : Nat` is `Ty.nat`);
* if it does, the wrapper leaves the equation `Name = field[self := Name]` behind, and
  the result is `Ty.recAlias` (`structure Rose where kids : Array Rose` is the fixed
  point of `Array _`, i.e. a JS array of arrays of …).  The occurrence must be guarded,
  or the type has no values: `structure S where s : S` is `notWellFounded`.
-/
def toWrapperTy (self : Nat) (name : NonEmptyString) (t : SrcTy) : Except Reject Ty :=
  if hu : kindUses t.kind = true then
    if ha : kindAvoids t.kind = true then
      match t.toSelfTy? self with
      | none => .error .foreignReference
      | some body => .ok (.recAlias { name := name, body := selfTyCast body hu ha })
    else .error .notWellFounded
  else
    match t.toTy? with
    | none => .error .foreignReference
    | some ty => .ok ty

/-- A member of a genuinely mutual block. -/
def toFamilyTy (d : SrcDecl) : Except Reject Ty :=
  match d.block with
  | m₁ :: m₂ :: rest =>
      if h₁ : famShapeOk (blockShape (m₁ :: m₂ :: rest)) = true then
        if h₂ : d.member < (blockShape rest).length + 2 then
          .ok (.mutualRecursiveFamily
            { name := m₁.name
            , members := buildFamMembers (m₁ :: m₂ :: rest)
            , member := d.member
            , h_shape := h₁
            , h_member := h₂ })
        else .error .memberOutOfRange
      else .error .familyIllFormed
  | _ => .error .familyIllFormed

/-- An **erased** declaration that is not part of a genuine mutual block: one of the
    six non-mutual outcomes, chosen by "a wrapper?", "recursive?", "how many
    constructors?" and "any fields?". -/
def toSingleTy (self : Nat) (m : SrcMember) : Except Reject Ty :=
  if mentionsForeign m self then .error .foreignReference
  else
    match m.ctors with
    | [] => .error .voidMember
    | [c] =>
        match c.fields with
        | [] => .error .unitLikeMember
        | [f] => toWrapperTy self m.name f.2
        | f :: f₂ :: fs =>
            if memberMentions m self then
              match buildSelfFields? self (f :: f₂ :: fs) with
              | none => .error .foreignReference
              | some row =>
                  if h : recObjectShapeOk (selfFieldShape (f :: f₂ :: fs)) = true then
                    .ok (.recObject { name := m.name, fields := row, h_shape := h })
                  else .error .notWellFounded
            else
              match buildFields? (f :: f₂ :: fs) with
              | none => .error .foreignReference
              | some row =>
                  if h : fieldShapeOk (plainFieldShape (f :: f₂ :: fs)) = true then
                    .ok (.record { name := m.name, fields := row, h_names := h })
                  else .error .duplicateNames
    | c₁ :: c₂ :: cs =>
        if memberMentions m self then
          match buildRecCtors? self (c₁ :: c₂ :: cs) with
          | none => .error .foreignReference
          | some row =>
              if h : recTaggedUnionShapeOk ((c₁ :: c₂ :: cs).map selfCtorShape) = true then
                .ok (.recTaggedUnion { name := m.name, ctors := row, h_shape := h })
              else .error .notWellFounded
        else if memberHasFields m then
          match buildCtors? (c₁ :: c₂ :: cs) with
          | none => .error .foreignReference
          | some row =>
              if h : taggedUnionShapeOk ((c₁ :: c₂ :: cs).map plainCtorShape) = true then
                .ok (.taggedUnion { name := m.name, ctors := row, h_shape := h })
              else .error .duplicateNames
        else
          if h : fieldShapeOk (c₁.tag :: c₂.tag :: cs.map (·.tag)) = true then
            .ok (.enum { name := m.name, ctor1 := c₁.tag, ctor2 := c₂.tag
                       , ctorRest := cs.map (·.tag), h_tags := h })
          else .error .duplicateNames

/-- **The** translation of an (already erased) source declaration into `Ty`.  It is a
    function, so a declaration has at most one translation; `toTy_class` shows the
    shape it picks is forced. -/
def SrcDecl.toTy (d : SrcDecl) : Except Reject Ty :=
  match d.block[d.member]? with
  | none => .error .memberOutOfRange
  | some m => if isGenuinelyMutual d.block then toFamilyTy d else toSingleTy d.member m

/-- The translation of a declaration as the front-end reads it: erase unit-like fields
    and impossible constructors, then translate. -/
def RawDecl.toTy (d : RawDecl) : Except Reject Ty := SrcDecl.toTy d.erase

/-! ## Which declarations are representable -/

/-- The declarations `toTy` accepts, stated in source-level vocabulary: the member
    exists; a non-mutual declaration refers to no sibling; it is neither void nor
    unit-like; its names are distinct; and, when recursive, it is well-founded.  For a
    genuinely mutual block the conditions are the family invariants of
    `famShapeOk`. -/
def singleSupported (self : Nat) (m : SrcMember) : Bool :=
  !mentionsForeign m self &&
    (match m.ctors with
     | [] => false
     | [c] =>
         (match c.fields with
          | [] => false
          | [f] => !kindUses f.2.kind || kindAvoids f.2.kind
          | f :: f₂ :: fs =>
              if memberMentions m self then
                recObjectShapeOk (selfFieldShape (f :: f₂ :: fs))
              else fieldShapeOk (plainFieldShape (f :: f₂ :: fs)))
     | c₁ :: c₂ :: cs =>
         if memberMentions m self then
           recTaggedUnionShapeOk ((c₁ :: c₂ :: cs).map selfCtorShape)
         else if memberHasFields m then
           taggedUnionShapeOk ((c₁ :: c₂ :: cs).map plainCtorShape)
         else fieldShapeOk (c₁.tag :: c₂.tag :: cs.map (·.tag)))

/-- The (erased) declarations `SrcDecl.toTy` accepts. -/
def supported (d : SrcDecl) : Bool :=
  match d.block[d.member]? with
  | none => false
  | some m =>
      if isGenuinelyMutual d.block then
        famShapeOk (blockShape d.block) && decide (d.member < d.block.length)
      else singleSupported d.member m

/-- The declarations `RawDecl.toTy` accepts — erasure included. -/
def rawSupported (d : RawDecl) : Bool := supported d.erase

/-- Which of the shapes a `Ty` is; `none` for the built-in types, which are not user
    declarations — and which is also what an erased newtype becomes, since its `Ty` is
    its field's. -/
def tyClass : Ty → Option ShapeClass
  | .enum _                  => some .enum
  | .record _                => some .record
  | .taggedUnion _           => some .taggedUnion
  | .recTaggedUnion _        => some .recTaggedUnion
  | .recObject _             => some .recObject
  | .recAlias _              => some .recAlias
  | .mutualRecursiveFamily _ => some .mutualFamily
  | _                        => none

/-! ## When do the builders succeed?

A field can be translated iff it uses the block in the way its shape allows: an
ordinary field must not mention the block at all, and a field of a non-mutual
recursive declaration may mention only that declaration itself. -/

/-- Does this source type mention only member `self` of the block? -/
def refsOnly (self : Nat) (s : SrcTy) : Bool := s.kind.targets.all (· == self)

@[simp] theorem refsOnly_prod (self : Nat) (a b : SrcTy) :
    refsOnly self (.prod a b) = (refsOnly self a && refsOnly self b) := by
  simp [refsOnly, SrcTy.kind, FamFieldKind.targets]

theorem toTy?_isSome (s : SrcTy) : s.toTy?.isSome = s.kind.targets.isEmpty := by
  induction s with
  | ext t => rfl
  | ref i => rfl
  | array t ih | list t ih | option t ih | thunk t ih | task t ih | promise t ih =>
      simpa [SrcTy.toTy?, SrcTy.kind, FamFieldKind.targets, Option.isSome_map] using ih
  | fn ps r ih =>
      simpa [SrcTy.toTy?, SrcTy.kind, FamFieldKind.targets, Option.isSome_map] using ih
  | prod a b iha ihb =>
      rw [SrcTy.kind, FamFieldKind.targets, isEmpty_append, ← iha, ← ihb, SrcTy.toTy?]
      cases a.toTy? <;> cases b.toTy? <;> simp

theorem toSelfTy?_isSome (self : Nat) (s : SrcTy) :
    (s.toSelfTy? self).isSome = refsOnly self s := by
  induction s with
  | ext t => rfl
  | ref i =>
      by_cases h : i = self <;>
        simp [SrcTy.toSelfTy?, refsOnly, SrcTy.kind, FamFieldKind.targets, h]
  | array t ih | list t ih | option t ih | thunk t ih | task t ih | promise t ih =>
      simpa [SrcTy.toSelfTy?, refsOnly, SrcTy.kind, FamFieldKind.targets,
        Option.isSome_map] using ih
  | fn ps r ih =>
      simpa [SrcTy.toSelfTy?, refsOnly, SrcTy.kind, FamFieldKind.targets,
        Option.isSome_map] using ih
  | prod a b iha ihb =>
      rw [refsOnly_prod, ← iha, ← ihb, SrcTy.toSelfTy?]
      cases a.toSelfTy? self <;> cases b.toSelfTy? self <;> simp

theorem buildFields?_isSome (fs : List (NonEmptyString × SrcTy)) :
    (buildFields? fs).isSome = fs.all (fun f => f.2.kind.targets.isEmpty) := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
      obtain ⟨n, t⟩ := f
      rw [List.all_cons, ← toTy?_isSome, ← ih, buildFields?]
      cases t.toTy? <;> cases buildFields? rest <;> simp

theorem buildSelfFields?_isSome (self : Nat) (fs : List (NonEmptyString × SrcTy)) :
    (buildSelfFields? self fs).isSome = fs.all (fun f => refsOnly self f.2) := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
      obtain ⟨n, t⟩ := f
      rw [List.all_cons, ← toSelfTy?_isSome, ← ih, buildSelfFields?]
      cases t.toSelfTy? self <;> cases buildSelfFields? self rest <;> simp

theorem buildCtors?_isSome (cs : List SrcCtor) :
    (buildCtors? cs).isSome
      = cs.all (fun c => c.fields.all (fun f => f.2.kind.targets.isEmpty)) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      rw [List.all_cons, ← buildFields?_isSome, ← ih, buildCtors?]
      cases buildFields? c.fields <;> cases buildCtors? rest <;> simp

theorem buildRecCtors?_isSome (self : Nat) (cs : List SrcCtor) :
    (buildRecCtors? self cs).isSome
      = cs.all (fun c => c.fields.all (fun f => refsOnly self f.2)) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      rw [List.all_cons, ← buildSelfFields?_isSome, ← ih, buildRecCtors?]
      cases buildSelfFields? self c.fields <;> cases buildRecCtors? self rest <;> simp

/-- "Refers to no sibling" is exactly "every field refers only to `self`". -/
theorem not_mentionsForeign_iff (m : SrcMember) (self : Nat) :
    (!mentionsForeign m self)
      = m.ctors.all (fun c => c.fields.all (fun f => refsOnly self f.2)) := by
  simp [mentionsForeign, refsOnly, not_any_eq_all_not, bne]

/-- A field that refers only to `self` but does not refer to `self` refers to
    nothing. -/
theorem targets_isEmpty_of (self : Nat) (s : SrcTy) (h1 : refsOnly self s = true)
    (h2 : s.kind.targets.contains self = false) : s.kind.targets.isEmpty = true := by
  simp only [refsOnly] at h1
  cases h : s.kind.targets with
  | nil => rfl
  | cons x xs =>
      rw [h] at h1 h2
      simp at h1 h2
      exact absurd h1.1.symm h2.1

/-! ## The two theorems -/

/-- Did the translation succeed? -/
def isOk (r : Except Reject Ty) : Bool := r.toOption.isSome

@[simp] theorem isOk_ok (t : Ty) : isOk (.ok t) = true := rfl
@[simp] theorem isOk_error (e : Reject) : isOk (.error e) = false := rfl

/-- A member that mentions no sibling has only `self`-referring fields. -/
theorem refsOnly_of_not_mentionsForeign {m : SrcMember} {self : Nat}
    (h : mentionsForeign m self = false) {c : SrcCtor} (hc : c ∈ m.ctors)
    {f : NonEmptyString × SrcTy} (hf : f ∈ c.fields) : refsOnly self f.2 = true := by
  cases hcon : refsOnly self f.2 with
  | true => rfl
  | false =>
      exfalso
      simp only [refsOnly, List.all_eq_false] at hcon
      obtain ⟨x, hx, hxs⟩ := hcon
      have hm : mentionsForeign m self = true := by
        simp only [mentionsForeign, List.any_eq_true]
        exact ⟨c, hc, f, hf, x, hx, by simpa using hxs⟩
      rw [h] at hm
      exact Bool.noConfusion hm

/-- A member that does not mention itself has no field referring to itself. -/
theorem not_contains_of_not_memberMentions {m : SrcMember} {self : Nat}
    (h : memberMentions m self = false) {c : SrcCtor} (hc : c ∈ m.ctors)
    {f : NonEmptyString × SrcTy} (hf : f ∈ c.fields) :
    f.2.kind.targets.contains self = false := by
  cases hcon : f.2.kind.targets.contains self with
  | false => rfl
  | true =>
      exfalso
      have hm : memberMentions m self = true := by
        simp only [memberMentions, List.any_eq_true]
        exact ⟨c, hc, f, hf, hcon⟩
      rw [h] at hm
      exact Bool.noConfusion hm

/-- The wrapper case of the coverage theorem: a newtype is representable exactly when
    its single field either does not mention the type at all (the wrapper is erased
    into that field's `Ty`) or mentions it only under a guard (the fixed point has
    values). -/
theorem toWrapperTy_isOk (self : Nat) (name : NonEmptyString) (t : SrcTy)
    (h : refsOnly self t = true) :
    isOk (toWrapperTy self name t) = (!kindUses t.kind || kindAvoids t.kind) := by
  unfold toWrapperTy
  by_cases hu : kindUses t.kind = true
  · rw [dif_pos hu]
    by_cases ha : kindAvoids t.kind = true
    · rw [dif_pos ha]
      have hs : (t.toSelfTy? self).isSome = true := by
        rw [toSelfTy?_isSome]; exact h
      split
      · rename_i hb; rw [hb] at hs; simp at hs
      · simp [hu, ha]
    · simp only [Bool.not_eq_true] at ha
      rw [dif_neg (by simp [ha])]
      simp [ha, hu]
  · simp only [Bool.not_eq_true] at hu
    rw [dif_neg (by simp [hu])]
    have hempty : t.kind.targets.isEmpty = true := by
      simpa [kindUses] using hu
    have hs : t.toTy?.isSome = true := by rw [toTy?_isSome]; exact hempty
    split
    · rename_i hb; rw [hb] at hs; simp at hs
    · simp [hu]

/-- The non-mutual half of the coverage theorem. -/
theorem toSingleTy_isOk (self : Nat) (m : SrcMember) :
    isOk (toSingleTy self m) = singleSupported self m := by
  unfold toSingleTy singleSupported
  by_cases hF : mentionsForeign m self = true
  · simp [hF]
  · simp only [Bool.not_eq_true] at hF
    simp only [hF, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false]
    have hself : ∀ c ∈ m.ctors, c.fields.all (fun f => refsOnly self f.2) = true := by
      intro c hc
      simp only [List.all_eq_true]
      intro f hf
      exact refsOnly_of_not_mentionsForeign hF hc hf
    rcases hc : m.ctors with _ | ⟨c, cs⟩
    · simp
    · rcases cs with _ | ⟨c₂, cs⟩
      · -- one constructor
        have hcf : c.fields.all (fun f => refsOnly self f.2) = true :=
          hself c (by rw [hc]; simp)
        rcases hf : c.fields with _ | ⟨f, fs⟩
        · simp [hf]
        · rcases fs with _ | ⟨f₂, fs⟩
          · -- a wrapper
            have hrefs : refsOnly self f.2 = true := by
              rw [hf] at hcf; simpa using hcf
            simp [hf, toWrapperTy_isOk self m.name f.2 hrefs]
          · by_cases hR : memberMentions m self = true
            · have hs : (buildSelfFields? self (f :: f₂ :: fs)).isSome = true := by
                rw [buildSelfFields?_isSome]; rw [hf] at hcf; exact hcf
              rcases hb : buildSelfFields? self (f :: f₂ :: fs) with _ | row
              · rw [hb] at hs; simp at hs
              · by_cases hok : recObjectShapeOk (selfFieldShape (f :: f₂ :: fs)) = true <;>
                  simp [hf, hb, hok, hR]
            · simp only [Bool.not_eq_true] at hR
              have hempty : c.fields.all (fun f => f.2.kind.targets.isEmpty) = true := by
                simp only [List.all_eq_true]
                intro x hx
                exact targets_isEmpty_of self x.2
                  (refsOnly_of_not_mentionsForeign hF (by rw [hc]; simp) hx)
                  (not_contains_of_not_memberMentions hR (by rw [hc]; simp) hx)
              have hs : (buildFields? (f :: f₂ :: fs)).isSome = true := by
                rw [buildFields?_isSome]; rw [hf] at hempty; exact hempty
              rcases hb : buildFields? (f :: f₂ :: fs) with _ | row
              · rw [hb] at hs; simp at hs
              · by_cases hok : fieldShapeOk (plainFieldShape (f :: f₂ :: fs)) = true <;>
                  simp [hf, hb, hok, hR]
      · -- at least two constructors
        by_cases hR : memberMentions m self = true
        · have hcs : ((c :: c₂ :: cs).all
              (fun c => c.fields.all (fun f => refsOnly self f.2))) = true := by
            simp only [List.all_eq_true]
            intro x hx
            simpa using hself x (by rw [hc]; exact hx)
          have hs : (buildRecCtors? self (c :: c₂ :: cs)).isSome = true := by
            rw [buildRecCtors?_isSome]; exact hcs
          rcases hb : buildRecCtors? self (c :: c₂ :: cs) with _ | row
          · rw [hb] at hs; simp at hs
          · by_cases hok : recTaggedUnionShapeOk (selfCtorShape c :: selfCtorShape c₂ :: cs.map selfCtorShape) = true <;>
              simp [hb, hok, hR]
        · simp only [Bool.not_eq_true] at hR
          have hempty : ∀ c ∈ m.ctors,
              c.fields.all (fun f => f.2.kind.targets.isEmpty) = true := by
            intro x hx
            simp only [List.all_eq_true]
            intro f hf
            exact targets_isEmpty_of self f.2 (refsOnly_of_not_mentionsForeign hF hx hf)
              (not_contains_of_not_memberMentions hR hx hf)
          by_cases hfields : memberHasFields m = true
          · have hcs : ((c :: c₂ :: cs).all
                (fun c => c.fields.all (fun f => f.2.kind.targets.isEmpty))) = true := by
              simp only [List.all_eq_true]
              intro x hx
              simpa using hempty x (by rw [hc]; exact hx)
            have hs : (buildCtors? (c :: c₂ :: cs)).isSome = true := by
              rw [buildCtors?_isSome]; exact hcs
            rcases hb : buildCtors? (c :: c₂ :: cs) with _ | row
            · rw [hb] at hs; simp at hs
            · by_cases hok : taggedUnionShapeOk (plainCtorShape c :: plainCtorShape c₂ :: cs.map plainCtorShape) = true <;>
                simp [hb, hok, hR, hfields]
          · simp only [Bool.not_eq_true] at hfields
            by_cases hok : fieldShapeOk (c.tag :: c₂.tag :: cs.map (·.tag)) = true <;>
              simp [hfields, hok, hR]

/-- The shape of a block has one entry per member. -/
@[simp] theorem blockShape_length (b : SrcBlock) : (blockShape b).length = b.length := by
  simp [blockShape]

/-- The mutual half of the coverage theorem. -/
theorem toFamilyTy_isOk (d : SrcDecl) (h : isGenuinelyMutual d.block = true) :
    isOk (toFamilyTy d)
      = (famShapeOk (blockShape d.block) && decide (d.member < d.block.length)) := by
  have hlen : 2 ≤ d.block.length := by
    simp only [isGenuinelyMutual, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  unfold toFamilyTy
  rcases hb : d.block with _ | ⟨m₁, rest⟩
  · rw [hb] at hlen; simp at hlen
  · rcases rest with _ | ⟨m₂, rest⟩
    · rw [hb] at hlen; simp at hlen
    · dsimp only
      by_cases h1 : famShapeOk (blockShape (m₁ :: m₂ :: rest)) = true
      · rw [dif_pos h1]
        by_cases h2 : d.member < (blockShape rest).length + 2
        · rw [dif_pos h2]
          simp only [blockShape, List.length_map] at h2
          simp [h1, h2]
        · rw [dif_neg h2]
          simp only [blockShape, List.length_map] at h2
          simp [h1, h2]
      · rw [dif_neg h1]
        simp [h1]

/-- **Coverage.**  Every supported declaration is representable, and only those are:
    the translation is defined exactly on `supported`. -/
theorem toTy_isOk_iff_supported (d : SrcDecl) :
    isOk d.toTy = supported d := by
  unfold SrcDecl.toTy supported
  rcases hm : d.block[d.member]? with _ | m
  · simp
  · by_cases hmut : isGenuinelyMutual d.block = true
    · simp only [hmut, if_true]
      exact toFamilyTy_isOk d hmut
    · simp only [Bool.not_eq_true] at hmut
      simp only [hmut, Bool.false_eq_true, if_false]
      exact toSingleTy_isOk d.member m

/-- Coverage, erasure included. -/
theorem rawToTy_isOk_iff_supported (d : RawDecl) : isOk d.toTy = rawSupported d :=
  toTy_isOk_iff_supported d.erase

/-! ### The shape is forced -/

/-- A member with a field-carrying constructor has fields. -/
theorem memberHasFields_of {m : SrcMember} {c : SrcCtor} {f : NonEmptyString × SrcTy}
    {fs : List (NonEmptyString × SrcTy)} (hc : c ∈ m.ctors) (hf : c.fields = f :: fs) :
    memberHasFields m = true := by
  simp only [memberHasFields, List.any_eq_true]
  exact ⟨c, hc, by simp [hf]⟩

/-- A field that mentions something uses the block. -/
theorem kindUses_of_contains {k : FamFieldKind} {i : Nat}
    (h : k.targets.contains i = true) : kindUses k = true := by
  cases hk : k.targets with
  | nil => rw [hk] at h; simp at h
  | cons x xs => simp [kindUses, hk]

/-- A **recursive** wrapper is a `recAlias`. -/
theorem toWrapperTy_class {self : Nat} {name : NonEmptyString} {t : SrcTy} {ty : Ty}
    (h : toWrapperTy self name t = .ok ty) (hu : kindUses t.kind = true) :
    tyClass ty = some .recAlias := by
  unfold toWrapperTy at h
  rw [dif_pos hu] at h
  by_cases ha : kindAvoids t.kind = true
  · rw [dif_pos ha] at h
    split at h
    · simp at h
    · injection h with h'; subst h'; rfl
  · rw [dif_neg (by simp_all)] at h
    simp at h

/-- A **non-recursive** wrapper is erased completely: its `Ty` is the field's own `Ty`,
    so the declaration contributes no shape of its own. -/
theorem toWrapperTy_eq_field {self : Nat} {name : NonEmptyString} {t : SrcTy} {ty : Ty}
    (hu : kindUses t.kind = false) (h : t.toTy? = some ty) :
    toWrapperTy self name t = .ok ty := by
  unfold toWrapperTy
  rw [dif_neg (by simp [hu]), h]

/-- The non-mutual half of the uniqueness theorem.  It is stated for the shapes a
    declaration really has: when `singleClass` is `none` the declaration is erased (it
    is void, unit-like, or a non-recursive wrapper) and the `Ty` produced — if any — is
    the field's, whose own class says nothing about this declaration. -/
theorem toSingleTy_class {self : Nat} {m : SrcMember} {t : Ty} {c : ShapeClass}
    (h : toSingleTy self m = .ok t) (hc : singleClass self m = some c) :
    tyClass t = some c := by
  unfold toSingleTy at h
  by_cases hF : mentionsForeign m self = true
  · rw [if_pos hF] at h; simp at h
  rw [if_neg (by simpa using hF)] at h
  unfold singleClass at hc
  rcases hctors : m.ctors with _ | ⟨c₁, cs⟩
  · simp only [hctors] at h; simp at h
  rcases cs with _ | ⟨c₂, cs⟩
  · simp only [hctors] at h
    rcases hfields : c₁.fields with _ | ⟨f, fs⟩
    · simp only [hfields] at h; simp at h
    rcases fs with _ | ⟨f₂, fs⟩
    · -- a wrapper
      simp only [hfields] at h
      by_cases hR : memberMentions m self = true
      · have hcontains : f.2.kind.targets.contains self = true := by
          simpa [memberMentions, hctors, hfields] using hR
        have hcls : c = .recAlias := by
          simp [hctors, hfields, memberHasFields, memberIsWrapper, hR,
            ShapeDescriptor.class?] at hc
          exact hc.symm
        subst hcls
        exact toWrapperTy_class h (kindUses_of_contains hcontains)
      · simp only [Bool.not_eq_true] at hR
        simp [hctors, hfields, memberHasFields, memberIsWrapper, hR,
          ShapeDescriptor.class?] at hc
    · simp only [hfields] at h
      by_cases hR : memberMentions m self = true
      · rw [if_pos hR] at h
        split at h
        · simp at h
        · split at h
          · injection h with h'
            subst h'
            simp [hctors, hfields, memberHasFields, memberIsWrapper, hR,
              ShapeDescriptor.class?] at hc
            simp [tyClass, ← hc]
          · simp at h
      · simp only [Bool.not_eq_true] at hR
        rw [if_neg (by simp [hR])] at h
        split at h
        · simp at h
        · split at h
          · injection h with h'
            subst h'
            simp [hctors, hfields, memberHasFields, memberIsWrapper, hR,
              ShapeDescriptor.class?] at hc
            simp [tyClass, ← hc]
          · simp at h
  · simp only [hctors] at h
    by_cases hR : memberMentions m self = true
    · rw [if_pos hR] at h
      split at h
      · simp at h
      · split at h
        · injection h with h'
          subst h'
          simp [hctors, memberHasFields, memberIsWrapper, hR,
            ShapeDescriptor.class?] at hc
          simp [tyClass, ← hc]
        · simp at h
    · simp only [Bool.not_eq_true] at hR
      rw [if_neg (by simp [hR])] at h
      by_cases hfields : memberHasFields m = true
      · rw [if_pos hfields] at h
        split at h
        · simp at h
        · split at h
          · injection h with h'
            subst h'
            simp [hctors, hfields, memberIsWrapper, hR,
              ShapeDescriptor.class?] at hc
            simp [tyClass, ← hc]
          · simp at h
      · simp only [Bool.not_eq_true] at hfields
        rw [if_neg (by simp [hfields])] at h
        split at h
        · injection h with h'
          subst h'
          simp [hctors, hfields, memberIsWrapper, hR, ShapeDescriptor.class?] at hc
          simp [tyClass, ← hc]
        · simp at h

/-- The mutual half of the uniqueness theorem. -/
theorem toFamilyTy_class {d : SrcDecl} {t : Ty} (h : toFamilyTy d = .ok t) :
    tyClass t = some .mutualFamily := by
  unfold toFamilyTy at h
  repeat' split at h
  all_goals
    first
      | (injection h with h'
         subst h'
         rfl)
      | simp at h

/-- **Uniqueness of the interpretation.**  When the translation succeeds, the shape it
    produces is the one the four observables predict.  Together with
    `SchemaDisjoint.SchemaOf.descriptor_ne` — different shapes never describe the same
    declaration — this says the algorithm had no choice. -/
theorem toTy_class {d : SrcDecl} {t : Ty} {c : ShapeClass}
    (h : d.toTy = .ok t) (hc : classify d = some c) : tyClass t = some c := by
  unfold SrcDecl.toTy at h
  rcases hm : d.block[d.member]? with _ | m
  · simp only [hm] at h; exact absurd h (by simp)
  · simp only [hm] at h
    by_cases hmut : isGenuinelyMutual d.block = true
    · rw [if_pos hmut] at h
      rw [classify_eq_mutual d m hm hmut] at hc
      rw [toFamilyTy_class h]
      exact hc.symm ▸ rfl
    · simp only [Bool.not_eq_true] at hmut
      rw [if_neg (by simp [hmut])] at h
      rw [classify_eq_singleClass d m hm hmut] at hc
      exact toSingleTy_class h hc

/-- Uniqueness of the interpretation, erasure included. -/
theorem rawToTy_class {d : RawDecl} {t : Ty} {c : ShapeClass} (h : d.toTy = .ok t)
    (hc : d.classify = some c) : tyClass t = some c :=
  toTy_class (d := d.erase) h hc

/-- A declaration has at most one translation: `toTy` is a function. -/
theorem toTy_unique {d : SrcDecl} {t₁ t₂ : Ty} (h₁ : d.toTy = .ok t₁) (h₂ : d.toTy = .ok t₂) :
    t₁ = t₂ := by
  rw [h₁] at h₂; exact Except.ok.inj h₂

/-- The same, erasure included: erasure is a function too. -/
theorem rawToTy_unique {d : RawDecl} {t₁ t₂ : Ty} (h₁ : d.toTy = .ok t₁)
    (h₂ : d.toTy = .ok t₂) : t₁ = t₂ := by
  rw [h₁] at h₂; exact Except.ok.inj h₂

end LakeJs.Source

end
