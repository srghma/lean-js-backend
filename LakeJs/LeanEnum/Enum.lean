module

public import Std.Data.HashSet
public import LakeJs.LeanEnum.Schema

@[expose] public section

/-! ### 2. `LeanEnum` (Zero Redundant Lookups) -/

/--
A runtime representation of an inductive value.
- `ctor`: The constructor schema (holds name and field count).
- `fields`: Sized directly by `ctor.numFields` (0 lookups).
- `h_mem`: Proof in `Prop` that `ctor` belongs to `schema` (checked via `by decide`).
-/
structure LeanEnum (schema : LeanEnumSchema) (expr : Type u) where
  ctor   : LeanEnumCtorSchema
  fields : Vector expr ctor.numFields
  h_mem  : schema.ctors.contains ctor := by decide
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Helper projection to access the constructor name directly. -/
def LeanEnum.ctorName (e : LeanEnum schema expr) : String :=
  e.ctor.name

/-- Look up a constructor schema by name with compile-time verification. -/
def LeanEnumSchema.getCtor (schema : LeanEnumSchema) (ctorName : String)
    (h : schema.hasCtor ctorName := by decide) : LeanEnumCtorSchema :=
  (schema.findCtor? ctorName).get h

/-- Smart constructor using a `LeanEnumCtorSchema` directly. -/
def LeanEnumSchema.mkEnum (schema : LeanEnumSchema) {expr : Type u}
    (ctor : LeanEnumCtorSchema)
    (fields : Vector expr ctor.numFields)
    (h_mem : schema.ctors.contains ctor := by decide) :
    LeanEnum schema expr :=
  ⟨ctor, fields, h_mem⟩

/-! ### 3. Typed Constructor: `LeanEnumAt` -/

/--
`LeanEnumAt schema ctorName expr` is the **unboxed** / **constructor-indexed** variant of
`LeanEnum` where the constructor name is fixed at the **type level**.

Internally it holds the same `ctor` + `fields` as `LeanEnum`, plus:
- `h_mem`  : proof that `ctor ∈ schema.ctors` (inherited from `LeanEnum`)
- `h_name` : proof that `ctor.name = ctorName`  ← the key invariant

Note that `h_name` is the *only* extra field. In particular no separate
`h_numFields : ctor.numFields = schema.ctorNumFields ctorName` is stored: it is
redundant, being derivable from `h_mem` and `h_name` alone (see the theorem
`LeanEnumAt.h_numFields` below, via `ctorNumFields_of_mem`). Storing it would only
mean one more proof obligation at every construction site, with nothing gained, so
it is a theorem instead — and `e.h_numFields` still works by dot notation.

The type-level `ctorName` lets you do **case analysis at the type level**:
```
if let some v := e.unboxAt "none" then
  -- v : LeanEnumAt schema "none" expr
  -- statically known: it's `none`
```
Boxing back to `LeanEnum` (erasing the type-level name) is lossless and O(1).
-/
structure LeanEnumAt (schema : LeanEnumSchema) (ctorName : String) (expr : Type u)
  extends LeanEnum schema expr where
  h_name : ctor.name = ctorName
  deriving Repr, DecidableEq

instance [BEq expr] : BEq (LeanEnumAt schema ctorName expr) where
  beq a b := a.toLeanEnum == b.toLeanEnum

instance [BEq expr] [ReflBEq expr] : ReflBEq (LeanEnumAt schema ctorName expr) where
  rfl {a} := ReflBEq.rfl (a := a.toLeanEnum)

instance [BEq expr] [LawfulBEq expr] : LawfulBEq (LeanEnumAt schema ctorName expr) where
  eq_of_beq {a b} h := by
    have hv : a.toLeanEnum = b.toLeanEnum := LawfulBEq.eq_of_beq h
    cases a; cases b; simp_all

/-- If `ctor ∈ schema.ctors` (by `BEq`) and `ctor.name = ctorName`,
    then `ctor.numFields = schema.ctorNumFields ctorName`.

    Proof: `h_mem` says `ctor` occurs in `schema.ctors`, and `schema.h_ctors_nodup`
    says constructor names are pairwise distinct, so looking `ctor` up by its own
    name (`= ctorName`) finds exactly `ctor`. -/
theorem ctorNumFields_of_mem
    {schema : LeanEnumSchema} {ctor : LeanEnumCtorSchema} {ctorName : String}
    (h_mem  : schema.ctors.contains ctor = true)
    (h_name : ctor.name = ctorName) :
    ctor.numFields = schema.ctorNumFields ctorName := by
  subst h_name
  have h_in : ctor ∈ schema.ctors := List.contains_iff_mem.mp h_mem
  simp [LeanEnumSchema.ctorNumFields, LeanEnumSchema.findCtor?,
    find?_name_eq_self schema.h_ctors_nodup h_in]

/-- The field count carried at runtime agrees with the statically-known schema lookup.
    This used to be a field of `LeanEnumAt`; it is redundant, since `h_mem` (from
    `LeanEnum`) together with `h_name` already determine it. Dot notation keeps it
    usable exactly as before: `e.h_numFields`. -/
theorem LeanEnumAt.h_numFields (e : LeanEnumAt schema ctorName expr) :
    e.ctor.numFields = schema.ctorNumFields ctorName :=
  ctorNumFields_of_mem e.h_mem e.h_name

/-- Fields projected to the statically-known count `schema.ctorNumFields ctorName`.
    Enables `e.castFields[i]` with bounds proved by `decide` — no `!` needed. -/
def LeanEnumAt.castFields (e : LeanEnumAt schema ctorName expr) :
    Vector expr (schema.ctorNumFields ctorName) :=
  e.fields.cast e.h_numFields

def LeanEnum.unboxAt (e : LeanEnum schema expr) (ctorName : String) :
    Option (LeanEnumAt schema ctorName expr) :=
  if h : e.ctor.name = ctorName then
    some { toLeanEnum := e, h_name := h }
  else
    none

/-- `unboxAt` fails exactly when the runtime constructor name differs. -/
theorem LeanEnum.unboxAt_eq_none_iff (e : LeanEnum schema expr) (ctorName : String) :
    e.unboxAt ctorName = none ↔ e.ctor.name ≠ ctorName := by
  unfold LeanEnum.unboxAt
  split <;> simp_all

/-- `unboxAt` succeeds exactly when the runtime constructor name matches. -/
theorem LeanEnum.unboxAt_isSome_iff (e : LeanEnum schema expr) (ctorName : String) :
    (e.unboxAt ctorName).isSome ↔ e.ctor.name = ctorName := by
  unfold LeanEnum.unboxAt
  split <;> simp_all

/-- If `unboxAt` fails, the runtime constructor name differs. -/
theorem LeanEnum.ctorName_ne_of_unboxAt_eq_none {e : LeanEnum schema expr} {ctorName : String}
    (h : e.unboxAt ctorName = none) : e.ctor.name ≠ ctorName :=
  (e.unboxAt_eq_none_iff ctorName).mp h

/-- Every value of `LeanEnum schema expr` carries one of the schema's constructor names. -/
theorem LeanEnum.ctorName_mem_names (e : LeanEnum schema expr) :
    e.ctor.name ∈ schema.ctors.map (·.name) :=
  List.mem_map_of_mem (List.contains_iff_mem.mp e.h_mem)

/-- **General exhaustiveness principle.** If `unboxAt` fails for every constructor name
    of the schema, we get a contradiction: a `LeanEnum` always carries one of them.
    This is what makes the "unknown"/fallback branch of a complete case split
    provably unreachable. -/
theorem LeanEnum.exhaustive {schema : LeanEnumSchema} {expr : Type u} (e : LeanEnum schema expr)
    (h : ∀ name ∈ schema.ctors.map (·.name), e.unboxAt name = none) : False :=
  LeanEnum.ctorName_ne_of_unboxAt_eq_none
    (h e.ctor.name e.ctorName_mem_names) rfl

/-! ### 4. Building blocks for the `match_enum` eliminator

A `match_enum` expansion is a chain of `unboxAt` tests. When the listed constructor
names cover the whole schema, the final "nothing matched" branch is impossible, and
the elaborator has to *produce a proof term* of `False` from the individual branch
equations `e.unboxAt "…" = none`. The definitions below give it exactly that: a
cons-list of those equations (`NoneAtAll`) plus a coverage check that is decided on
the concrete schema literal. -/

/-- `e.NoneAtAll names` says that unboxing `e` at each name in `names` fails. -/
def LeanEnum.NoneAtAll {schema : LeanEnumSchema} {expr : Type u}
    (e : LeanEnum schema expr) (names : List String) : Prop :=
  ∀ n ∈ names, e.unboxAt n = none

theorem LeanEnum.noneAtAll_nil {schema : LeanEnumSchema} {expr : Type u}
    (e : LeanEnum schema expr) : e.NoneAtAll [] := by
  intro n hn; cases hn

theorem LeanEnum.noneAtAll_cons {schema : LeanEnumSchema} {expr : Type u}
    {e : LeanEnum schema expr} {n : String} {ns : List String}
    (h : e.unboxAt n = none) (hs : e.NoneAtAll ns) : e.NoneAtAll (n :: ns) := by
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm'
  · exact h
  · exact hs m hm'

/-- **Exhaustiveness, list form.** If `names` covers every constructor name of the
    schema (a decidable check on the schema literal) and unboxing fails at each of
    those names, we have a contradiction. This is the term the `match_enum`
    elaborator emits for the unreachable fallback branch. -/
theorem LeanEnum.exhaustive_of_cover {schema : LeanEnumSchema} {expr : Type u}
    (e : LeanEnum schema expr) (names : List String)
    (hcover : schema.ctors.all (fun c => names.contains c.name) = true)
    (hnone : e.NoneAtAll names) : False := by
  have h_in : e.ctor ∈ schema.ctors := List.contains_iff_mem.mp e.h_mem
  have h_name : names.contains e.ctor.name = true := List.all_eq_true.mp hcover _ h_in
  exact LeanEnum.ctorName_ne_of_unboxAt_eq_none
    (hnone _ (List.contains_iff_mem.mp h_name)) rfl

end
