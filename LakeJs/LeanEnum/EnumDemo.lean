module

public import LakeJs.LeanEnum.Schema
public meta import LakeJs.LeanEnum.Schema
public import LakeJs.LeanEnum.SchemaMeta
public meta import LakeJs.LeanEnum.SchemaMeta

public import LakeJs.LeanEnum.Enum
public meta import LakeJs.LeanEnum.Enum
public import LakeJs.LeanEnum.EnumMeta
public meta import LakeJs.LeanEnum.EnumMeta

public section
@[expose] section

/-! # Verification & Testing -/

inductive Action where
  | stop
  | move (x : Nat) (y : Nat)
  | jump (height : Nat)

def actionSchema : LeanEnumSchema := lean_schema% Action

-- Look up constructor schemas directly from schema
def moveCtor : LeanEnumCtorSchema :=
  (actionSchema.findCtor? "move").get (by decide)

def ltCtor : LeanEnumCtorSchema :=
  (orderingSchema.findCtor? "lt").get (by decide)

-- 1. Constructing with `h_mem` resolved automatically by `by decide`:
def testLt : LeanEnum orderingSchema Nat :=
  { ctor := ltCtor, fields := #v[] }

def testMove : LeanEnum actionSchema Nat :=
  LeanEnum.mk moveCtor #v[10, 20]

-- 2. Constructing via `mkEnum!` elaborator (boxed):
def testMoveByName : LeanEnum actionSchema Nat :=
  mkEnum! actionSchema "move" #v[10, 20]

def testConsByName : LeanEnum listSchema Nat :=
  mkEnum! listSchema "cons" #v[1, 2]

-- 3. `mkEnumAt!`: construct the typed/unboxed variant directly
def testMoveAt : LeanEnumAt actionSchema "move" Nat :=
  mkEnumAt! actionSchema "move" #v[10, 20]

def testStopAt : LeanEnumAt actionSchema "stop" Nat :=
  mkEnumAt! actionSchema "stop" #v[]

-- 4. Box (LeanEnumAt → LeanEnum): lossless, O(1)
def testBoxMove : LeanEnum actionSchema Nat :=
  testMoveAt.toLeanEnum

-- 5. Unbox (LeanEnum → Option (LeanEnumAt ctorName)):
--    succeeds when the runtime ctor name matches
def testUnboxMove : Option (LeanEnumAt actionSchema "move" Nat) :=
  testMove.unboxAt "move"   -- some { ctor := "move", castFields := #v[10, 20], ... }

def testUnboxStop : Option (LeanEnumAt actionSchema "stop" Nat) :=
  testMove.unboxAt "stop"   -- none: testMove is "move", not "stop"

/-! ### Exhaustiveness for `actionSchema` -/

/-- Every runtime value of `actionSchema` carries one of the three constructor names.
    The list of names is a compile-time literal, so this is decided by `decide`. -/
theorem action_ctorName_cases (e : LeanEnum actionSchema Nat) :
    e.ctor.name = "stop" ∨ e.ctor.name = "move" ∨ e.ctor.name = "jump" := by
  have h : ∀ s ∈ actionSchema.ctors.map (·.name),
      s = "stop" ∨ s = "move" ∨ s = "jump" := by decide
  exact h _ e.ctorName_mem_names

/-- The fallback ("unknown") branch of a `stop`/`move`/`jump` case split is unreachable:
    `unboxAt` cannot fail for all three names. -/
theorem action_unbox_exhaustive {e : LeanEnum actionSchema Nat}
    (h1 : e.unboxAt "stop" = none) (h2 : e.unboxAt "move" = none)
    (h3 : e.unboxAt "jump" = none) : False := by
  rcases action_ctorName_cases e with h | h | h
  · exact LeanEnum.ctorName_ne_of_unboxAt_eq_none h1 h
  · exact LeanEnum.ctorName_ne_of_unboxAt_eq_none h2 h
  · exact LeanEnum.ctorName_ne_of_unboxAt_eq_none h3 h

-- 6. Full case analysis with SAFE indexing via `castFields` (no `!`), written as a
--    `match` chain so each failing branch records an equation; the final, impossible
--    branch is discharged by `action_unbox_exhaustive` instead of returning "unknown".
--
-- `move.castFields : Vector Nat (actionSchema.ctorNumFields "move")`
-- The kernel reduces `actionSchema.ctorNumFields "move"` to `2`, so
-- `move.castFields[0]` proves `0 < 2` by `decide` automatically. ✓
def describeAction (e : LeanEnum actionSchema Nat) : String :=
  match h1 : e.unboxAt "stop" with
  | some _stop =>
    -- _stop : LeanEnumAt actionSchema "stop" Nat  →  castFields : Vector Nat 0
    "stop"
  | none =>
    match h2 : e.unboxAt "move" with
    | some move =>
      -- move : LeanEnumAt actionSchema "move" Nat  →  castFields : Vector Nat 2
      s!"move({move.castFields[0]}, {move.castFields[1]})"
    | none =>
      match h3 : e.unboxAt "jump" with
      | some jump =>
        -- jump : LeanEnumAt actionSchema "jump" Nat  →  castFields : Vector Nat 1
        s!"jump({jump.castFields[0]})"
      | none =>
        -- Unreachable: `actionSchema` only has stop/move/jump.
        (action_unbox_exhaustive h1 h2 h3).elim

#eval describeAction testMove                            -- "move(10, 20)"
#eval describeAction (mkEnum! actionSchema "stop" #v[])  -- "stop"
#eval describeAction (mkEnum! actionSchema "jump" #v[5]) -- "jump(5)"

/-! ### 7. The same thing with `match_enum`

`match_enum` is the surface syntax for exactly the case split above: one alternative
per constructor *name*, with the fields bound as a `Vector` of statically-known
length. The elaborator reads the schema off the type of the scrutinee, so a wrong
or missing constructor name is a compile-time error, and the unreachable fallback
branch is generated (and proved) automatically. -/

def describeActionMatch (e : LeanEnum actionSchema Nat) : String :=
  match_enum e with
  | "stop" => "stop"
  | "move" f => s!"move({f[0]}, {f[1]})"
  | "jump" f => s!"jump({f[0]})"

#eval describeActionMatch testMove                            -- "move(10, 20)"
#eval describeActionMatch (mkEnum! actionSchema "stop" #v[])  -- "stop"
#eval describeActionMatch (mkEnum! actionSchema "jump" #v[5]) -- "jump(5)"

/-- The two versions agree (they elaborate to the same case split). -/
example : describeActionMatch testMove = describeAction testMove := rfl

/-- A generic printer: the fields vector can also just be printed as a list. -/
def showAction (e : LeanEnum actionSchema Nat) : String :=
  match_enum e with
  | "stop" f => s!"stop {f.toList}"
  | "move" f => s!"move {f.toList}"
  | "jump" f => s!"jump {f.toList}"

#eval showAction testMove                            -- "move [10, 20]"

/-- An explicit catch-all is allowed when you do not want to list every constructor. -/
def isStop (e : LeanEnum actionSchema Nat) : Bool :=
  match_enum e with
  | "stop" => true
  | _ => false

#eval isStop testMove                            -- false
#eval isStop (mkEnum! actionSchema "stop" #v[])  -- true

/-- `match_enum` is not tied to `Action`: it works for any schema, since the schema is
    taken from the type of the scrutinee. Here it is on `listSchema`. -/
def showList (e : LeanEnum listSchema Nat) : String :=
  match_enum e with
  | "nil" => "nil"
  | "cons" f => s!"cons({f[0]}, {f[1]})"

#eval showList testConsByName                          -- "cons(1, 2)"
#eval showList (mkEnum! listSchema "nil" #v[])         -- "nil"

/-- `match_enum` returns any type, including proofs; here the result is a `Nat`. -/
def arity (e : LeanEnum actionSchema Nat) : Nat :=
  match_enum e with
  | "stop" f => f.size
  | "move" f => f.size
  | "jump" f => f.size

#eval arity testMove                                   -- 2

/-! ### 8. The schema invariant and the removed `h_numFields` field

`CtorNamesNodup` is a `Prop` (`List.Nodup` of the constructor names), still decided
by `decide` on a schema literal, while `ctorNamesNodupFast` is the linear-time
(hash-set) implementation used when a schema is validated at runtime. -/

example : CtorNamesNodup actionSchema.ctors := by decide

#eval ctorNamesNodupFast actionSchema.ctors                      -- true
#eval ctorNamesNodupFast (actionSchema.ctors ++ actionSchema.ctors) -- false

/-- The two formulations agree, on this schema as in general. -/
example : ctorNamesNodupFast actionSchema.ctors = true ↔ CtorNamesNodup actionSchema.ctors :=
  ctorNamesNodupFast_iff _

/-- `LeanEnumAt` now stores only `h_name`; the field count is a *theorem*. -/
example (e : LeanEnumAt actionSchema "move" Nat) : e.ctor.numFields = 2 := e.h_numFields

/-- Constructing a `LeanEnumAt` by hand needs `h_mem` and `h_name` only. -/
def testJumpAt : LeanEnumAt actionSchema "jump" Nat :=
  { ctor := (actionSchema.findCtor? "jump").get (by decide)
    fields := #v[7]
    h_name := by decide }

#eval testJumpAt.castFields[0]                                   -- 7

-- Compile-time checks performed by `match_enum` (all of these are errors):
--   * unknown constructor name:
--       match_enum e with | "fly" => "?" | ...   -- 'fly' is not in the schema
--   * duplicate alternative:
--       match_enum e with | "stop" => .. | "stop" => ..
--   * missing constructor and no catch-all:
--       match_enum e with | "stop" => "stop"     -- missing 'move', 'jump'

end
