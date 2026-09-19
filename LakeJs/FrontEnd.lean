import Lean
import Lean.Compiler.LCNF
import Lean.Elab.PreDefinition.WF.Eqns
import LakeJs.Totality
import LakeJs.FrontEndPrimExterns

/-!
# The front end: from what the `.olean` stores to a `Term` of the one grammar

This is the part of the old `LakeJs/FromLcnf.lean` that the plan of record keeps — reading
the **`saveBase` LCNF phase** out of the compiled module and producing a term of
`LakeJs.Expr` — rewritten against the *current* grammar, in which the one way to repeat
work is `Term.fix`, which carries its own rank.

The front end is deliberately a **whitelist**.  A declaration is translated only when

* `LakeJs.Totality` accepts it — it is not `partial`, not `unsafe`, not an `IO` function,
  not a partial fixpoint, and has a body to read;
* Lean recorded that it is non-recursive, *structurally* recursive, or recursive over a
  *well-founded* relation whose measure this module can transcribe;
* and every construct of its LCNF body is one of the small set below.

Anything else is refused with a message that names the construct, rather than translated
approximately.

## What a recursion becomes

`Term.fix ps k measure body stuck` carries a **lexicographic measure**: `k` components,
each a term of the parameters.  The evaluator recomputes the whole vector at every self
call and descends only when it is strictly smaller than the vector the current activation
was entered with; when it is not, the recursion answers `stuck`.  So a recursive Lean
declaration becomes **one** `fix` taking all of its parameters:

* a **structural** recursion on a `Nat` argument is measured by that argument; on any
  other argument by `Term.structSize` of it;
* a **well-founded** recursion is measured by the components of its `termination_by`
  clause, transcribed verbatim and in order.  Ackermann's `termination_by m n => (m, n)`
  is the two-component measure `[m, n]` of one `fix`, not a nest.

A self call supplies every argument and says nothing else: there is no iteration bound to
guess, no level to assign a call to, and no `+1`.  The one thing the front end has to get
right is the measure, and a wrong measure cannot produce a wrong answer — it can only fail
to descend, which the `stuck` branch makes observable.

A **mutual clique** becomes one `fix` over the tag of the member and the parameters of
every member, with the two-component measure `[measure of the member the tag selects,
phase]`, where the phase counts down along the order Lean records the members in.  A call
from one member to another that does not descend on the measure — `cata` handing its
argument to `cataMap` unchanged — descends on the phase instead.

## The output

`translateModule` produces, for a module, the text of its `<Module>Program.lean`: a Lean
file whose header comment is the `Term` tree of every declaration in the notation of
`LakeJs.ExprPretty`, followed by the program itself as Lean source — a `Sig`, one `Term`
per declaration and the `Program` telescope that ties them together.  The driver
elaborates that file against `import LakeJs` before writing it.  That elaboration is the
guarantee: what the file contains is a term of the grammar, and therefore terminating by
construction.
-/

namespace LakeJs.FrontEnd

open Lean Lean.Meta Lean.Compiler.LCNF

/-! ## Why a declaration did not become a `Term`

A declaration the front end does not write out is one of two very different things, and
the generated `<Module>Program.lean` keeps them apart.

* It is **outside the language**: its type, or the type of one of its parameters, has no
  counterpart in `Ty` — a `Repr`, a `Sort`-valued motive, a hash container, a type with
  no values — or it is polymorphic and nothing in the module says at which types to
  compile it.  Nothing is wrong: the backend is a monomorphic first-order language, and
  this declaration is not a program of it.
* Or it **is** a program of the language and the translation nevertheless failed.  That
  is a gap in the front end, and the generated file says `not translated`.

The first kind is thrown with `throwOutsideLanguage`, which marks the message; the second
is an ordinary `throwError`. -/

/-- The mark `throwOutsideLanguage` puts in front of its message. -/
def outsideLanguageTag : String := "⟪outside-the-language⟫"

/-- Refuse a declaration because it is not a program of the language at all — as opposed
    to one the front end failed to translate. -/
def throwOutsideLanguage {α} (msg : MessageData) : MetaM α :=
  throwError "{outsideLanguageTag}{msg}"

/-- Is this the message of a declaration that is outside the language, and what does it
    say once the mark is taken off? -/
def outsideLanguage? (msg : String) : Option String :=
  if msg.startsWith outsideLanguageTag then
    some (msg.drop outsideLanguageTag.length).toString
  else none

/-! ## The intermediate tree

`Src` is the same language as `LakeJs.Expr.Term`, with **named** variables rather than de
Bruijn indices and with no proofs in it: it is what the translation builds, and the two
renderers below turn it into the tree in the header comment of a `<Module>Program.lean`
and into its Lean source.  It is not
a second grammar — nothing runs a `Src`; the only thing that is ever run is the `Term` the
Lean source elaborates to. -/
/-- A declaration, together with the types it is compiled at.

    The type language is monomorphic, so a *polymorphic* declaration has no type of its
    own; what has one is the declaration at an instantiation of its type parameters.  The
    front end therefore compiles such a declaration once per instantiation its callers
    use, and this is the key of that instantiation: the Lean declaration and the types its
    type parameters are taken at, in the order the parameters appear.  `targs` is empty for
    a monomorphic declaration, which is compiled exactly once. -/
structure Inst where
  /-- The Lean declaration. -/
  name : Name
  /-- The types its type parameters are taken at.  Empty when it has none. -/
  targs : List Expr := []
  deriving Inhabited

inductive Src where
  /-- A local variable, by the (unique) name of the LCNF free variable it came from. -/
  | var (x : Name)
  /-- A declaration of the program's signature: the name it is declared under, and the
      Lean declaration (at the types it is compiled at) it came from, if it is one — a
      merged mutual clique is not. -/
  | glob (name : String) (decl : Option Inst)
  /-- A `Nat` literal. -/
  | natLit (n : Nat)
  /-- A `Bool` literal. -/
  | boolLit (b : Bool)
  /-- An `Int` literal. -/
  | intLit (i : Int)
  /-- A `String` literal. -/
  | strLit (s : String)
  /-- A `Char` literal. -/
  | charLit (c : Char)
  /-- A literal of a fixed-width scalar type, as the whole number it holds. -/
  | scalarLit (s : SScalar) (n : Nat)
  /-- An application, of one argument. -/
  | ap (f a : Src)
  /-- A one-parameter abstraction. -/
  | lam (x : Name) (b : Src)
  /-- `let x := v; b`. -/
  | letE (x : Name) (v b : Src)
  /-- `if c then t else e`. -/
  | ite (c t e : Src)
  /-- A call of a function of the runtime: the helper that names it, its argument types
      and its result type (which is what the tree prints), and its arguments. -/
  | op (helper : String) (argTys : List STy) (ret : STy) (args : List Src)
  /-- The structural size of a value: the measure of a structural recursion. -/
  | structSize (e : Src)
  /-- A call of the recursion being translated, with its full argument list. -/
  | selfCall (args : List Src)
  /-- The one recursion of a declaration: its parameters, the components of its
      lexicographic measure (outermost first), its body, and its answer when a self call
      does not make that measure descend. -/
  | fix (params : List (Name × STy)) (measures : List Src) (body : Src) (stuck : Src)
  /-- A constructor of a type that has a layout: the type it is built at, its tag, the
      types of its fields and their values. -/
  | ctorS (ty : STy) (tag : Nat) (fieldTys : List STy) (args : List Src)
  /-- A field of a value of a one-constructor type. -/
  | projS (e : Src) (tag field : Nat)
  /-- A dispatch on the tag of a value: one branch per constructor tested, each binding
      the fields of that constructor, and a default branch when the branches are not
      exhaustive. -/
  | caseS (scrut : Src) (alts : List (Nat × List (Name × STy) × Src)) (deflt : Option Src)
  deriving Inhabited

/-- The canonical inhabitant of a type: what a stuck recursion and an unreachable branch
    answer with. -/
partial def STy.dflt : STy → Src
  | .nat => .natLit 0
  | .bool => .boolLit false
  | .int => .intLit 0
  | .string => .strLit ""
  | .char => .charLit 'A'
  | .scalar s => .scalarLit s 0
  | .fn _ b => .lam `_ b.dflt
  | .array a =>
      .op ("(arrEmpty (α := " ++ a.source ++ "))") [.nat] (.array a) [.natLit 0]
  | .option a => .ctorS (.option a) 0 [] []
  | .prod a b => .ctorS (.prod a b) 0 [a, b] [a.dflt, b.dflt]
  | .selfRef => .natLit 0
  | .data src rsrc pp cs =>
      -- the canonical value is built with a constructor that does not mention the type
      -- itself, so that a recursive type has a finite one
      match cs.zipIdx.find? (fun (c, _) => !c.2.contains STy.selfRef) with
      | some ((_, fields), tag) =>
          .ctorS (.data src rsrc pp cs) tag fields (fields.map STy.dflt)
      | none => .natLit 0

/-! ## Rendering -/

/-- The de Bruijn index of a name in a context, innermost first. -/
private def idxOf (bs : List Name) (x : Name) : Option Nat := bs.idxOf? x

/-- `.there`s enough to reach position `k` of a signature. -/
private def globRefSource : Nat → String
  | 0 => ".here"
  | k + 1 => "(.there " ++ globRefSource k ++ ")"

/-- `.tail`s enough to reach a de Bruijn index. -/
private def deBruijnSource : Nat → String
  | 0 => ".head"
  | k + 1 => "(.tail " ++ deBruijnSource k ++ ")"

/-- A spine, as Lean source. -/
private def spineSource (args : List String) : String :=
  args.foldr (fun a acc => "(.cons " ++ a ++ " " ++ acc ++ ")") ".nil"

/-- The environment a renderer walks with: the variables in scope (innermost first) and
    the names the signature declares (in signature order).  A declaration has at most one
    recursion, so a self call always names the innermost one. -/
structure RCtx where
  /-- The variables in scope, innermost first. -/
  vars : List Name := []
  /-- The names the signature declares, in order. -/
  sig : List String := []

/-- Render a `Src` as Lean source: a term of `LakeJs.Expr.Term`. -/
partial def Src.toLean (ctx : RCtx) : Src → String
  | .var x =>
      match idxOf ctx.vars x with
      | some i => "(♯" ++ toString i ++ ")"
      | none => "(UNBOUND_VARIABLE_" ++ toString x ++ ")"
  | .glob n _ =>
      match ctx.sig.idxOf? n with
      | some i => "(Term.global " ++ globRefSource i ++ ")"
      | none => "(UNDECLARED_GLOBAL_" ++ n ++ ")"
  | .natLit n => "(Term.natL " ++ toString n ++ ")"
  | .boolLit b => "(Term.boolL " ++ (if b then "true" else "false") ++ ")"
  | .intLit i => "(Term.intL (" ++ toString i ++ "))"
  | .strLit s => "(Term.strL " ++ s.quote ++ ")"
  | .charLit c => "(Term.lit (.char (Char.ofNat " ++ toString c.toNat ++ ")))"
  | .scalarLit s n => "(Term.lit (." ++ s.name ++ " " ++ s.litSource n ++ "))"
  | .ap f a => "(Term.ap " ++ f.toLean ctx ++ " " ++ a.toLean ctx ++ ")"
  | .lam x b => "(Term.lam " ++ b.toLean { ctx with vars := x :: ctx.vars } ++ ")"
  | .letE x v b =>
      "(Term.letE " ++ v.toLean ctx ++ " " ++
        b.toLean { ctx with vars := x :: ctx.vars } ++ ")"
  | .ite c t e =>
      "(Term.ite " ++ c.toLean ctx ++ " " ++ t.toLean ctx ++ " " ++ e.toLean ctx ++ ")"
  | .op helper _ _ args =>
      "(" ++ helper ++ String.join (args.map (fun a => " " ++ a.toLean ctx)) ++ ")"
  | .structSize e => "(Term.structSize " ++ e.toLean ctx ++ ")"
  | .selfCall args =>
      "(Term.selfCall " ++ deBruijnSource 0 ++ " " ++
        spineSource (args.map (fun a => a.toLean ctx)) ++ ")"
  | .fix ps measures body stuck =>
      let inner : RCtx := { ctx with vars := ps.map Prod.fst ++ ctx.vars }
      "(Term.fix [" ++ String.intercalate ", " (ps.map (fun p => p.2.source)) ++ "] " ++
        toString measures.length ++ " " ++
        spineSource (measures.map (fun m => m.toLean inner)) ++ " " ++
        body.toLean inner ++ " " ++ stuck.toLean inner ++ ")"
  | .ctorS ty tag fieldTys args =>
      "(Term.ctor (τ := " ++ ty.source ++ ") " ++ toString tag ++ " [" ++
        String.intercalate ", " (fieldTys.map STy.source) ++ "] (by rfl) " ++
        spineSource (args.map (fun a => a.toLean ctx)) ++ ")"
  | .projS e tag field =>
      "(Term.proj " ++ e.toLean ctx ++ " " ++ toString tag ++ " " ++ toString field ++
        " (by rfl) (by rfl))"
  | .caseS scrut alts deflt =>
      let base :=
        match deflt with
        | some d => "(Alts.deflt " ++ d.toLean ctx ++ ")"
        | none => "Alts.nilFull"
      let altsSrc := alts.foldr (init := base) fun (tag, fields, body) rest =>
        let inner : RCtx := { ctx with vars := fields.map Prod.fst ++ ctx.vars }
        "(Alts.cons " ++ toString tag ++ " [" ++
          String.intercalate ", " (fields.map (fun f => f.2.source)) ++
          "] (by rfl) " ++ body.toLean inner ++ " " ++ rest ++ ")"
      "(Term.caseTag " ++ scrut.toLean ctx ++ " " ++ altsSrc ++ " (by rfl))"

/-- `n` spaces, as `LakeJs.ExprPretty` indents. -/
private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- Render a `Src` the way `LakeJs.ExprPretty` prints the `Term` it elaborates to. -/
partial def Src.toPretty (ctx : RCtx) (ind : Nat) : Src → String
  | .var x =>
      match idxOf ctx.vars x with
      | some i => "♯" ++ toString i
      | none => "?" ++ toString x
  | .glob n _ => "@" ++ n
  | .natLit n => toString n ++ "#"
  | .boolLit b => if b then "true" else "false"
  | .intLit i => toString i ++ "i"
  | .strLit s => "\"" ++ s ++ "\""
  | .charLit c => "'" ++ String.singleton c ++ "'"
  | .scalarLit s n => toString n ++ "#" ++ s.name
  | .ap f a => "(" ++ f.toPretty ctx ind ++ " ⬝ " ++ a.toPretty ctx ind ++ ")"
  | .lam x b => "ƛ " ++ b.toPretty { ctx with vars := x :: ctx.vars } ind
  | .letE x v b =>
      "let ♯ := " ++ v.toPretty ctx ind ++ ";\n" ++ spaces ind ++
        b.toPretty { ctx with vars := x :: ctx.vars } ind
  | .ite c t e =>
      "if " ++ c.toPretty ctx ind ++ " then " ++ t.toPretty ctx ind ++ " else " ++
        e.toPretty ctx ind
  | .op _ argTys ret args =>
      -- an extern applied to its arguments, one at a time, as `Term.callExtern` is
      let head := "extern⟨" ++ prettyTyList argTys ++ " ⇒ " ++ ret.pretty ++ "⟩"
      args.foldl (fun acc a => "(" ++ acc ++ " ⬝ " ++ a.toPretty ctx ind ++ ")") head
  | .structSize e => "size(" ++ e.toPretty ctx ind ++ ")"
  | .selfCall args =>
      "self0⟨↓⟩(" ++
        String.intercalate ", " (args.map (fun a => a.toPretty ctx ind)) ++ ")"
  | .ctorS _ tag fieldTys args =>
      "ctor" ++ toString tag ++ "(" ++ prettyTyList fieldTys ++ ")(" ++
        String.intercalate ", " (args.map (fun a => a.toPretty ctx ind)) ++ ")"
  | .projS e tag field =>
      "proj" ++ toString tag ++ "." ++ toString field ++ "(" ++ e.toPretty ctx ind ++ ")"
  | .caseS scrut alts deflt =>
      let branches := String.join (alts.map fun (tag, fields, body) =>
        let inner : RCtx := { ctx with vars := fields.map Prod.fst ++ ctx.vars }
        spaces (ind + 2) ++ "| " ++ toString tag ++ "(" ++
          prettyTyList (fields.map Prod.snd) ++ ") => " ++
          body.toPretty inner (ind + 4) ++ "\n")
      let dfltSrc :=
        match deflt with
        | some d => spaces (ind + 2) ++ "| _ => " ++ d.toPretty ctx (ind + 4) ++ "\n"
        | none => ""
      "case " ++ scrut.toPretty ctx ind ++ " of\n" ++ branches ++ dfltSrc
  | .fix ps measures body stuck =>
      let inner : RCtx := { ctx with vars := ps.map Prod.fst ++ ctx.vars }
      let measureSrc :=
        String.intercalate ", " (measures.map (fun m => m.toPretty inner (ind + 2)))
      "fix (" ++ prettyTyList (ps.map Prod.snd) ++ ")" ++
        " measure [ " ++ measureSrc ++ " ] body {\n" ++
        spaces (ind + 2) ++ body.toPretty inner (ind + 2) ++ "\n" ++
        spaces ind ++ "} stuck { " ++ stuck.toPretty inner (ind + 2) ++ " }"

/-! ## The functions of the runtime the front end knows -/

/-- One entry of the small extern table: the Lean function, the helper of
    `LakeJs.Expr.Ops` that calls it, and its type. -/
structure OpInfo where
  /-- The Lean function it translates. -/
  lean : Name
  /-- The helper of `LakeJs.Expr.Ops` that builds the call. -/
  helper : String
  /-- The types of its arguments. -/
  argTys : List STy
  /-- The type of its result. -/
  ret : STy

/-- The pure runtime functions the front end can translate.  Anything else is refused:
    the point of the table is that a call of the runtime is checked against the type the
    catalogue of `LakeJs.Externs` gives it. -/
def opTable : List OpInfo :=
  [ ⟨``Nat.add, "natAdd", [.nat, .nat], .nat⟩
  , ⟨``Nat.sub, "natSub", [.nat, .nat], .nat⟩
  , ⟨``Nat.mul, "natMul", [.nat, .nat], .nat⟩
  , ⟨``Nat.mod, "natMod", [.nat, .nat], .nat⟩
  , ⟨``Nat.beq, "natEq", [.nat, .nat], .bool⟩
  , ⟨``Nat.decEq, "natEq", [.nat, .nat], .bool⟩
  , ⟨``instDecidableEqNat, "natEq", [.nat, .nat], .bool⟩
  , ⟨``Nat.ble, "natLe", [.nat, .nat], .bool⟩
  , ⟨``Nat.decLe, "natLe", [.nat, .nat], .bool⟩
  , ⟨``Nat.blt, "natLt", [.nat, .nat], .bool⟩
  , ⟨``Nat.decLt, "natLt", [.nat, .nat], .bool⟩
  , ⟨``Nat.div, "natDiv", [.nat, .nat], .nat⟩
  , ⟨``Nat.pow, "natPow", [.nat, .nat], .nat⟩
  , ⟨``Nat.shiftLeft, "natShiftLeft", [.nat, .nat], .nat⟩
  , ⟨``Nat.shiftRight, "natShiftRight", [.nat, .nat], .nat⟩
  , ⟨``Nat.land, "natLand", [.nat, .nat], .nat⟩
  , ⟨``Nat.lor, "natLor", [.nat, .nat], .nat⟩
  , ⟨``Nat.log2, "natLog2", [.nat], .nat⟩
  , ⟨``Int.add, "intAdd", [.int, .int], .int⟩
  , ⟨``Int.sub, "intSub", [.int, .int], .int⟩
  , ⟨``Int.mul, "intMul", [.int, .int], .int⟩
  , ⟨``Int.toNat, "intToNat", [.int], .nat⟩
  , ⟨``Int.ofNat, "natToInt", [.nat], .int⟩
  , ⟨``Int.decEq, "intEq", [.int, .int], .bool⟩
  , ⟨``Int.instDecidableEq, "intEq", [.int, .int], .bool⟩
  , ⟨``Int.decLt, "intLt", [.int, .int], .bool⟩
  , ⟨``Int.decLe, "intLe", [.int, .int], .bool⟩
  , ⟨``String.length, "strLength", [.string], .nat⟩
  , ⟨``String.utf8ByteSize, "strUtf8ByteSize", [.string], .nat⟩
  , ⟨``String.append, "strAppend", [.string, .string], .string⟩
  , ⟨``String.Internal.append, "strAppend", [.string, .string], .string⟩
  , ⟨``String.push, "strPush", [.string, .char], .string⟩
  , ⟨``String.decEq, "strEq", [.string, .string], .bool⟩
  , ⟨``instDecidableEqString, "strEq", [.string, .string], .bool⟩
  -- a string position is the byte index it holds (`String.Pos.Raw` is a newtype over
  -- `Nat`), and `lean_string_decode_char` is the primitive that reads at one
  , ⟨``String.Pos.Raw.get, "strCharAt", [.string, .nat], .char⟩
  -- the primitive `String.startsWith` and the other pattern functions are built from:
  -- are the `len` bytes of one string from one position the `len` bytes of the other
  -- from its own?
  , ⟨``String.extract, "strExtract", [.string, .nat, .nat], .string⟩
  , ⟨``String.Pos.Raw.extract, "strExtract", [.string, .nat, .nat], .string⟩
  -- writing at a byte position, at a position held as the byte index it is
  , ⟨``String.Pos.Raw.set, "(prim3Op .lean_string_pos_raw_set)",
      [.string, .nat, .char], .string⟩
  , ⟨``String.Slice.Pattern.Internal.memcmpStr, "strMemcmp",
      [.string, .string, .nat, .nat, .nat], .bool⟩
  ]

/-- The nullary constructors the front end reads as literals. -/
def litOf? (n : Name) : Option (Src × STy) :=
  if n == ``Bool.true then some (.boolLit true, .bool)
  else if n == ``Bool.false then some (.boolLit false, .bool)
  -- a `Decidable` is the `Bool` it decides, and the proof each constructor carries is
  -- erased, so the constructor itself is that boolean
  else if n == ``Decidable.isTrue then some (.boolLit true, .bool)
  else if n == ``Decidable.isFalse then some (.boolLit false, .bool)
  else if n == ``Nat.zero then some (.natLit 0, .nat)
  else none

/-- The runtime function that reads a `Nat` as this scalar. -/
def SScalar.ofNatExtern : SScalar → Option String
  | .uint8 => some "lean_uint8_of_nat"
  | .uint16 => some "lean_uint16_of_nat"
  | .uint32 => some "lean_uint32_of_nat"
  | .uint64 => some "lean_uint64_of_nat"
  | .int8 => some "lean_int8_of_nat"
  | .int16 => some "lean_int16_of_nat"
  | .int32 => some "lean_int32_of_nat"
  | .int64 => some "lean_int64_of_nat"
  | .float | .float32 => none

/-- The runtime function that reads an `Int` as this scalar. -/
def SScalar.ofIntExtern : SScalar → Option String
  | .int8 => some "lean_int8_of_int"
  | .int16 => some "lean_int16_of_int"
  | .int32 => some "lean_int32_of_int"
  | .int64 => some "lean_int64_of_int"
  | _ => none

/-- The runtime function that reads this scalar as a `Nat`. -/
def SScalar.toNatExtern : SScalar → Option String
  | .uint8 => some "lean_uint8_to_nat"
  | .uint16 => some "lean_uint16_to_nat"
  | .uint32 => some "lean_uint32_to_nat"
  | .uint64 => some "lean_uint64_to_nat"
  | _ => none

/-- The runtime function that reads this scalar as an `Int`.  `Int64` is `ISize`, and the
    catalogue names that conversion after the latter. -/
def SScalar.toIntExtern : SScalar → Option String
  | .int8 => some "lean_int8_to_int"
  | .int16 => some "lean_int16_to_int"
  | .int32 => some "lean_int32_to_int"
  | .int64 => some "lean_isize_to_int"
  | _ => none

/-- A value of type `got`, as a value of type `want`.

    Lean's own types are wider than the machine types its runtime functions are typed at
    — `Float.scaleb` takes an `Int` in Lean and a machine integer in C — so a call of the
    runtime is read at the types the catalogue gives it, with the conversion the runtime
    itself provides in front of an argument that has the other one.  `none` says there is
    no such conversion, and the call is refused rather than written out ill-typed. -/
def coerceSrc (want got : STy) (e : Src) : Option Src :=
  if want == got then some e else
  let call (n : String) (a r : STy) : Src := .op ("(prim1Op ." ++ n ++ ")") [a] r [e]
  match want, got with
  | .scalar s, .nat => (s.ofNatExtern).map (call · .nat want)
  | .scalar s, .int => (s.ofIntExtern).map (call · .int want)
  | .nat, .scalar s => (s.toNatExtern).map (call · got .nat)
  | .int, .scalar s => (s.toIntExtern).map (call · got .int)
  -- a `Char` is its code point: `Char.mk` takes the `UInt32` it holds, and the runtime
  -- builds the character from the number
  | .char, .scalar .uint32 =>
      some (.op "(prim1Op .lean_char_of_nat_aux)" [.nat] .char
        [.op "(prim1Op .lean_uint32_to_nat)" [.scalar .uint32] .nat [e]])
  | .char, .nat => some (.op "(prim1Op .lean_char_of_nat_aux)" [.nat] .char [e])
  | .int, .nat => some (.op "natToInt" [.nat] .int [e])
  | .nat, .int => some (.op "intToNat" [.int] .nat [e])
  | _, _ => none

/-- The table entry of a Lean function, if the front end knows it. -/
def opOf? (n : Name) : Option OpInfo := opTable.find? (·.lean == n)

/-! ## Reading the compiled module -/

/-- The schema of a tagged union, as Lean source: the encoding names the first
    constructor that carries a field, so it is canonical.  `none` when no constructor
    carries one, or when there are fewer than two constructors — neither is a tagged
    union. -/
partial def taggedUnionSchemaSource (ctors : List (List String)) : Option String :=
  let listSrc (l : List String) : String := "[" ++ String.intercalate ", " l ++ "]"
  let rec payloadAfter : List (List String) → Option String
    | [] => none
    | c :: rest =>
        match c with
        | f :: fs =>
            some ("(.here ⟨" ++ f ++ ", " ++ listSrc fs ++ "⟩ " ++
              listSrc (rest.map listSrc) ++ ")")
        | [] => (payloadAfter rest).map fun s => "(.skip " ++ s ++ ")"
  match ctors with
  | c0 :: c1 :: rest =>
      match c0 with
      | f :: fs =>
          some ("(.payloadFirst ⟨" ++ f ++ ", " ++ listSrc fs ++ "⟩ " ++ listSrc c1 ++
            " " ++ listSrc (rest.map listSrc) ++ ")")
      | [] => (payloadAfter (c1 :: rest)).map fun s => "(.skip " ++ s ++ ")"
  | _ => none

/-- The type a value of `e` is at run time: a structure with exactly one field that
    survives erasure *is* that field, so the wrapper is peeled off, as many times as it is
    wrapped.  This is what makes a newtype over a recursive type — the `FixExpr` of
    `structure FixExpr where unFix : ExprF FixExpr` — the type it wraps. -/
partial def erasedTypeOf (e : Expr) (fuel : Nat := 8) : MetaM Expr := do
  if fuel == 0 then return e
  let fn := e.getAppFn
  let .const n us := fn | return e
  let some (.inductInfo iv) := (← getEnv).find? n | return e
  if iv.all.length != 1 || iv.ctors.length != 1 then return e
  let args := e.getAppArgs
  if args.size < iv.numParams then return e
  let cinfo ← getConstInfoCtor iv.ctors[0]!
  let cty ← instantiateTypeLevelParams cinfo.toConstantVal us
  let cty ← Meta.instantiateForall cty (args.extract 0 iv.numParams)
  let fields ← forallTelescope cty fun xs _ => do
    let mut fs : Array Expr := #[]
    for x in xs do
      let xty ← inferType x
      unless ← isProp xty do
        fs := fs.push xty
    return fs
  if fields.size == 1 && fields[0]! != e then erasedTypeOf fields[0]! (fuel - 1)
  else return e

mutual

/-- The `Ty` a Lean type denotes, if the front end can translate it.  `visiting` are the
    inductive types whose fields are being read, so that a type that mentions itself is
    refused rather than unfolded for ever. -/
partial def styOfAux (visiting : List Name) (e : Expr) : MetaM (Option STy) := do
  match e with
  | .const ``Nat _ => return some .nat
  | .const ``Bool _ => return some .bool
  | .const ``Int _ => return some .int
  | .const ``String _ => return some .string
  -- `Char` is a one-field structure over `UInt32`, but the runtime has a character of
  -- its own and the catalogue types its string primitives at it, so it is a leaf here
  | .const ``Char _ => return some .char
  | .const n _ =>
      -- a fixed-width scalar is a leaf of the type language too; anything else that is a
      -- bare constant is read as a user-defined type below
      match SScalar.ofLeanName? n with
      | some s => return some (.scalar s)
      | none => dataStyOf? visiting e
  | .forallE nm d b bi =>
      if ← isProp d then
        -- a proof carries nothing at run time, so a function that takes one takes one
        -- argument fewer
        Meta.withLocalDecl nm bi d fun x => styOfAux visiting (b.instantiate1 x)
      else if b.hasLooseBVars then
        -- the result may mention the argument only where nothing survives erasure — the
        -- predicate of a `Subtype`, say — so look at it with the argument as a local
        let some a ← styOfAux visiting d | return none
        Meta.withLocalDecl nm bi d fun x => do
          match ← styOfAux visiting (b.instantiate1 x) with
          | some r => return some (.fn a r)
          | none => return none
      else
        match ← styOfAux visiting d, ← styOfAux visiting b with
        | some a, some r => return some (.fn a r)
        | _, _ => return none
  -- the front end represents a `Decidable` by the `Bool` it decides, so a function that
  -- answers with one answers with a `Bool`
  | .app (.const ``Decidable _) _ => return some .bool
  | .app (.const ``Array _) a => return (← styOfAux visiting a).map STy.array
  | .app (.const ``Option _) a => return (← styOfAux visiting a).map STy.option
  | .app (.app (.const ``Prod _) a) b =>
      match ← styOfAux visiting a, ← styOfAux visiting b with
      | some x, some y => return some (.prod x y)
      | _, _ => return none
  | .mdata _ b => styOfAux visiting b
  | _ =>
      match ← dataStyOf? visiting e with
      | some t => return some t
      | none =>
        -- an abbreviation of a type — `DecidableEq α`, which is
        -- `(a b : α) → Decidable (a = b)` — is the type it unfolds to
        match ← unfoldDefinition? e with
        | some e' => if e' == e then return none else styOfAux visiting e'
        | none => return none

/-- The `Ty` a **user-defined** type denotes: a structure with one field is erased to that
    field, a structure with several fields is a record, field-less constructors make a
    boolean or an enum, and a sum in which some constructor carries a field is a tagged
    union — a *recursive* one when a field is an occurrence of the type itself.  A type
    the front end cannot place in one of those shapes is refused. -/
partial def dataStyOf? (visiting : List Name) (e : Expr) : MetaM (Option STy) := do
  let fn := e.getAppFn
  let .const n us := fn | return none
  if visiting.contains n then return none
  -- LCNF erases the arguments of a type it does not need at run time, and `Subtype
  -- lcErased` says nothing about what the value is; such a type is read off the Lean
  -- type of the declaration instead
  if e.getAppArgs.any (fun a => a.isConstOf ``lcErased || a.isConstOf ``lcAny) then
    return none
  let some (.inductInfo iv) := (← getEnv).find? n | return none
  -- a *nested* inductive (`structure FixExpr where unFix : ExprF FixExpr`) has no layout
  -- of its own, but a nested **newtype** is erased to the type of its one field, which may
  -- well have one
  if (iv.isNested && iv.ctors.length != 1) || iv.all.length != 1 then return none
  let args := e.getAppArgs
  if args.size < iv.numParams then return none
  let params := args.extract 0 iv.numParams
  let selfTy := mkAppN fn (params ++ args.extract iv.numParams args.size)
  let mut ctors : List (Name × List STy) := []
  for c in iv.ctors do
    let cinfo ← getConstInfoCtor c
    let cty ← instantiateTypeLevelParams cinfo.toConstantVal us
    let cty ← Meta.instantiateForall cty params
    let fields? ← forallTelescope cty fun xs _ => do
      let mut fields : List STy := []
      for x in xs do
        let xty ← inferType x
        if ← isProp xty then
          continue
        -- a field of the type being described is an occurrence of it — and so is a field
        -- of a newtype over it, since a newtype *is* the value it wraps
        if xty == selfTy || (← erasedTypeOf xty) == selfTy then
          fields := fields ++ [STy.selfRef]
          continue
        match ← styOfAux (n :: visiting) xty with
        | some t => fields := fields ++ [t]
        | none => return none
      return some fields
    let some fields := fields? | return none
    ctors := ctors ++ [(c, fields)]
  let recursive := ctors.any fun c => c.2.contains STy.selfRef
  -- a recursive type every constructor of which mentions the type itself has no values,
  -- so it is not a `Ty` at all
  if recursive && ctors.all (fun c => c.2.contains STy.selfRef) then return none
  let fieldsPretty (fs : List STy) : String := "(" ++ prettyTyList fs ++ ")"
  let unionPretty (cs : List (Name × List STy)) : String :=
    String.intercalate "|" (cs.map fun c => fieldsPretty c.2)
  match ctors with
  | [(_, [])] => return none            -- a unit type carries nothing
  | [(_, [t])] => return if recursive then none else some t  -- a newtype is its field
  | [(c, a :: b :: rest)] =>
      let fs := a :: b :: rest
      let src :=
        if recursive then
          "(Ty.recObject ⟨" ++ a.rsource ++ ", " ++ b.rsource ++ ", [" ++
            String.intercalate ", " (rest.map STy.rsource) ++ "]⟩)"
        else
          "(Ty.record ⟨" ++ a.source ++ ", " ++ b.source ++ ", [" ++
            String.intercalate ", " (rest.map STy.source) ++ "]⟩)"
      let rsrc :=
        "(RTy.record ⟨" ++ a.rsource ++ ", " ++ b.rsource ++ ", [" ++
          String.intercalate ", " (rest.map STy.rsource) ++ "]⟩)"
      let pp := (if recursive then "(recObject " else "(record ") ++ prettyTyList fs ++ ")"
      return some (.data src rsrc pp [(c, fs)])
  | _ =>
      if ctors.all (fun c => c.2.isEmpty) then
        -- only field-less constructors: a boolean or an enum
        if ctors.length == 2 then return some .bool
        let src := "(Ty.enum ⟨" ++ toString (ctors.length - 3) ++ ", 0⟩)"
        let rsrc := "(RTy.enum ⟨" ++ toString (ctors.length - 3) ++ ", 0⟩)"
        let pp := "(enum " ++ toString ctors.length ++ " 0)"
        return some (.data src rsrc pp ctors)
      -- a tagged union: the schema names the first constructor that carries a field
      let tys : List (List String) := ctors.map fun c => c.2.map STy.rsource
      let some schema := taggedUnionSchemaSource tys | return none
      let src :=
        if recursive then "(Ty.recTaggedUnion " ++ schema ++ ")"
        else
          let tysC : List (List String) := ctors.map fun c => c.2.map STy.source
          match taggedUnionSchemaSource tysC with
          | some s => "(Ty.taggedUnion " ++ s ++ ")"
          | none => ""
      if src.isEmpty then return none
      let rsrc := "(RTy." ++ (if recursive then "recTaggedUnion " else "taggedUnion ") ++
        schema ++ ")"
      let pp := (if recursive then "(recTaggedUnion " else "(taggedUnion ") ++
        unionPretty ctors ++ ")"
      return some (.data src rsrc pp ctors)

end

/-- The `Ty` a Lean type denotes, if the front end can translate it. -/
def styOf? (e : Expr) : MetaM (Option STy) := styOfAux [] e

/-- Why a Lean type is not one of the language, when there is something short to say about
    it: a type every constructor of which mentions the type itself has no values at all,
    and every type of the language has a canonical value (`LakeJs.RTyWf`), so it is not one
    of them.  The empty string when there is nothing to add. -/
def whyNotATy (e : Expr) : MetaM String := do
  let .const n _ := e.getAppFn | return ""
  let some (.inductInfo iv) := (← getEnv).find? n | return ""
  if iv.ctors.isEmpty then
    return s!" (`{n}` has no constructor, so it has no values)"
  let selfTy := e
  for c in iv.ctors do
    let cinfo ← getConstInfoCtor c
    let mentionsSelf ← forallTelescope cinfo.type fun xs _ => do
      for x in xs do
        let xty ← inferType x
        if xty == selfTy || (← erasedTypeOf xty) == selfTy then
          return true
      return false
    unless mentionsSelf do
      return ""
  return s!" (every constructor of `{n}` mentions `{n}`, so it has no values, and every \
type of the language has a canonical value)"

/-- The tag and the field types of a constructor of a type that has a layout. -/
def ctorOf? (ty : STy) (ctorName : Name) : Option (Nat × List STy) :=
  match ty with
  | .option a =>
      if ctorName == ``Option.none then some (0, [])
      else if ctorName == ``Option.some then some (1, [a])
      else none
  | .prod a b => if ctorName == ``Prod.mk then some (0, [a, b]) else none
  | .data src rsrc pp cs => do
      let i ← cs.findIdx? (·.1 == ctorName)
      let c ← (STy.data src rsrc pp cs).ctors[i]?
      return (i, c.2)
  | _ => none

/-- How many fields of an inductive type survive erasure: the ones that are neither
    proofs nor types. -/
def valueFieldCount (iv : InductiveVal) (ctor : Name) : MetaM Nat := do
  let cinfo ← getConstInfoCtor ctor
  forallTelescope cinfo.type fun xs _ => do
    let mut fields := 0
    for x in xs.extract iv.numParams xs.size do
      let xty ← inferType x
      if (← isProp xty) || (← Meta.isType x) then
        continue
      fields := fields + 1
    return fields

/-- Is `n` a **newtype**: a single-constructor type with exactly one field that survives
    erasure?  `Ty` erases such a wrapper to the type of its field (`structure Wrap where
    v : Nat` is `Ty.nat`), so building one and reading it back are both the identity —
    `String.Pos.Raw` and `Subtype` are the ones the snapshots use. -/
def isNewtype (n : Name) : MetaM Bool := do
  let some (.inductInfo iv) := (← getEnv).find? n | return false
  -- a *nested* one-field structure (`structure FixExpr where unFix : ExprF FixExpr`) is
  -- erased the same way: it is the value it wraps
  unless iv.ctors.length == 1 && iv.all.length == 1 do return false
  return (← valueFieldCount iv iv.ctors.head!) == 1

/-- Is `n` the constructor of a newtype? -/
def isNewtypeCtor (n : Name) : MetaM Bool := do
  let some (.ctorInfo ci) := (← getEnv).find? n | return false
  isNewtype ci.induct

/-- Is `n` the projection that reads the one field of a newtype — `String.Pos.Raw.byteIdx`
    of a `String.Pos.Raw`?  Such a projection is the identity, since the wrapper is
    erased. -/
def isNewtypeProjFn (n : Name) : MetaM Bool := do
  let some info := (← getEnv).getProjectionFnInfo? n | return false
  if info.i != 0 then return false
  isNewtypeCtor info.ctorName

/-- Where field `i` of the one constructor of the structure `tn` sits among the fields
    that survive erasure: a `Prop`-valued field carries nothing at run time, so it takes no
    slot.  `Std.Legacy.Range` keeps `start`, `stop` and `step` and drops `step_pos`. -/
def dataFieldIndex (tn : Name) (i : Nat) : MetaM Nat := do
  let some (.inductInfo iv) := (← getEnv).find? tn
    | throwError "`{tn}` is not an inductive type"
  let some ctor := iv.ctors.head?
    | throwError "`{tn}` has no constructor"
  let cinfo ← getConstInfoCtor ctor
  forallTelescope cinfo.type fun xs _ => do
    let fields := xs.extract iv.numParams xs.size
    let mut k := 0
    for j in [0:min i fields.size] do
      unless ← isProp (← inferType fields[j]!) do
        k := k + 1
    return k

/-- The field a projection function reads, as a slot of the value at run time — `none`
    when `c` is not such a projection, or when it reads the one field of a newtype, which
    is the identity. -/
def structProjField? (c : Name) : MetaM (Option Nat) := do
  let some info := (← getEnv).getProjectionFnInfo? c | return none
  if ← isNewtypeCtor info.ctorName then return none
  let some (.ctorInfo ci) := (← getEnv).find? info.ctorName | return none
  return some (← dataFieldIndex ci.induct info.i)

/-! ## Compiling a polymorphic declaration at the types it is called at

The type language is monomorphic.  A polymorphic declaration — `Array.back?`, a `cata` —
is therefore not compiled once and for all: it is compiled once per instantiation of its
type parameters that a caller uses, and the instantiation is read off the *call*, whose
LCNF types are concrete.  Everything below is that machinery: the substitution a
specialization runs under, the matching that recovers the instantiation from a call, and
the type the declaration has at it. -/

/-- Is this LCNF parameter or argument an erased one — a proof, or a type? -/
def isErasedTypeExpr (e : Expr) : Bool :=
  e.isConstOf ``lcErased || e.isConstOf ``lcAny

/-- Is this LCNF parameter a **type** parameter — the `α` of a polymorphic declaration? -/
def isTypeParam (p : Param) : Bool := p.type.isSort

/-- Substitute the type parameters of a specialization in a type read off its LCNF body:
    a type parameter is a free variable of the declaration, and it stands for the type the
    caller takes it at. -/
def substTypeParams (s : Std.HashMap Name Expr) (e : Expr) : Expr :=
  if s.isEmpty then e
  else e.replace fun x =>
    match x with
    | .fvar id => s[id.name]?
    | _ => none

/-- Instantiate the leading binders of a type with the given arguments. -/
def instForall : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: as => instForall (b.instantiate1 a) as
  | .mdata _ e, as => instForall e as
  | _, _ => none

/-- The result type of an LCNF declaration, written in its own parameters: the type with
    every parameter instantiated by the free variable that stands for it, so that a type
    parameter of it is a hole a call can fill. -/
def declResultPattern (d : Decl) (arity : Nat) : Option Expr :=
  instForall d.type ((d.params.toList.take arity).map (fun p => Expr.fvar p.fvarId))

/-- Match a type of the callee, whose type parameters are holes, against the concrete type
    the call has: first-order matching, which is all an instantiation of type parameters
    needs.  Returns the assignment extended by what this match determines. -/
partial def matchTypePattern (holes : Std.HashSet Name) (pat concrete : Expr)
    (assign : Std.HashMap Name Expr) : Option (Std.HashMap Name Expr) :=
  match pat, concrete with
  | .mdata _ p, c => matchTypePattern holes p c assign
  | p, .mdata _ c => matchTypePattern holes p c assign
  | .fvar id, c =>
      if holes.contains id.name then
        match assign[id.name]? with
        | some e => if e == c then some assign else none
        | none => some (assign.insert id.name c)
      else if Expr.fvar id == c then some assign else none
  | .app f a, .app f' a' => do
      let m ← matchTypePattern holes f f' assign
      matchTypePattern holes a a' m
  -- the callee's type is universe polymorphic and the call's is not: a type is the same
  -- type whatever universe it was read at
  | .const n _, .const n' _ => if n == n' then some assign else none
  | .sort _, .sort _ => some assign
  | p, c => if p == c then some assign else none

/-- The substitution a declaration is compiled under at `targs`: its type parameters, in
    order, mapped to the types the caller takes them at. -/
def typeSubstOf? (d : Decl) (targs : List Expr) : Option (Std.HashMap Name Expr) := do
  let tps := d.params.filter isTypeParam
  if tps.size != targs.length then none
  else
    let mut s : Std.HashMap Name Expr := {}
    for (p, t) in tps.toList.zip targs do
      s := s.insert p.fvarId.name t
    return s

/-- The name a declaration is written out under: its Lean name, and the types it is
    compiled at when it is a specialization of a polymorphic declaration. -/
def instSigName (inst : Inst) : MetaM String := do
  if inst.targs.isEmpty then return toString inst.name
  let mut s := toString inst.name
  for t in inst.targs do
    s := s ++ " @ " ++ toString (← ppExpr t)
  return s

/-- The parameters a declaration takes at run time, at the types it is compiled at: the
    ones that are neither a type parameter nor erased, with the type each of them has
    under the instantiation. -/
def instParamTys? (d : Decl) (tsub : Std.HashMap Name Expr) : MetaM (Option (List STy)) := do
  let mut ps : List STy := []
  for p in d.params do
    if isTypeParam p || isErasedTypeExpr p.type then
      continue
    let some t ← styOf? (substTypeParams tsub p.type) | return none
    ps := ps ++ [t]
  return some ps

/-- The type a declaration has at the types it is compiled at. -/
def instTypeOf? (inst : Inst) : MetaM (Option STy) := do
  let some d ← getBaseDecl? (LakeJs.Totality.resolveModel inst.name) | return none
  let some tsub := typeSubstOf? d inst.targs | return none
  let some ps ← instParamTys? d tsub | return none
  let some retE := declResultPattern d d.params.size | return none
  let some ret ← styOf? (substTypeParams tsub retE) | return none
  return some (STy.arrows ps ret)

/-- Everything a value of the translation knows about an LCNF free variable: the term it
    stands for, its type, and — when it is a `Nat` — its value as an offset from a
    variable, which is what decides *which* recursion a self call belongs to. -/
structure VInfo where
  /-- The term the variable stands for. -/
  src : Src
  /-- Its type. -/
  ty : STy
  /-- The Lean type LCNF gave it, when it is known: what a call of a polymorphic
      declaration is matched against to find the types it is called at. -/
  lty : Option Expr := none
  /-- `some (base, k)` when the value is `base + k` (a `Nat`), `some (none, k)` when it is
      the literal `k`. -/
  nf : Option (Option Name × Int) := none
  deriving Inhabited

/-- What the body translation needs to know about the function it is translating. -/
structure FnCtx where
  /-- The name of the function itself: a call of it is a self call. -/
  selfName : Name
  /-- The parameters of its recursion; empty when it is not recursive. -/
  recParams : Array (Name × STy)
  /-- The type it answers with. -/
  retTy : STy
  /-- The declarations of the module, which a call may name. -/
  moduleDecls : Array Name
  /-- When the function is a member of a **mutual clique** that is being translated as one
      ranked recursion: the members of the clique, in the order Lean records them.  A call
      of any of them is then a self call of that one recursion, tagged with the index of
      the member it enters. -/
  cliqueNames : Array Name := #[]
  /-- The parameters of every member of the clique, in the same order: the merged
      recursion takes the tag and then the parameters of every member, and a call fills
      the slots of the member it enters and leaves the others at their default. -/
  cliqueParams : Array (Array (Name × STy)) := #[]
  /-- When the members of the clique answer with **different** types: the union of those
      types, which is what the one merged recursion answers with.  A call of a member then
      reads its own summand out of the answer. -/
  cliqueUnion : Option STy := none
  /-- The result type of every member of the clique, in the same order. -/
  cliqueRetTys : Array STy := #[]
  /-- When the function being translated is a **specialization** of a polymorphic
      declaration: its type parameters, mapped to the types this specialization is
      compiled at.  Every type read off its LCNF body is instantiated by it. -/
  tsubst : Std.HashMap Name Expr := {}

/-- A type read off the LCNF body of the function being translated, at the types the
    function is compiled at. -/
def FnCtx.instTy (fn : FnCtx) (e : Expr) : Expr := substTypeParams fn.tsubst e

/-- The name the merged recursion of a mutual clique takes its tag under.  It is not a
    name any LCNF free variable can have, so it cannot be captured by a parameter. -/
def cliqueTagName : Name := `«clique tag»

/-- The name the summand of a member takes when it is read out of the answer of a merged
    clique.  It is bound and used at once, so it cannot capture anything. -/
def cliqueResultName : Name := `« clique result »

/-- Read the summand of member `j` out of the answer of a merged clique. -/
def unwrapCliqueResult (j : Nat) (rj : STy) (e : Src) : Src :=
  .caseS e [(j, [(cliqueResultName, rj)], .var cliqueResultName)] (some rj.dflt)

/-- The type a merged clique answers with when its members do **not** all answer with the
    same type: the tagged union with one constructor per member, carrying that member's
    result.  The clique is one recursion, so it has one result type; this is it. -/
def cliqueUnionTy (clique : Array Name) (rets : Array STy) : Option STy := do
  let schema ← taggedUnionSchemaSource (rets.toList.map (fun r => [r.source]))
  let rschema ← taggedUnionSchemaSource (rets.toList.map (fun r => [r.rsource]))
  let pp := "(taggedUnion " ++
    String.intercalate "|" (rets.toList.map (fun r => "(" ++ r.pretty ++ ")")) ++ ")"
  return STy.data ("(Ty.taggedUnion " ++ schema ++ ")") ("(RTy.taggedUnion " ++ rschema ++ ")")
    pp ((clique.toList.zip rets.toList).map (fun (n, r) => (n, [r])))

/-- The name a merged clique is declared under: `go & k (clique)`, from the names its
    members are written out under. -/
def cliqueSigNameOf (memberNames : List String) : String :=
  String.intercalate " & " memberNames ++ " (clique)"

/-- The value arguments of an LCNF application: the erased ones (proofs, types, instances
    with no run-time content) carry nothing and are dropped, as they are from the
    parameter list of the callee. -/
def valueArgs (args : Array Arg) : Array FVarId := Id.run do
  let mut out := #[]
  for a in args do
    match a with
    | .fvar f => out := out.push f
    | _ => pure ()
  return out

/-! ## Translating a body -/

/-- The values the LCNF free variables stand for. -/
abbrev VEnv := Std.HashMap Name VInfo

/-- The join points in scope, with their parameters and their bodies. -/
abbrev JEnv := Std.HashMap Name (Array Param × Code)

/-- What a free variable stands for, or an error naming it. -/
def lookupV (env : VEnv) (f : FVarId) : MetaM VInfo := do
  match env[f.name]? with
  | some v => return v
  | none =>
      throwError "the value of `{f.name}` is not available: it is erased, or it is bound \
        by a construct the front end does not translate"

/-- `a + k` as a normal form, when `a` has one. -/
def nfOffset (v : VInfo) (k : Int) : Option (Option Name × Int) :=
  v.nf.map fun (b, o) => (b, o + k)

/-- A self call: the one recursion of the declaration, applied to every argument.  There
    is nothing to classify — the evaluator recomputes the measure at the call and descends
    only when it is strictly smaller, so the front end has only to hand over the
    arguments. -/
def mkSelfCall (fn : FnCtx) (args : Array VInfo) : MetaM Src := do
  unless args.size == fn.recParams.size do
    throwError "a call of `{fn.selfName}` supplies {args.size} arguments, but the \
      recursion takes {fn.recParams.size}"
  return .selfCall (args.toList.map (·.src))


/-- The type of a declaration of the module, as Lean stored it, when it has one.  A
    compiler-generated specialization has no `ConstantInfo`: only LCNF knows it. -/
def typeOfDecl? (n : Name) : MetaM (Option Expr) := do
  return ((← getEnv).find? n).map ConstantInfo.type

/-- The type of a declaration of the module, as Lean stored it. -/
def typeOfDecl (n : Name) : MetaM Expr := do
  match ← typeOfDecl? n with
  | some t => return t
  | none => throwError "`{n}` has no declaration"

mutual

/-- The term an LCNF `let` value stands for. -/
partial def transLetValue (fn : FnCtx) (env : VEnv) (ty : Expr) (v : LetValue) :
    MetaM VInfo := do
  match v with
  | .lit (.nat n) => return { src := .natLit n, ty := .nat, nf := some (none, n) }
  | .lit (.str s) => return { src := .strLit s, ty := .string }
  | .lit (.uint32 v) =>
      -- a `Char` is a code point, which LCNF stores as a `UInt32` literal
      if (fn.instTy ty).isConstOf ``Char then
        return { src := .charLit (Char.ofNat v.toNat), ty := .char }
      else
        return { src := .scalarLit .uint32 v.toNat, ty := .scalar .uint32 }
  | .lit (.uint8 v) => return { src := .scalarLit .uint8 v.toNat, ty := .scalar .uint8 }
  | .lit (.uint16 v) => return { src := .scalarLit .uint16 v.toNat, ty := .scalar .uint16 }
  | .lit (.uint64 v) => return { src := .scalarLit .uint64 v.toNat, ty := .scalar .uint64 }
  -- a `USize` is the 64-bit unsigned scalar
  | .lit (.usize v) => return { src := .scalarLit .uint64 v.toNat, ty := .scalar .uint64 }
  | .erased => throwError "an erased value is used at run time"
  | .proj tn i x => do
      let v ← lookupV env x
      -- a newtype — a `Subtype`, which carries one value and one erased proof, or a
      -- one-field structure such as `String.Pos.Raw` — *is* its field at run time, so
      -- reading that field is the identity
      if i == 0 && (tn == ``Subtype || (← isNewtype tn)) then
        -- as above: reading the one field of a wrapper is the identity only when the
        -- language gives the wrapper that field's type
        if let some sty ← styOf? ty then
          unless sty == v.ty do
            throwOutsideLanguage m!"reading the field of `{tn}` converts a \
              `{v.ty.pretty}` into a `{sty.pretty}`, which the front end does not \
              translate"
        return v
      match v.ty.ctors with
      | [(0, fields)] =>
          let some fty := fields[i]?
            | throwError "a projection of field {i} of a value that has no such field"
          return { src := .projS v.src 0 i, ty := fty }
      | _ =>
          throwError "a projection of a value of a type that is not a one-constructor \
            type the front end translates"
  | .fvar f args =>
      let head ← lookupV env f
      if args.isEmpty then return head
      let mut acc := head.src
      let mut resTy := head.ty
      for a in valueArgs args do
        let av ← lookupV env a
        match resTy with
        | .fn _ r => acc := .ap acc av.src; resTy := r
        | _ => throwError "too many arguments applied to a value of a terminal type"
      return { src := acc, ty := resTy }
  | .const declName _ args =>
      let vargs ← (valueArgs args).mapM (lookupV env)
      -- building a newtype is the identity on its value, for the reason above
      if declName == ``Subtype.mk || (← isNewtypeCtor declName) then
        let some v := vargs[0]?
          | throwError "`{declName}` is applied to no value the front end can read"
        -- a newtype *is* its field, but only when the language gives the wrapper the very
        -- type of that field.  `Array.mk` wraps a list in an array, and the language has
        -- an array of its own, so that one is a conversion rather than a wrapper.
        if let some sty ← styOf? (fn.instTy ty) then
          unless sty == v.ty do
            -- the wrapper is a type of the language of its own — `Char`, which wraps the
            -- `UInt32` of its code point — so building it is the conversion the runtime
            -- has, when it has one
            let some e := coerceSrc sty v.ty v.src
              | throwOutsideLanguage m!"`{declName}` converts a value into a \
                  `{sty.pretty}`, which is a different type of the language from the \
                  `{v.ty.pretty}` it is applied to"
            return { src := e, ty := sty }
        return v
      if let some j := fn.cliqueNames.findIdx? (· == declName) then
        -- a call of any member of the clique is a call of the one merged recursion
        let ps := fn.cliqueParams[j]!
        unless vargs.size == ps.size do
          throwError "a call of `{declName}` supplies {vargs.size} arguments, but it \
            takes {ps.size}"
        let mut sargs : List Src := [Src.natLit j]
        for m in [0:fn.cliqueParams.size] do
          if m == j then
            sargs := sargs ++ vargs.toList.map (·.src)
          else
            sargs := sargs ++ fn.cliqueParams[m]!.toList.map (fun p => p.2.dflt)
        match fn.cliqueUnion with
        | none => return { src := .selfCall sargs, ty := fn.retTy }
        | some _ =>
            -- the merged recursion answers with the union of the members' result types;
            -- this call answers with the summand of the member it entered
            let some rj := fn.cliqueRetTys[j]?
              | throwError "the clique has no result type for `{declName}`"
            return { src := unwrapCliqueResult j rj (.selfCall sargs), ty := rj }
      if declName == fn.selfName then
        let src ← mkSelfCall fn vargs
        return { src := src, ty := fn.retTy }
      if declName == ``Nat.succ then
        -- the successor constructor is the runtime's `+ 1`: a `Nat` is the number it is
        let some a := vargs[0]? | throwError "`Nat.succ` is applied to no number"
        return { src := .op "natAdd" [.nat, .nat] .nat [a.src, .natLit 1], ty := .nat
                 nf := nfOffset a 1 }
      if let some (l, lty) := litOf? declName then
        unless vargs.isEmpty do
          throwError "`{declName}` is a constant, but it is applied to arguments"
        return { src := l, ty := lty
                 nf := if lty == .nat then some (none, 0) else none }
      if let some sty := ← styOf? ty then
        if let some (tag, fieldTys) := ctorOf? sty declName then
          unless vargs.size == fieldTys.length do
            throwError "`{declName}` is applied to {vargs.size} arguments, but the \
              constructor has {fieldTys.length} fields"
          return { src := .ctorS sty tag fieldTys (vargs.toList.map (·.src)), ty := sty }
      -- the operations on an array are polymorphic, so their types are read off the
      -- type of the array they are applied to rather than from the table.  A few of them
      -- (`Array.get!Internal`, say) take an `Inhabited` instance in front of the array,
      -- which survives erasure, so the arguments are counted from the array on.
      let aargs : Array VInfo :=
        match vargs.findIdx? (fun v => match v.ty with | .array _ => true | _ => false) with
        | some k => vargs.extract k vargs.size
        | none => vargs
      if declName == ``Array.size || declName == ``Array.usize then
        let some a := aargs[0]? | throwError "`{declName}` is applied to no array"
        let .array elem := a.ty
          | throwError "`{declName}` is applied to something that is not an array"
        return { src := .op "arrLen" [.array elem] .nat [a.src], ty := .nat }
      -- `Array.uget` and `Array.uset` index with a `USize`, which the language holds as
      -- the 64-bit scalar it is; the runtime's array primitives index with a `Nat`
      if declName == ``Array.uget || declName == ``Array.uset then
        let some arr := aargs[0]? | throwError "`{declName}` is applied to no array"
        let some i := aargs[1]? | throwError "`{declName}` is applied to no index"
        let .array elem := arr.ty
          | throwError "`{declName}` is applied to something that is not an array"
        let idx : Src :=
          .op "(prim1Op .lean_usize_to_nat)" [.scalar .uint64] .nat [i.src]
        if declName == ``Array.uget then
          return { src := .op "arrGet" [.array elem, .nat] elem [arr.src, idx], ty := elem }
        let some x := aargs[2]? | throwError "`{declName}` is applied to no element"
        return { src := .op "arrSet" [.array elem, .nat, elem] (.array elem)
                   [arr.src, idx, x.src]
                 ty := .array elem }
      if declName == ``Array.getInternal || declName == ``Array.getD
          || declName == ``Array.get!Internal
          || declName == `Array.get! || declName == `Array.get then
        let some arr := aargs[0]? | throwError "`{declName}` is applied to no array"
        let some i := aargs[1]? | throwError "`{declName}` is applied to no index"
        let .array elem := arr.ty
          | throwError "`{declName}` is applied to something that is not an array"
        return { src := .op "arrGet" [.array elem, .nat] elem [arr.src, i.src], ty := elem }
      if declName == ``Array.set || declName == ``Array.set!
          || declName == ``Array.setIfInBounds then
        let some arr := aargs[0]? | throwError "`{declName}` is applied to no array"
        let some i := aargs[1]? | throwError "`{declName}` is applied to no index"
        let some x := aargs[2]? | throwError "`{declName}` is applied to no element"
        let .array elem := arr.ty
          | throwError "`{declName}` is applied to something that is not an array"
        return { src := .op "arrSet" [.array elem, .nat, elem] (.array elem)
                   [arr.src, i.src, x.src]
                 ty := .array elem }
      if declName == ``Array.swap || declName == ``Array.swapIfInBounds then
        let some arr := aargs[0]? | throwError "`{declName}` is applied to no array"
        let some i := aargs[1]? | throwError "`{declName}` is applied to no index"
        let some j := aargs[2]? | throwError "`{declName}` is applied to no index"
        let .array elem := arr.ty
          | throwError "`{declName}` is applied to something that is not an array"
        return { src := .op "arrSwap" [.array elem, .nat, .nat] (.array elem)
                   [arr.src, i.src, j.src]
                 ty := .array elem }
      if declName == ``Array.pop then
        let some arr := aargs[0]? | throwError "`{declName}` is applied to no array"
        let .array elem := arr.ty
          | throwError "`{declName}` is applied to something that is not an array"
        return { src := .op "arrPop" [.array elem] (.array elem) [arr.src]
                 ty := .array elem }
      if declName == ``Array.replicate || declName == `Array.mkArray then
        let some n := vargs[0]? | throwError "`{declName}` is applied to no length"
        let some x := vargs[1]? | throwError "`{declName}` is applied to no element"
        let elem := x.ty
        return { src := .op "arrReplicate" [.nat, elem] (.array elem) [n.src, x.src]
                 ty := .array elem }
      if declName == ``Array.push then
        let some arr := aargs[0]? | throwError "`{declName}` is applied to no array"
        let some x := aargs[1]? | throwError "`{declName}` is applied to no element"
        let .array elem := arr.ty
          | throwError "`{declName}` is applied to something that is not an array"
        return { src := .op "arrPush" [.array elem, elem] (.array elem) [arr.src, x.src]
                 ty := .array elem }
      if declName == ``Array.mkEmpty || declName == ``Array.emptyWithCapacity then
        -- the empty array, at the element type the call is made at; the capacity the
        -- runtime is asked to reserve is the argument
        let some aty ← styOf? ty
          | throwError "`{declName}` builds an array of a type the front end does not \
              translate"
        let .array elem := aty
          | throwError "`{declName}` does not build an array"
        let cap := (vargs[0]?.map (·.src)).getD (Src.natLit 0)
        return { src := .op ("(arrEmpty (α := " ++ elem.source ++ "))") [.nat] aty [cap]
                 ty := aty }
      -- negation: the front end represents a `Decidable` by the `Bool` it decides, and
      -- the language has the conditional, so `not` is one
      if declName == ``Bool.not || declName == ``instDecidableNot then
        let some a := vargs[0]? | throwError "`{declName}` is applied to nothing"
        return { src := .ite a.src (.boolLit false) (.boolLit true), ty := .bool }
      if declName == ``Decidable.decide then
        -- the front end represents a `Decidable` by the `Bool` it decides, so `decide`
        -- is the identity on it
        let some a := vargs[0]?
          | throwError "`Decidable.decide` is applied to no decidable instance"
        return { src := a.src, ty := .bool }
      -- a declaration Lean implements with `@[extern]` is the function of the runtime
      -- that its C symbol names, whenever the catalogue has that symbol between types of
      -- the language
      let env ← getEnv
      let tableOp? : Option OpInfo :=
        match opOf? declName with
        | some op => some op
        | none =>
          match Lean.getExternNameFor env `c declName with
          | some cname =>
            (primExternOf? cname).map fun pe => ⟨declName, pe.helper, pe.argTys, pe.ret⟩
          | none => none
      match tableOp? with
      | some op =>
          if vargs.size > op.argTys.length then
            throwError "`{declName}` is applied to {vargs.size} arguments, but the \
              runtime function takes {op.argTys.length}"
          if vargs.size < op.argTys.length then
            -- a partial application — an equality instance handed to a container, say:
            -- the call of the runtime function is eta-expanded to the arguments it
            -- still expects
            let missing := (List.range (op.argTys.length - vargs.size)).map fun i =>
              Name.mkSimple s!"η{i}"
            let body := Src.op op.helper op.argTys op.ret
              (vargs.toList.map (·.src) ++ missing.map Src.var)
            return { src := missing.foldr (fun x acc => Src.lam x acc) body
                     ty := STy.arrows (op.argTys.drop vargs.size) op.ret }
          let mut argSrcs : List Src := []
          for i in [0:vargs.size] do
            let a := vargs[i]!
            let want := op.argTys[i]!
            let some e := coerceSrc want a.ty a.src
              | throwError "`{declName}` is given a `{a.ty.pretty}` where the runtime \
                  function takes a `{want.pretty}`, and the runtime has no conversion \
                  between them"
            argSrcs := argSrcs ++ [e]
          let src := Src.op op.helper op.argTys op.ret argSrcs
          let nf :=
            if declName == ``Nat.add then
              match vargs[1]!.nf with
              | some (none, k) => nfOffset vargs[0]! k
              | _ => none
            else if declName == ``Nat.sub then
              match vargs[1]!.nf with
              | some (none, k) => nfOffset vargs[0]! (-k)
              | _ => none
            else none
          return { src := src, ty := op.ret, nf := nf }
      | none =>
        -- an ordinary Lean function: a call of a declaration of the program, which the
        -- translation pulls in if it is not one already
        let hasBody ← do
          match ← getBaseDecl? (LakeJs.Totality.resolveModel declName) with
          | some d => match d.value with
              | .code _ => pure true
              | _ => pure false
          | none => pure false
        unless hasBody do
          -- `panicCore` is `default`: Lean defines it as the canonical value of its
          -- type, and prints a message on the way in the compiled program
          if declName == ``panicCore || declName == ``panic then
            let some sty ← styOf? (fn.instTy ty)
              | throwOutsideLanguage m!"`{declName}` answers at a type that is not one \
                  the front end translates"
            return { src := sty.dflt, ty := sty }
          -- a constructor of a type the front end has no layout for is not a program of
          -- the language at all
          if ((← getEnv).find? declName).any (· matches .ctorInfo _) then
            throwOutsideLanguage m!"`{declName}` builds a value of a type that is not one \
              the front end translates"
          throwError "`{declName}` has no Lean body the front end can read, and it is \
            not one of the runtime functions it knows"
        -- the type the call is checked against: the declaration's own, or — when that is
        -- an abbreviation the front end cannot read, such as `DecidableEq Char` — the one
        -- of the model whose body stands in for it
        let declTy? ← do
          match ← typeOfDecl? declName with
          | none =>
              -- a compiler-generated specialization of a library loop has no
              -- `ConstantInfo`; the type LCNF stored for it is already monomorphic
              instTypeOf? ⟨declName, []⟩
          | some te =>
            match ← styOf? te with
            | some t => pure (some t)
            | none =>
                let m := LakeJs.Totality.resolveModel declName
                if m == declName then pure none
                else match ← typeOfDecl? m with
                  | some tm => styOf? tm
                  | none => pure none
        -- a polymorphic declaration has no type of its own: it is compiled at the types
        -- this call takes it at, which are read off the concrete LCNF types of the call
        let (inst, declTy) ←
          match declTy? with
          | some t => pure (⟨declName, []⟩, t)
          | none => do
              let targs ← callTypeArgs fn declName ty args vargs
              let inst : Inst := ⟨declName, targs⟩
              let some t ← instTypeOf? inst
                | throwOutsideLanguage m!"the type of `{declName}` is not one the front \
                    end translates"
              pure (inst, t)
        let mut acc : Src := .glob (← instSigName inst) (some inst)
        let mut resTy := declTy
        for a in vargs do
          match resTy with
          | .fn _ r => acc := .ap acc a.src; resTy := r
          | _ => throwError "`{declName}` is applied to more arguments than it takes"
        return { src := acc, ty := resTy }

/-- The types a call takes a polymorphic declaration at.  The call's own LCNF types are
    concrete — the type of the value it binds, and the types of the arguments it supplies
    — so matching the callee's types, whose type parameters are holes, against them says
    what each type parameter stands for here. -/
partial def callTypeArgs (fn : FnCtx) (declName : Name) (ty : Expr) (args : Array Arg)
    (vargs : Array VInfo) : MetaM (List Expr) := do
  let src := LakeJs.Totality.resolveModel declName
  let some d ← getBaseDecl? src
    | throwError "`{declName}` has no LCNF body in the compiled module"
  let tps := d.params.filter isTypeParam
  if tps.isEmpty then
    throwError "the type of `{declName}` is not one the front end translates"
  let holes : Std.HashSet Name :=
    tps.foldl (fun s p => s.insert p.fvarId.name) {}
  let mut assign : Std.HashMap Name Expr := {}
  -- the type of the value the call binds, against the result type of the callee
  if let some pat := declResultPattern d args.size then
    if let some a := matchTypePattern holes pat (fn.instTy ty) assign then
      assign := a
  -- the type of every argument, against the type of the parameter it fills
  let valueParams := d.params.filter (fun p => !isTypeParam p && !isErasedTypeExpr p.type)
  for (p, v) in valueParams.toList.zip vargs.toList do
    if let some lty := v.lty then
      if let some a := matchTypePattern holes p.type lty assign then
        assign := a
  let mut targs : List Expr := []
  for p in tps do
    let some t := assign[p.fvarId.name]?
      | throwError "`{declName}` is polymorphic, and this call does not say what type \
          its parameter `{p.binderName}` is taken at"
    targs := targs ++ [t]
  return targs

/-- The term an LCNF code block stands for. -/
partial def transCode (fn : FnCtx) (env : VEnv) (jps : JEnv) (code : Code) : MetaM Src := do
  match code with
  | .let decl k =>
      if isErasedTypeExpr decl.type then
        -- nothing is bound: a use of it is an error, raised where it is used
        transCode fn env jps k
      else
        let dty := fn.instTy decl.type
        let v ← transLetValue fn env dty decl.value
        let name := decl.fvarId.name
        let body ← transCode fn
          (env.insert name { v with src := .var name, lty := some dty }) jps k
        return .letE name v.src body
  | .jp decl k =>
      transCode fn env (jps.insert decl.fvarId.name (decl.params, decl.value)) k
  | .jmp f args =>
      let some (ps, body) := jps[f.name]?
        | throwError "a jump to `{f.name}`, which is not a join point in scope"
      let vargs ← (valueArgs args).mapM (lookupV env)
      let mut env' := env
      let mut i := 0
      for p in ps do
        if isErasedTypeExpr p.type then
          continue
        let some a := vargs[i]? | throwError "a jump supplies too few arguments"
        env' := env'.insert p.fvarId.name a
        i := i + 1
      transCode fn env' jps body
  | .fun decl k =>
      -- a local function: LCNF keeps a recursion in the declaration itself or in a join
      -- point, so this is an ordinary abstraction, bound to a name of its own
      let mut ps : List (Name × STy) := []
      let mut fenv := env
      for p in decl.params do
        if isTypeParam p || isErasedTypeExpr p.type then
          continue
        let pty := fn.instTy p.type
        let some ty ← styOf? pty
          | throwOutsideLanguage m!"the parameter `{p.binderName}` of the local function \
              `{decl.binderName}` has type `{← ppExpr pty}`, which the front end does \
              not translate"
        ps := ps ++ [(p.fvarId.name, ty)]
        fenv := fenv.insert p.fvarId.name
          { src := .var p.fvarId.name, ty := ty, lty := some pty }
      -- LCNF records the **whole** type of a local function in `decl.type`, parameters
      -- and all; the type it answers with is what is left of it once the parameters are
      -- taken
      let retE := fn.instTy
        (← Meta.instantiateForall decl.type (decl.params.map (fun p => Expr.fvar p.fvarId)))
      let some retTy ← styOf? retE
        | throwOutsideLanguage m!"the local function `{decl.binderName}` answers with \
            `{← ppExpr retE}`, which the front end does not translate"
      if ps.isEmpty then
        throwError "the local function `{decl.binderName}` takes no argument that \
          survives erasure"
      let fbody ← transCode { fn with retTy := retTy } fenv jps decl.value
      let lam := ps.foldr (fun p acc => Src.lam p.1 acc) fbody
      let name := decl.fvarId.name
      let fnTy := STy.arrows (ps.map Prod.snd) retTy
      let rest ← transCode fn
        (env.insert name { src := .var name, ty := fnTy, lty := none }) jps k
      return .letE name lam rest
  | .return f => return (← lookupV env f).src
  | .unreach _ => return fn.retTy.dflt
  | .cases c =>
      let scrut ← lookupV env c.discr
      if c.typeName == ``Nat then
        let mut zero? : Option Src := none
        let mut succ? : Option Src := none
        for alt in c.alts do
          match alt with
          | .alt ctor ps body =>
              if ctor == ``Nat.zero then
                zero? := some (← transCode fn env jps body)
              else if ctor == ``Nat.succ then
                let some p := ps[0]? | throwError "`Nat.succ` alternative with no field"
                let pname := p.fvarId.name
                let pv : VInfo :=
                  { src := .op "natSub" [.nat, .nat] .nat [scrut.src, .natLit 1]
                    ty := .nat
                    nf := nfOffset scrut (-1) }
                succ? := some (← transCode fn (env.insert pname pv) jps body)
              else
                throwError "an unexpected constructor `{ctor}` of `Nat`"
          | .default body =>
              let d ← transCode fn env jps body
              if zero?.isNone then zero? := some d
              if succ?.isNone then succ? := some d
        let some z := zero? | throwError "a `Nat` dispatch with no zero branch"
        let some s := succ? | throwError "a `Nat` dispatch with no successor branch"
        return .ite (.op "natEq" [.nat, .nat] .bool [scrut.src, .natLit 0]) z s
      else if c.typeName == ``Int then
        -- an `Int` is `ofNat n` when it is not negative and `negSucc n` when it is, and
        -- the field each constructor binds is read back off the number itself
        let mut ofNat? : Option Src := none
        let mut negSucc? : Option Src := none
        for alt in c.alts do
          match alt with
          | .alt ctor ps body =>
              let fieldSrc : Src :=
                if ctor == ``Int.ofNat then
                  .op "intToNat" [.int] .nat [scrut.src]
                else
                  -- `negSucc n` is the number `-n - 1`, so `n` is `-i - 1`
                  .op "intToNat" [.int] .nat
                    [.op "intSub" [.int, .int] .int
                      [.op "intSub" [.int, .int] .int [.intLit 0, scrut.src], .intLit 1]]
              let mut env' := env
              if let some p := ps[0]? then
                env' := env'.insert p.fvarId.name { src := fieldSrc, ty := .nat }
              let b ← transCode fn env' jps body
              if ctor == ``Int.ofNat then ofNat? := some b
              else if ctor == ``Int.negSucc then negSucc? := some b
              else throwError "an unexpected constructor `{ctor}` of `Int`"
          | .default body =>
              let d ← transCode fn env jps body
              if ofNat?.isNone then ofNat? := some d
              if negSucc?.isNone then negSucc? := some d
        let some nonNeg := ofNat? | throwError "an `Int` dispatch with no `ofNat` branch"
        let some neg := negSucc? | throwError "an `Int` dispatch with no `negSucc` branch"
        return .ite (.op "intLe" [.int, .int] .bool [.intLit 0, scrut.src]) nonNeg neg
      else if ← isNewtype c.typeName then
        -- a newtype *is* the value it wraps, so matching on it binds that value: there is
        -- one constructor, one field, and the field is the scrutinee itself
        let mut body? : Option Src := none
        for alt in c.alts do
          match alt with
          | .alt _ ps b =>
              let mut env' := env
              for p in ps do
                unless isErasedTypeExpr p.type do
                  env' := env'.insert p.fvarId.name scrut
              body? := some (← transCode fn env' jps b)
          | .default b => if body?.isNone then body? := some (← transCode fn env jps b)
        let some body := body?
          | throwError "a dispatch on the newtype `{c.typeName}` with no branch"
        return body
      else if scrut.ty == .bool then
        -- the boolean, and every other two-constructor type with no fields: the first
        -- constructor is `false` and the second is `true`, which is what their tags are
        let mut tt? : Option Src := none
        let mut ff? : Option Src := none
        for alt in c.alts do
          match alt with
          | .alt ctor _ body =>
              let cinfo ← getConstInfoCtor ctor
              let b ← transCode fn env jps body
              if cinfo.cidx == 1 then tt? := some b
              else if cinfo.cidx == 0 then ff? := some b
              else throwError "an unexpected constructor `{ctor}` of a two-valued type"
          | .default body =>
              let d ← transCode fn env jps body
              if tt?.isNone then tt? := some d
              if ff?.isNone then ff? := some d
        let some t := tt? | throwError "a `Bool` dispatch with no `true` branch"
        let some f := ff? | throwError "a `Bool` dispatch with no `false` branch"
        return .ite scrut.src t f
      else if scrut.ty.ctors.isEmpty then
        throwError "a dispatch on `{c.typeName}` is not translated yet: the front end \
          handles `Nat`, `Bool`, `Decidable`, `Option` and product scrutinees"
      else
        -- a dispatch on a type that has a layout: one branch per constructor, each
        -- binding the fields of the constructor it matches
        let mut alts : List (Nat × List (Name × STy) × Src) := []
        let mut deflt : Option Src := none
        for alt in c.alts do
          match alt with
          | .alt ctor ps body =>
              let some (tag, fieldTys) := ctorOf? scrut.ty ctor
                | throwError "`{ctor}` is not a constructor of the type the front end \
                    gave the scrutinee"
              let mut fields : List (Name × STy) := []
              let mut env' := env
              let mut i := 0
              for fty in fieldTys do
                let some p := ps[i]?
                  | throwError "the alternative for `{ctor}` binds too few fields"
                let pname := p.fvarId.name
                fields := fields ++ [(pname, fty)]
                env' := env'.insert pname { src := .var pname, ty := fty }
                i := i + 1
              alts := alts ++ [(tag, fields, ← transCode fn env' jps body)]
          | .default body => deflt := some (← transCode fn env jps body)
        -- a dispatch with a branch for every constructor needs no default branch
        let full := alts.length == scrut.ty.ctors.length
        return .caseS scrut.src alts (if full then none else deflt)

end

/-! ## The termination measure -/

/-- The measure function Lean stored: the `h` of `WellFounded.Nat.fix h _ _`, or the `f`
    of `invImage f inst`, with the relation instance in the second case. -/
partial def findMeasure? (e : Expr) : Option (Expr × Option Expr) :=
  if e.isAppOf ``WellFounded.Nat.fix && e.getAppNumArgs ≥ 4 then
    some (e.getArg! 2, none)
  else if e.isAppOf ``invImage && e.getAppNumArgs ≥ 4 then
    some (e.getArg! 2, some (e.getArg! 3))
  else
    match e with
    | .app f a => (findMeasure? f).orElse fun _ => findMeasure? a
    | .lam _ _ b _ | .forallE _ _ b _ => findMeasure? b
    | .letE _ _ v b _ => (findMeasure? v).orElse fun _ => findMeasure? b
    | .mdata _ b => findMeasure? b
    | .proj _ _ b => findMeasure? b
    | _ => none

/-- Open the measure function: Lean packs the arguments of a recursive function into a
    `PSigma`, and the measure destructures it, so its real binders are the ones under the
    `PSigma.casesOn`. -/
partial def peelMeasure {α : Type} (f : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  go #[] f
where
  /-- `acc` are the binders already recognised as parameters; `f` is what is left. -/
  go (acc : Array Expr) (f : Expr) : MetaM α :=
    lambdaTelescope f fun xs body => do
      if body.isAppOf ``PSigma.casesOn && xs.size ≥ 1 then
        let args := body.getAppArgs
        if args.size ≥ 2 && args[args.size - 2]! == xs[xs.size - 1]! then
          -- the last binder is the packed pair this `casesOn` takes apart, so it is not
          -- a parameter; the ones before it are
          return ← go (acc ++ xs.pop) args[args.size - 1]!
      k (acc ++ xs) body

/-- The components of a lexicographic measure, outermost first. -/
partial def measureParts (e : Expr) : List Expr :=
  if e.isAppOf ``Prod.mk && e.getAppNumArgs == 4 then
    e.getArg! 2 :: measureParts (e.getArg! 3)
  else
    [e]

/-- Transcribe one component of a `termination_by` measure as a term of the parameters. -/
partial def transMeasure (names : Std.HashMap Name (Name × STy)) (e : Expr) :
    MetaM Src := do
  match e with
  | .fvar f =>
      match names[f.name]? with
      | some (n, _) => return .var n
      | none => throwError "the measure mentions a variable that is not a parameter"
  | .lit (.natVal n) => return .natLit n
  | .mdata _ b => transMeasure names b
  | .proj tn i x => do
      if i == 0 && (tn == ``Subtype || (← isNewtype tn)) then
        transMeasure names x
      else
        return .projS (← transMeasure names x) 0 (← dataFieldIndex tn i)
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const c _ =>
        if c == ``OfNat.ofNat && args.size ≥ 2 then
          match args[1]! with
          | .lit (.natVal n) => return .natLit n
          | _ => throwError "a numeral the front end cannot read in a measure"
        else if c == ``HAdd.hAdd && args.size == 6 then
          return .op "natAdd" [.nat, .nat] .nat
            [← transMeasure names args[4]!, ← transMeasure names args[5]!]
        else if c == ``HSub.hSub && args.size == 6 then
          return .op "natSub" [.nat, .nat] .nat
            [← transMeasure names args[4]!, ← transMeasure names args[5]!]
        else if c == ``HMul.hMul && args.size == 6 then
          return .op "natMul" [.nat, .nat] .nat
            [← transMeasure names args[4]!, ← transMeasure names args[5]!]
        else if (c == ``Array.size || c == ``Array.usize) && args.size ≥ 2 then
          -- the size of an array: the type of its elements is read off the parameter
          match args[1]! with
          | .fvar f =>
              match names[f.name]? with
              | some (n, .array elem) =>
                  return .op "arrLen" [.array elem] .nat [.var n]
              | _ => throwError "the measure takes the size of something that is not a \
                  parameter of an array type"
          | _ => throwError "the measure takes the size of an expression the front end \
              cannot transcribe"
        else if let some fld ← structProjField? c then
          -- a field of a structure the measure reads: `range.stop` of a `Std.Legacy.Range`
          match ← transMeasure names args[args.size - 1]! with
          | e => return .projS e 0 fld
        else if (← isNewtypeProjFn c) && args.size ≥ 1 then
          -- reading the one field of a newtype is the identity: the wrapper is erased,
          -- so `p.byteIdx` of a `String.Pos.Raw` *is* `p`
          transMeasure names args[args.size - 1]!
        else
          match opOf? c with
          | some op =>
              let vargs := args.extract (args.size - op.argTys.length) args.size
              return .op op.helper op.argTys op.ret (← vargs.toList.mapM (transMeasure names))
          | none =>
              throwError "the measure mentions `{c}`, which the front end cannot \
                transcribe into a rank"
    | _ => throwError "a measure the front end cannot transcribe into a rank"

/-- Match the binders a measure is written against with the parameters that survive
    erasure.  `vars` is the fixed prefix of the recursion — the parameters it never
    changes, such as a value the function captured — followed by the binders of the
    measure itself, so it lines up with the parameter list in order. -/
def mkMeasureNames (n : Name) (params : Array (Name × STy)) (binderNames : Array Name)
    (vars : Array Expr) : MetaM (Std.HashMap Name (Name × STy)) := do
  let mut dataVars : Array Expr := #[]
  for x in vars do
    let xty ← inferType x
    -- a proof and a type parameter carry nothing at run time: the measure is written
    -- against the parameters that survive erasure
    unless (← isProp xty) || xty.isSort do
      dataVars := dataVars.push x
  -- Lean writes the measure against the binders of the *packed* function, whose fixed
  -- prefix — the parameters the recursion never changes — comes first, whatever position
  -- those parameters have in the function itself.  So the binders are matched with the
  -- parameters by the name each was written under, and only by position when the names do
  -- not pair them up one to one.
  let userNames ← dataVars.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes
  let binders := binderNames.map Name.eraseMacroScopes
  let mut names : Std.HashMap Name (Name × STy) := {}
  if dataVars.size == params.size then
    let byName :=
      userNames.all (fun u => (binders.filter (· == u)).size == 1) &&
      binders.all (fun b => (userNames.filter (· == b)).size == 1)
    for i in [0:params.size] do
      let k := if byName then (binders.idxOf? userNames[i]!).getD i else i
      let some p := params[k]? | throwError "the measure of `{n}` mentions a parameter \
        the compiled function does not have"
      names := names.insert dataVars[i]!.fvarId!.name p
    return names
  -- A compiler-generated specialization does not take the same parameters as the
  -- declaration it was specialized from: what the caller fixed — a monad instance, the
  -- loop body — is gone, and what the caller captured is added in front.  There is no
  -- position to go by, so the binders of the measure are matched with the parameters by
  -- name alone; a binder that pairs with none of them is simply not available to the
  -- measure, and `transMeasure` refuses a measure that does mention it.
  for i in [0:dataVars.size] do
    let u := userNames[i]!
    if (binders.filter (· == u)).size == 1 then
      if let some k := binders.idxOf? u then
        if let some p := params[k]? then
          names := names.insert dataVars[i]!.fvarId!.name p
  return names

/-! ## Translating a declaration -/

/-- One translated declaration. -/
structure TransDecl where
  /-- The Lean name it came from. -/
  name : Name
  /-- The name it is declared under in the signature. -/
  sigName : String
  /-- Its type. -/
  ty : STy
  /-- Its body. -/
  term : Src
  /-- Is it a public entry point of the module (🎯) rather than a declaration the
      translation pulled in (📦)? -/
  target : Bool
  /-- When it is recursive: where the measure of its recursion came from, and what it is,
      in the notation the tree below it is printed in.  The generated program records this
      so that the one thing the front end has to get right is on the page. -/
  measureNote : Option String := none
  deriving Inhabited

/-- The Lean declarations a term calls, each at the types it calls it at. -/
partial def Src.globalDecls : Src → List Inst
  | .ctorS _ _ _ args => args.flatMap Src.globalDecls
  | .projS e _ _ => e.globalDecls
  | .caseS s alts d =>
      s.globalDecls ++ alts.flatMap (fun a => a.2.2.globalDecls) ++
        (d.map Src.globalDecls).getD []
  | .glob _ d => d.toList
  | .ap f a => f.globalDecls ++ a.globalDecls
  | .lam _ b => b.globalDecls
  | .letE _ v b => v.globalDecls ++ b.globalDecls
  | .ite c t e => c.globalDecls ++ t.globalDecls ++ e.globalDecls
  | .op _ _ _ args => args.flatMap Src.globalDecls
  | .structSize e => e.globalDecls
  | .selfCall args => args.flatMap Src.globalDecls
  | .fix _ ms b e => ms.flatMap Src.globalDecls ++ b.globalDecls ++ e.globalDecls
  | _ => []

/-- The declarations of the module a term calls. -/
partial def Src.globals : Src → List String
  | .ctorS _ _ _ args => args.flatMap Src.globals
  | .projS e _ _ => e.globals
  | .caseS s alts d =>
      s.globals ++ alts.flatMap (fun a => a.2.2.globals) ++ (d.map Src.globals).getD []
  | .glob n _ => [n]
  | .ap f a => f.globals ++ a.globals
  | .lam _ b => b.globals
  | .letE _ v b => v.globals ++ b.globals
  | .ite c t e => c.globals ++ t.globals ++ e.globals
  | .op _ _ _ args => args.flatMap Src.globals
  | .structSize e => e.globals
  | .selfCall args => args.flatMap Src.globals
  | .fix _ ms b e => ms.flatMap Src.globals ++ b.globals ++ e.globals
  | _ => []

/-- Peel `n` arrows off a type. -/
private def dropArrows : Nat → Expr → Option Expr
  | 0, e => some e
  | n + 1, .forallE _ _ b _ => dropArrows n b
  | _, _ => none

/-- Translate one declaration of the module into a term of the grammar.  `inst` is the
    declaration together with the types it is compiled at: for a polymorphic declaration
    there is one translation per instantiation its callers use, and the type parameters
    stand for those types throughout its body. -/
def translateDecl (moduleDecls : Array Name) (target : Bool) (inst : Inst) :
    MetaM TransDecl := do
  let env ← getEnv
  let n := inst.name
  -- a core function Lean implements in C is compiled from its Lean-source model
  -- (`LakeJs.CoreModels`); everything below reads the model, and only the *name* the
  -- declaration is written out under stays the one the program calls
  let src := LakeJs.Totality.resolveModel n
  let some d ← getBaseDecl? src
    | throwError "`{n}` has no LCNF body in the compiled module"
  let .code body := d.value
    | throwError "`{n}` is implemented by `@[extern]`, so there is no body to translate"
  -- the types this translation takes the type parameters at
  let some tsub := typeSubstOf? d inst.targs
    | if inst.targs.isEmpty then
        throwOutsideLanguage m!"`{n}` is polymorphic, and the type language is monomorphic: \
          it is compiled once per instantiation a caller uses, and this module has no \
          call of it the front end could read one off"
      else
        throwError "`{n}` takes a different number of type parameters than the call that \
          pulled it in supplies"
  -- the parameters, and the type each of them is taken at
  let mut params : Array (Name × STy) := #[]
  -- where each of them sits among *all* the parameters, which is what the position of a
  -- structural recursion counts
  let mut paramSourceIdx : Array Nat := #[]
  -- the name each of them was written under, which is how the binders of a
  -- `termination_by` measure are matched with them
  let mut paramBinderNames : Array Name := #[]
  let mut paramPos := 0
  for p in d.params do
    let here := paramPos
    paramPos := paramPos + 1
    if isTypeParam p || isErasedTypeExpr p.type then
      continue
    let some ty := ← styOf? (substTypeParams tsub p.type)
      | throwOutsideLanguage m!"the parameter `{p.binderName}` of `{n}` has type \
          `{← ppExpr (substTypeParams tsub p.type)}`, which the front end does not \
          translate{← whyNotATy (substTypeParams tsub p.type)}"
    params := params.push (p.fvarId.name, ty)
    paramBinderNames := paramBinderNames.push p.binderName
    paramSourceIdx := paramSourceIdx.push here
  let some retExpr :=
      (if inst.targs.isEmpty then dropArrows d.params.size d.type
       else declResultPattern d d.params.size).map (substTypeParams tsub)
    | throwError "the type of `{n}` is not an arrow of its parameters"
  -- when LCNF erased what the result type is made of — `Subtype lcErased` — the Lean type
  -- of the declaration still says it
  let retTy? ← do
    match ← styOf? retExpr with
    | some t => pure (some t)
    | none =>
        if !inst.targs.isEmpty then pure none else
        match ← typeOfDecl? src with
        | none => pure none
        | some srcTy =>
          Meta.forallBoundedTelescope srcTy (some d.params.size) fun xs body =>
            if xs.size == d.params.size then styOf? body else pure none
  let some retTy := retTy?
    | throwOutsideLanguage m!"the result type of `{n}`, `{← ppExpr retExpr}`, is not one \
        the front end translates"
  -- how Lean elaborated the recursion — for a compiler-generated specialization, what
  -- Lean recorded for the declaration it was specialized from
  let recSrc := LakeJs.Totality.recInfoSource env src
  -- the components of the measure of its recursion, outermost first, and where they came
  -- from; empty when it is not recursive at all
  let measureInfo : Array Src × String ←
    match LakeJs.Totality.recKind? env recSrc with
    | .error msg => throwError msg
    | .ok .nonRecursive => pure (#[], "")
    | .ok (.structural recArgPos clique) => do
        unless clique.size == 1 do
          throwError "`{n}` is part of a mutual clique of {clique.size} functions; the \
            front end translates one function at a time so far"
        -- the position counts the parameters of the declaration the recursion was
        -- *recorded* for.  A compiler-generated specialization does not take the same
        -- parameters as the declaration it was specialized from, so there the argument is
        -- found by the name it was written under instead.
        let byPos := (paramSourceIdx.idxOf? recArgPos).bind (params[·]?)
        -- LCNF renumbers the names it generates itself (`x.2` of the origin is `x.3` of
        -- the specialization), so the name is tried first and the *position counted from
        -- the last parameter* second: a specialization adds what the caller captured in
        -- front and drops what the caller fixed, and the loop's own state stays at the
        -- end, in the order it had.
        let (byName, byEnd) ← do
          if recSrc == src then pure (none, none)
          else match ← getBaseDecl? recSrc with
            | some od =>
                let byName := match od.params[recArgPos]? with
                  | some op => (paramBinderNames.idxOf? op.binderName).bind (params[·]?)
                  | none => none
                let byEnd :=
                  if recArgPos < od.params.size then
                    let fromEnd := od.params.size - recArgPos
                    if fromEnd ≤ d.params.size then
                      (paramSourceIdx.idxOf? (d.params.size - fromEnd)).bind (params[·]?)
                    else none
                  else none
                pure (byName, byEnd)
            | none => pure (none, none)
        let some (pname, pty) :=
          (if recSrc == src then byPos else byName <|> byEnd <|> byPos)
          | throwError "the recursion of `{n}` is on argument {recArgPos}, which is not \
              one of the parameters that survive erasure"
        let measure : Src := if pty == .nat then .var pname else .structSize (.var pname)
        pure (#[measure],
          "structural recursion, on the argument Lean recorded (position " ++
            toString recArgPos ++ ")")
    | .ok (.wellFounded clique) => do
        unless clique.size == 1 do
          throwError "`{n}` is part of a mutual clique of {clique.size} functions; the \
            front end translates one function at a time so far"
        let some info := Lean.Elab.WF.eqnInfoExt.find? env recSrc
          | throwError "`{n}` is well-founded recursive but Lean stored no measure"
        let some packed := (env.find? info.declNameNonRec).bind ConstantInfo.value?
          | throwError "the packed declaration `{info.declNameNonRec}` has no value"
        let comps ← lambdaTelescope packed fun pre packedBody => do
         -- the binders Lean put in front of the recursion are its fixed prefix
         let some (measureFn, inst?) := findMeasure? packedBody
           | throwError "no termination measure was found in `{info.declNameNonRec}`"
         peelMeasure measureFn fun xs mbody => do
          -- the binders of the measure are the *source* parameters, proofs included
          let names ← mkMeasureNames n params paramBinderNames (pre ++ xs)
          let parts ←
            match inst? with
            | none => pure [mbody]
            | some inst =>
                if inst.isAppOf ``Prod.instWellFoundedRelation then
                  pure (measureParts mbody)
                else if inst.isAppOf ``PSigma.instWellFoundedRelation then
                  throwError "the measure of `{n}` is ordered by a dependent \
                    lexicographic relation, which the front end does not split yet"
                else
                  pure [mbody]
          parts.mapM (transMeasure names)
        -- the components are transcribed verbatim, in the order `termination_by` gives
        -- them: the recursion compares them lexicographically, so nothing has to be said
        -- about which parameter belongs to which of them
        pure (comps.toArray, "well-founded recursion, `termination_by` transcribed verbatim")
  let measures := measureInfo.1
  let measureFrom := measureInfo.2
  -- the body, in a context where every parameter stands for itself
  let mut venv : VEnv := {}
  let ltyOf : Std.HashMap Name Expr :=
    d.params.foldl (fun m p => m.insert p.fvarId.name (substTypeParams tsub p.type)) {}
  for (pname, pty) in params do
    venv := venv.insert pname
      { src := .var pname, ty := pty, lty := ltyOf[pname]?
        nf := some (some pname, 0) }
  let fctx : FnCtx :=
    { selfName := src, recParams := if measures.isEmpty then #[] else params
      retTy := retTy, moduleDecls := moduleDecls, tsubst := tsub }
  let inner ← transCode fctx venv {} body
  -- wrap it: the one recursion of the declaration, or plain abstractions when it has none
  let declTy := STy.arrows (params.toList.map Prod.snd) retTy
  let term : Src :=
    if measures.isEmpty then
      params.foldr (fun p acc => Src.lam p.1 acc) inner
    else
      .fix params.toList measures.toList inner retTy.dflt
  let note : Option String :=
    if measures.isEmpty then none
    else
      let ctx : RCtx := { vars := params.toList.map Prod.fst }
      some (measureFrom ++ "; " ++ toString measures.size ++
        (if measures.size == 1 then " component: [ " else " components: [ ") ++
        String.intercalate ", " (measures.toList.map (fun m => m.toPretty ctx 0)) ++ " ]")
  return { name := n, sigName := ← instSigName inst, ty := declTy, term := term
           target := target, measureNote := note }

/-! ## A mutual clique, as one ranked recursion -/

/-- The branches of the measure of a mutual clique.  Lean packs the arguments of a clique
    into a `PSum` of one summand per member and gives the clique one measure of that sum,
    `fun x => PSum.casesOn x f₀ f₁`; the leaves of that tree are the measures of the
    members, in the order Lean lists them. -/
partial def measureBranches (e : Expr) : MetaM (List Expr) := do
  lambdaTelescope e fun xs body => do
    if xs.size == 1 && body.isAppOf ``PSum.casesOn then
      let args := body.getAppArgs
      if args.size ≥ 6 then
        let inl := args[args.size - 2]!
        let inr := args[args.size - 1]!
        return (← measureBranches inl) ++ (← measureBranches inr)
    return [e]

/-- The measure of every member of a mutual clique: the argument a structural recursion
    descends on, or the `termination_by` measure of that member. -/
def cliqueMeasures (clique : Array Name) (memberParams : Array (Array (Name × STy)))
    (memberSourceIdx : Array (Array Nat)) (memberBinderNames : Array (Array Name)) :
    MetaM (Array Src) := do
  let env ← getEnv
  match LakeJs.Totality.recKind? env clique[0]! with
  | .error msg => throwError msg
  | .ok .nonRecursive =>
      throwError "`{clique[0]!}` is in a mutual clique but Lean recorded no recursion"
  | .ok (.structural ..) => do
      let mut out : Array Src := #[]
      for i in [0:clique.size] do
        let n := clique[i]!
        match LakeJs.Totality.recKind? env n with
        | .ok (.structural recArgPos _) =>
            -- `recArgPos` counts *all* the parameters, the erased ones included
            let some k := memberSourceIdx[i]!.idxOf? recArgPos
              | throwError "the recursion of `{n}` is on argument {recArgPos}, which is \
                  not one of the parameters that survive erasure"
            let some (pname, pty) := memberParams[i]![k]?
              | throwError "the recursion of `{n}` is on argument {recArgPos}, which is \
                  not one of the parameters that survive erasure"
            let m : Src := if pty == .nat then .var pname else .structSize (.var pname)
            out := out.push m
        | _ =>
            throwError "`{n}` is in a structural clique, but Lean recorded no structural \
              recursion for it"
      return out
  | .ok (.wellFounded _) => do
      let some info := Lean.Elab.WF.eqnInfoExt.find? env clique[0]!
        | throwError "`{clique[0]!}` is well-founded recursive but Lean stored no measure"
      let some packed := (env.find? info.declNameNonRec).bind ConstantInfo.value?
        | throwError "the packed declaration `{info.declNameNonRec}` has no value"
      lambdaTelescope packed fun pre packedBody => do
        let some (measureFn, _) := findMeasure? packedBody
          | throwError "no termination measure was found in `{info.declNameNonRec}`"
        let leaves ← measureBranches measureFn
        unless leaves.length == clique.size do
          throwError "the measure of the clique has {leaves.length} branches, but the \
            clique has {clique.size} members"
        let mut out : Array Src := #[]
        for i in [0:clique.size] do
          let n := clique[i]!
          let params := memberParams[i]!
          out := out.push (← peelMeasure leaves[i]! fun xs mbody => do
            transMeasure (← mkMeasureNames n params memberBinderNames[i]! (pre ++ xs)) mbody)
        return out

/-- A dispatch on the tag of the merged recursion: branch `i` is what member `i` does. -/
def tagDispatch (alts : Array Src) : Src := Id.run do
  let mut acc := alts[alts.size - 1]!
  let mut i := alts.size - 1
  while i > 0 do
    i := i - 1
    acc := .ite (.op "natEq" [.nat, .nat] .bool [.var cliqueTagName, .natLit i])
      alts[i]! acc
  return acc

/-- Translate a **mutual clique** into one ranked recursion, plus one declaration per
    member that enters it.

    The merged recursion takes a tag and the parameters of every member; its rank is the
    measure of the member the tag selects, and its body dispatches on the tag.  A call
    from one member to another — which is what makes the clique mutual — is then an
    ordinary `Term.selfCall` of that one recursion with the tag of the callee, so the
    clique is ranked exactly once, at entry, and the grammar's own `Nat.rec` shape bounds
    every call of it.  This is sound because Lean's own termination proof for the clique
    is a *single* measure that decreases along every call, whichever member makes it. -/
def translateClique (moduleDecls : Array Name) (targets : Array Name)
    (clique : Array Name) (targs : List Expr) : MetaM (Array TransDecl) := do
  -- the parameters, the result type and the body of every member
  let mut memberParams : Array (Array (Name × STy)) := #[]
  let mut memberOrig : Array (Array Name) := #[]
  let mut memberSubst : Array (Std.HashMap Name Expr) := #[]
  let mut memberLty : Array (Std.HashMap Name Expr) := #[]
  let mut memberRets : Array STy := #[]
  let mut memberSourceIdx : Array (Array Nat) := #[]
  let mut memberBinderNames : Array (Array Name) := #[]
  let mut bodies : Array Code := #[]
  let mut retTy? : Option STy := none
  for i in [0:clique.size] do
    let n := clique[i]!
    let some d ← getBaseDecl? n
      | throwError "`{n}` has no LCNF body in the compiled module"
    let .code body := d.value
      | throwError "`{n}` is implemented by `@[extern]`, so there is no body to translate"
    -- the members of a polymorphic clique are compiled at the same types
    let some tsub := typeSubstOf? d targs
      | if targs.isEmpty then
          throwOutsideLanguage m!"`{n}` is polymorphic, and the type language is \
            monomorphic: it is compiled once per instantiation a caller uses, and this \
            module has no call of it the front end could read one off"
        else
          throwError "`{n}` takes a different number of type parameters than the call \
            that pulled its clique in supplies"
    let mut params : Array (Name × STy) := #[]
    let mut origs : Array Name := #[]
    let mut ltys : Std.HashMap Name Expr := {}
    -- where each surviving parameter sits among *all* the parameters, which is what the
    -- position of a structural recursion counts
    let mut srcIdx : Array Nat := #[]
    let mut binderNames : Array Name := #[]
    let mut pos := 0
    for p in d.params do
      let here := pos
      pos := pos + 1
      if isTypeParam p || isErasedTypeExpr p.type then
        continue
      let pty := substTypeParams tsub p.type
      let some ty := ← styOf? pty
        | throwOutsideLanguage m!"the parameter `{p.binderName}` of `{n}` has type \
            `{← ppExpr pty}`, which the front end does not translate"
      -- the members are compiled separately, so two of them can name a parameter alike;
      -- the merged recursion gives every member a slot of its own
      params := params.push (Name.mkNum p.fvarId.name i, ty)
      origs := origs.push p.fvarId.name
      srcIdx := srcIdx.push here
      binderNames := binderNames.push p.binderName
      ltys := ltys.insert p.fvarId.name pty
    let some retExpr :=
        (if targs.isEmpty then dropArrows d.params.size d.type
         else declResultPattern d d.params.size).map (substTypeParams tsub)
      | throwError "the type of `{n}` is not an arrow of its parameters"
    let some rty := ← styOf? retExpr
      | throwError "the result type of `{n}`, `{← ppExpr retExpr}`, is not one the front \
          end translates"
    memberSubst := memberSubst.push tsub
    memberLty := memberLty.push ltys
    memberSourceIdx := memberSourceIdx.push srcIdx
    memberBinderNames := memberBinderNames.push binderNames
    memberRets := memberRets.push rty
    if retTy?.isNone then retTy? := some rty
    memberParams := memberParams.push params
    memberOrig := memberOrig.push origs
    bodies := bodies.push body
  let some retTy0 := retTy? | throwError "an empty mutual clique"
  -- the members of a clique may answer with different types — `cata` with an `α`, its
  -- `cataMap` with an `ExprF α`.  The merged recursion is *one* recursion, so it has one
  -- result type: the union of theirs, tagged by the member that answered.  A call of a
  -- member reads its own summand out of it, so nothing outside the clique sees the union.
  let union? :=
    if memberRets.all (· == retTy0) then none
    else cliqueUnionTy clique memberRets
  if memberRets.any (· != retTy0) && union?.isNone then
    throwError "the members of the mutual clique answer with different types, and the \
      front end cannot build the union of them"
  let retTy := union?.getD retTy0
  let measures ← cliqueMeasures clique memberParams memberSourceIdx memberBinderNames
  -- the body of every member, in the context of the merged recursion
  let mut srcBodies : Array Src := #[]
  for i in [0:clique.size] do
    let mut venv : VEnv := {}
    for j in [0:memberParams[i]!.size] do
      let (pname, pty) := memberParams[i]![j]!
      venv := venv.insert memberOrig[i]![j]!
        { src := .var pname, ty := pty, lty := memberLty[i]![memberOrig[i]![j]!]?
          nf := some (some pname, 0) }
    let fctx : FnCtx :=
      { selfName := clique[i]!, recParams := #[], retTy := memberRets[i]!
        moduleDecls := moduleDecls
        cliqueNames := clique, cliqueParams := memberParams
        cliqueUnion := union?, cliqueRetTys := memberRets
        tsubst := memberSubst[i]! }
    let b ← transCode fctx venv {} bodies[i]!
    -- the body answers with the member's own type; the merged recursion answers with the
    -- union, so the answer is tagged with the member that produced it
    srcBodies := srcBodies.push
      (match union? with
       | none => b
       | some u => .ctorS u i [memberRets[i]!] [b])
  -- the merged recursion itself
  let allParams : List (Name × STy) :=
    (cliqueTagName, STy.nat) :: memberParams.toList.flatMap (·.toList)
  let memberNames ← clique.toList.mapM (fun m => instSigName ⟨m, targs⟩)
  let cliqueName := cliqueSigNameOf memberNames
  -- the measure of the merged recursion is lexicographic: the measure of the member the
  -- tag selects, and then the **phase** of that member.  The members of a clique may call
  -- one another *without* descending — `cata` hands its argument to `cataMap` unchanged,
  -- since the `FixExpr` wrapper is erased and the two are the same value — and the phase
  -- is what such a call descends on: it counts down along the order Lean records the
  -- members in, so a call from an earlier member to a later one descends.  A call that
  -- goes the other way without descending on the measure answers `stuck`, which is
  -- observable, rather than a wrong number.
  let phase : Src :=
    .op "natSub" [.nat, .nat] .nat [.natLit (clique.size - 1), .var cliqueTagName]
  let cliqueMeasure : List Src := [tagDispatch measures, phase]
  let cliqueTerm : Src :=
    .fix allParams cliqueMeasure (tagDispatch srcBodies) retTy.dflt
  let cliqueNote : String :=
    let ctx : RCtx := { vars := allParams.map Prod.fst }
    "mutual clique of " ++ toString clique.size ++
      " members; 2 components: [ " ++
      String.intercalate ", " (cliqueMeasure.map (fun m => m.toPretty ctx 0)) ++
      " ] — the measure of the member the tag selects, then its phase"
  let cliqueTy := STy.arrows (allParams.map Prod.snd) retTy
  let mut out : Array TransDecl :=
    #[{ name := clique[0]!, sigName := cliqueName, ty := cliqueTy, term := cliqueTerm
        target := false, measureNote := some cliqueNote }]
  -- one declaration per member: enter the merged recursion with the member's tag
  for i in [0:clique.size] do
    let ps := memberParams[i]!
    let mut app : Src := .ap (.glob cliqueName none) (.natLit i)
    for m in [0:clique.size] do
      for (pname, pty) in memberParams[m]! do
        app := .ap app (if m == i then .var pname else pty.dflt)
    let answer :=
      match union? with
      | none => app
      | some _ => unwrapCliqueResult i memberRets[i]! app
    let term := ps.toList.foldr (fun p acc => Src.lam p.1 acc) answer
    out := out.push
      { name := clique[i]!, sigName := ← instSigName ⟨clique[i]!, targs⟩
        ty := STy.arrows (ps.toList.map Prod.snd) memberRets[i]!, term := term
        target := targets.contains clique[i]! }
  return out

/-! ## A whole module -/

/-- The declarations of `mod` that have compiled code of their own, in name order: the
    public entry points a `<Module>Program.lean` is about. -/
def moduleTargets (env : Environment) (mod : Name) : Array Name := Id.run do
  let some idx := env.getModuleIdx? mod | return #[]
  let mut ns := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternalDetail then
      if let some (.fdecl ..) := Lean.IR.findEnvDecl env n then
        ns := ns.push n
  return ns.qsort Name.lt

/-- Every declaration of `mod`, whatever it is: what a call may name. -/
def moduleNames (env : Environment) (mod : Name) : Array Name := Id.run do
  let some idx := env.getModuleIdx? mod | return #[]
  let mut ns := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      ns := ns.push n
  return ns

/-- Order the translated declarations so that each one only calls the ones before it —
    which is what makes them a `Program`, a telescope with no cycle in it. -/
def topoSort (ds : Array TransDecl) : MetaM (Array TransDecl) := do
  let byName : Std.HashMap String TransDecl :=
    ds.foldl (fun m d => m.insert d.sigName d) {}
  let mut out : Array TransDecl := #[]
  let mut placed : Std.HashSet String := {}
  let mut remaining := ds.toList
  while !remaining.isEmpty do
    let ready := remaining.filter fun d =>
      d.term.globals.all fun g => placed.contains g || !byName.contains g
    if ready.isEmpty then
      throwError "the declarations {remaining.map (·.sigName)} call each other in a \
        cycle; a mutual clique has to become one ranked recursion, which the front end \
        does not build yet"
    for d in ready do
      out := out.push d
      placed := placed.insert d.sigName
    remaining := remaining.filter fun d => !placed.contains d.sigName
  return out

/-- A Lean identifier for a declaration name: `Nat.gcd` becomes `Nat_gcd`. -/
def identOf (name : String) : String :=
  String.ofList (name.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else '_')

/-- The `GlobalDecl` of a translated declaration, as Lean source. -/
def declSource (d : TransDecl) : String :=
  "⟨" ++ d.sigName.quote ++ ", " ++ d.ty.source ++ "⟩"

/-- Drop `n` arrows from a type: the result type of a recursion with `n` parameters. -/
def STy.dropArrows : Nat → STy → Option STy
  | 0, t => some t
  | n + 1, .fn _ b => STy.dropArrows n b
  | _, _ => none

/-- The Lean source of a module's program: a `GlobalDecl` and a `Term` per declaration,
    and the `Program` telescope that ties them together. -/
def leanSourceOf (mod : Name) (ds : Array TransDecl) : String := Id.run do
  let modIdent := (mod.components.map toString).foldl (· ++ ·) ""
  let mut src :=
    "import LakeJs\n\nopen LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops\n\n" ++
    "namespace Program" ++ modIdent ++ "\n\n"
  for i in [0:ds.size] do
    let d := ds[i]!
    let sigNames := ((ds.extract 0 i).toList.map (·.sigName)).reverse
    let sigList := String.intercalate ", "
      (((ds.extract 0 i).toList.map (fun e => "d_" ++ identOf e.sigName)).reverse)
    let dn := "d_" ++ identOf d.sigName
    let tn := "tm_" ++ identOf d.sigName
    let sn := "sig_" ++ identOf d.sigName
    let pn := "prog_" ++ identOf d.sigName
    let prev := if i = 0 then "Program.nil" else "prog_" ++ identOf ds[i-1]!.sigName
    -- a recursion is emitted in three pieces — its measure, its body, and the `Term.fix`
    -- that ties them together — so that `<Module>Descends.lean` can state the
    -- verification condition of *these* two and nothing has to be repeated or re-checked
    let (recParts, tmSource) :=
      match d.term with
      | .fix ps measures fixBody stuck =>
        match d.ty.dropArrows ps.length with
        | some retTy =>
          let bdName := "bd_" ++ identOf d.sigName
          let psSource := String.intercalate ", " (ps.map (fun p => p.2.source))
          let inner : RCtx := { vars := ps.map Prod.fst, sig := sigNames }
          let k := measures.length
          ("/-- The body of the recursion of `" ++ d.sigName ++ "`. -/\n" ++
           "def " ++ bdName ++ " : Term " ++ sn ++ " ([" ++ psSource ++ "] ++ []) [⟨[" ++
             psSource ++ "], " ++ retTy.source ++ "⟩] " ++ retTy.source ++ " :=\n  " ++
           fixBody.toLean inner ++ "\n\n",
           "Term.fix [" ++ psSource ++ "] " ++ toString k ++ " " ++
             spineSource (measures.map (fun m => m.toLean inner)) ++ " " ++
             bdName ++ " " ++ stuck.toLean inner)
        | none => ("", d.term.toLean { sig := sigNames })
      | _ => ("", d.term.toLean { sig := sigNames })
    src := src ++ "/-- `" ++ d.sigName ++ "`, as a declaration of the module. -/\n" ++
      "def " ++ dn ++ " : GlobalDecl := " ++ declSource d ++ "\n\n" ++
      "/-- The signature `" ++ d.sigName ++ "` is written against. -/\n" ++
      "def " ++ sn ++ " : Sig := ⟨[" ++ sigList ++ "], by decide⟩\n\n" ++
      recParts ++
      "/-- The body of `" ++ d.sigName ++ "`. -/\n" ++
      "def " ++ tn ++ " : Term " ++ sn ++ " [] [] " ++ d.ty.source ++ " :=\n  " ++
      tmSource ++ "\n\n" ++
      "/-- The module up to and including `" ++ d.sigName ++ "`. -/\n" ++
      "def " ++ pn ++ " : Program (" ++ dn ++ " :: " ++ sn ++ ".decls) :=\n  " ++
      ".cons " ++ dn ++ " " ++ sn ++ ".h_names_unique " ++ tn ++ " " ++ prev ++ "\n\n"
  let sigAll := String.intercalate ", "
    ((ds.toList.map (fun e => "d_" ++ identOf e.sigName)).reverse)
  src := src ++ "/-- The signature of the whole module. -/\ndef moduleSig : Sig := ⟨[" ++
    sigAll ++ "], by decide⟩\n\n" ++
    "/-- The module as a telescope: every body is written against the declarations \
      before it, so the call graph is acyclic by construction.  It is built one \
      declaration at a time, above, so that no single elaboration sees the whole \
      telescope at once. -/\ndef program : Program moduleSig.decls :=\n  "
  let last := match ds.back? with
    | some d => "prog_" ++ identOf d.sigName
    | none => "Program.nil"
  return src ++ last ++ "\n\nend Program" ++ modIdent ++ "\n"

/-- A block of prose as Lean line comments, one `--` per line.  Lines that are already
    comments are left alone, so a header can be passed through unchanged. -/
def commentBlock (s : String) : String :=
  String.intercalate "\n" ((s.splitOn "\n").map fun l =>
    if l.isEmpty then "--"
    else if l.startsWith "--" then l
    else "-- " ++ l)

/-- The text of a module's `<Module>Program.lean`: the tree of every declaration, as a
    comment at the top of the file, and the program itself as Lean source.  The whole file
    is Lean, and type checks against `import LakeJs`. -/
def programText (mod : Name) (ds : Array TransDecl) (failures : Array (Name × String))
    (outside : Array (Name × String)) (rejections : Array LakeJs.Totality.Rejection) :
    String := Id.run do
  let mut trees := ""
  for i in [0:ds.size] do
    let d := ds[i]!
    let sig := ((ds.extract 0 i).toList.map (·.sigName)).reverse
    let marker := if d.target then "🎯" else "📦"
    let note :=
      match d.measureNote with
      | some m => "     measure: " ++ m ++ "\n"
      | none => ""
    trees := trees ++ "════ " ++ marker ++ " " ++ d.sigName ++ " : " ++ d.ty.pretty ++ "\n" ++
      note ++ d.term.toPretty { sig := sig } 0 ++ "\n\n"
  let mut header :=
    "-- " ++ toString mod ++ ": the module as a Program of the one grammar of `LakeJs.Expr`.\n" ++
    "-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.\n" ++
    "-- Every term below is a `Term`, so it is terminating by construction: the one way it\n" ++
    "-- repeats work is `Term.fix`, whose measure it descends on at every self call.\n"
  for r in rejections do
    header := header ++ "-- refused by the totality gate: " ++ r.message ++ "\n"
  for (n, why) in outside do
    header := header ++ "-- outside the language: `" ++ toString n ++ "`: " ++ why ++ "\n"
  for (n, why) in failures do
    header := header ++ "-- not translated: `" ++ toString n ++ "`: " ++ why ++ "\n"
  return commentBlock (header ++ "\n" ++ trees) ++ "\n" ++
    "-- ── the same program as Lean source ────────────────────────────────────\n" ++
    "-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;\n" ++
    "-- copy one into a `[LEAN|...]` elaboration if you want to read it there.\n\n" ++
    leanSourceOf mod ds

/-! ## The verification condition, generated for every recursion

A generated program is terminating because it is a `Term`; that its recursions never reach
their `stuck` branch is a *different* statement, `Term.Descends`, and it is the one that
says the measure the front end read is right.  `<Module>Descends.lean` states it for every
recursion the module has and proves it with `descent_auto`, the tactic of
`LakeJs.DescentTactic`: the derivation is assembled from the rules of `LakeJs.DescentVC`,
one per node of the body, and the arithmetic each self call leaves — exactly the obligation
Lean's own `decreasing_by` discharged — is closed by `omega`.

So a measure the front end read wrongly no longer has to be caught by a differential check
at run time: **the generated file does not elaborate**.  Where the tactic cannot close the
arithmetic the declaration is listed in the header instead of being asserted, so the file
says what it has proved and what it has not. -/

/-- The declarations of a module whose verification condition `descent_auto` is not asked
    to prove, with the reason.  A name is listed here only after the tactic has been seen
    to fail on it; the file then says so in its header rather than failing to elaborate. -/
def descentSkip : List (String × String) := []

/-- The text of a module's `<Module>Descends.lean`, or `""` when the module has no
    recursion. -/
def descendsText (mod : Name) (ds : Array TransDecl) : String := Id.run do
  let modIdent := (mod.components.map toString).foldl (· ++ ·) ""
  let mut body := ""
  let mut skipped := ""
  for d in ds do
    match d.term with
    | .fix ps measures _ _ =>
      let some retTy := d.ty.dropArrows ps.length | continue
      let tn := "tm_" ++ identOf d.sigName
      let sn := "sig_" ++ identOf d.sigName
      let bdName := "bd_" ++ identOf d.sigName
      let psSource := String.intercalate ", " (ps.map (fun p => p.2.source))
      let inner : RCtx := { vars := ps.map Prod.fst, sig := [] }
      let msSource := spineSource (measures.map (fun m => m.toLean inner))
      let k := measures.length
      match descentSkip.find? (fun e => e.1 == d.sigName) with
      | some (_, why) =>
        skipped := skipped ++ "-- not proved: `" ++ d.sigName ++ "`: " ++ why ++ "\n"
      | none =>
        body := body ++
          "/-- **The verification condition of `" ++ d.sigName ++ "`**: every self call of \
            `" ++ bdName ++ "` is made at arguments of strictly smaller measure — the \
            measure written out here is the one `" ++ tn ++ "` carries — so its `stuck` \
            branch is unreachable and the recursion satisfies the ordinary unrolling \
            equation. -/\n" ++
          "theorem " ++ tn ++ "_descends (δ : GEnv " ++ sn ++ ".decls) :\n" ++
          "    Term.Descends (Sg := " ++ sn ++ ") (Γ := []) (Ρ := []) (ps := [" ++
            psSource ++ "]) (τ := " ++ retTy.source ++ ") (k := " ++ toString k ++ ")\n" ++
          "      " ++ msSource ++ "\n      " ++ bdName ++ " δ .nil .nil := by\n" ++
          "  descent_auto as\n\n"
    | _ => pure ()
  if body.isEmpty && skipped.isEmpty then
    return ""
  let header :=
    "/-\nThe verification condition of every recursion of `" ++ toString mod ++
      "`, generated by the front end.\n\n\
     `Term.Descends measure body δ γ ρ` says that the body consults its self-reference \
     only at arguments of strictly smaller measure.  From it, `LakeJs.Descends` derives \
     that the `stuck` branch is never taken and that the recursion satisfies the ordinary \
     unrolling equation — so this file is the statement that the measure the front end \
     read off Lean's `termination_by` (or off the structure of the recursion subject) is \
     *right*, checked on the emitted term rather than on the Lean source it came from.\n\n\
     Each proof is one call of `descent_auto`, which assembles the derivation from the \
     rules of `LakeJs.DescentVC` and closes the arithmetic each self call leaves.\n-/\n\n" ++
    skipped ++
    "import " ++ toString mod ++ "Program\n\n\
     open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops Program" ++ modIdent ++ "\n\n\
     -- the statements mention whole emitted bodies, and the tactic runs the interpreter \
     over them, so both are well past the default budget\n\
     set_option maxHeartbeats 2000000\n\n\
     namespace Descends" ++ modIdent ++ "\n\n"
  return header ++ body ++ "end Descends" ++ modIdent ++ "\n"

/-! ## Differential checks, generated for every translated declaration

A recursion answers `stuck` when its measure fails to descend at a self call, so a wrong
measure shows up as a *wrong answer at run time* rather than as a term that does not
elaborate.  These generated checks are what makes that loud: for every declaration the
front end translated whose arguments and result are `Nat`, `Int` or `Bool`, the file
`<Module>AutoCheck.lean` runs the emitted term and the Lean declaration it was translated
from at a sample of inputs and asserts that they agree.  Building the snapshot library is
then a test of the translation, not only of the grammar. -/

/-- The Lean type a type of the language is written as, when the check generator knows how
    to write literals of it. -/
def STy.checkLeanName? : STy → Option String
  | .nat => some "Nat"
  | .int => some "Int"
  | .bool => some "Bool"
  | _ => none

/-- The same Lean type as an expression, so that the declaration a term was translated
    from can be checked to have *exactly* it: one that also takes a proof, or a
    compiler-generated specialization, does not and is skipped. -/
def STy.checkLeanExpr? : STy → Option Expr
  | .nat => some (mkConst ``Nat)
  | .int => some (mkConst ``Int)
  | .bool => some (mkConst ``Bool)
  | .fn a b => do return .forallE `x (← a.checkLeanExpr?) (← b.checkLeanExpr?) .default
  | _ => none

/-- Split an arrow type into its arguments and its result. -/
def STy.argsAndResult : STy → List STy × STy
  | .fn a b => let (as, r) := b.argsAndResult; (a :: as, r)
  | t => ([], t)

/-- The values a parameter of a scalar type is sampled at.  The sample shrinks as the
    arity grows, since the checks run every combination. -/
def STy.checkSamples (arity : Nat) : STy → List String
  | .nat =>
      if arity ≤ 1 then ["0", "1", "2", "3", "4", "5", "6", "9"]
      else if arity == 2 then ["0", "1", "2", "3"]
      else ["0", "1", "2"]
  | .int =>
      if arity ≤ 1 then ["(-3)", "(-1)", "0", "2", "5"]
      else if arity == 2 then ["(-2)", "0", "3"]
      else ["(-1)", "0", "2"]
  | .bool => ["true", "false"]
  | _ => []

/-- Every combination of one sample per parameter. -/
def sampleTuples : List (List String) → List (List String)
  | [] => [[]]
  | vs :: rest => (sampleTuples rest).flatMap fun t => vs.map fun v => v :: t

/-- The text of a module's `<Module>AutoCheck.lean`, or `""` when the module has no
    declaration the generator can sample. -/
def autoCheckText (mod : Name) (ds : Array TransDecl) : MetaM String := do
  let env ← getEnv
  let modIdent := (mod.components.map toString).foldl (· ++ ·) ""
  let mut body := ""
  let mut seen : Std.HashSet Name := {}
  for i in [0:ds.size] do
    let d := ds[i]!
    if seen.contains d.name then continue
    let (argTys, retTy) := d.ty.argsAndResult
    if argTys.isEmpty || argTys.length > 3 then continue
    if retTy.checkLeanName?.isNone then continue
    if argTys.any (fun a => a.checkLeanName?.isNone) then continue
    if d.name.isInternal || isPrivateName d.name then continue
    let some cinfo := env.find? d.name | continue
    unless cinfo.levelParams.isEmpty do continue
    let some want := d.ty.checkLeanExpr? | continue
    unless ← Meta.isDefEq cinfo.type want do continue
    seen := seen.insert d.name
    let tn := "tm_" ++ identOf d.sigName
    let prev := if i == 0 then "Program.nil" else "prog_" ++ identOf ds[i - 1]!.sigName
    let runName := "run_" ++ identOf d.sigName
    let binders := String.join (argTys.zipIdx.map fun (a, j) =>
      " (a" ++ toString j ++ " : " ++ a.checkLeanName?.getD "Nat" ++ ")")
    let appArgs := String.join ((List.range argTys.length).map fun j => " a" ++ toString j)
    let tuples := sampleTuples (argTys.map (STy.checkSamples argTys.length))
    let call (head : String) (t : List String) : String :=
      head ++ String.join (t.map (fun v => " " ++ v))
    let lhs := String.intercalate ", " (tuples.map (call runName))
    let rhs := String.intercalate ", " (tuples.map (call ("_root_." ++ toString d.name)))
    body := body ++
      "/-- `" ++ toString d.name ++ "`, as the emitted term computes it. -/\n" ++
      "def " ++ runName ++ binders ++ " : " ++ (retTy.checkLeanName?.getD "Nat") ++ " :=\n" ++
      "  Program.run " ++ prev ++ " " ++ tn ++ appArgs ++ "\n\n" ++
      "/-- The emitted term and `" ++ toString d.name ++ "` agree on the sample. -/\n" ++
      "theorem " ++ identOf d.sigName ++ "_agrees :\n" ++
      "    [" ++ lhs ++ "] =\n      [" ++ rhs ++ "] := by native_decide\n\n"
  if body.isEmpty then
    return ""
  let header :=
    "/-\nDifferential checks for `" ++ toString mod ++ "`, generated by the front end.\n\n\
     Every declaration below was translated into a `Term`, which is terminating by \
     construction; what these checks add is that it computes the *same function* as the \
     Lean declaration it came from.  A recursion whose measure fails to descend at a self \
     call answers `stuck`, so a measure the front end read wrongly shows up here as a \
     disagreement rather than as a silent wrong answer later.\n-/\n\n\
     import " ++ toString mod ++ "Program\nimport " ++ toString mod ++ "\n\n\
     open LakeJs LakeJs.Expr Program" ++ modIdent ++ "\n\n\
     namespace AutoCheck" ++ modIdent ++ "\n\n"
  return header ++ body ++ "end AutoCheck" ++ modIdent ++ "\n"

/-- What the front end made of a module. -/
structure ModuleResult where
  /-- The text of the `<Module>Program.lean`. -/
  text : String
  /-- The Lean source part of it, without the header comment. -/
  leanSource : String
  /-- The text of the `<Module>AutoCheck.lean`, or `""` when the module has no
      declaration the check generator can sample. -/
  autoCheck : String
  /-- The text of the `<Module>Descends.lean`, or `""` when the module has no
      recursion. -/
  descends : String
  /-- The declarations it translated. -/
  decls : Array TransDecl
  /-- The declarations it failed to translate although they are programs of the
      language, and why.  This is the list that has to stay empty. -/
  failures : Array (Name × String)
  /-- The declarations that are not programs of the language at all, and why. -/
  outside : Array (Name × String)
  /-- What the totality gate refused. -/
  rejections : Array LakeJs.Totality.Rejection

/-- Translate a whole module: the totality gate, then every public declaration, then the
    text of its `<Module>Program.lean`. -/
def translateModule (mod : Name) : MetaM ModuleResult := do
  let env ← getEnv
  let targets := moduleTargets env mod
  let names := moduleNames env mod
  let moduleIdxs : Array Nat :=
    match env.getModuleIdx? mod with
    | some i => #[i.toNat]
    | none => #[]
  let rejections ← LakeJs.Totality.check moduleIdxs targets
  let mut ds : Array TransDecl := #[]
  let mut failures : Array (Name × String) := #[]
  let mut outside : Array (Name × String) := #[]
  -- the names, as they are written out, of the declarations that are outside the
  -- language: what calls one of them is outside the language too
  let mut outsideSig : Std.HashSet String := {}
  -- and the names of the declarations the totality gate refused: what calls one of
  -- those is refused for the same reason, not a translation failure
  let mut rejectedSig : Std.HashSet String := {}
  let mut rejections := rejections
  -- what has been dealt with, by the name it is written out under: a polymorphic
  -- declaration is translated once per instantiation, so the name carries the types
  let mut done : Std.HashSet String := {}
  for n in targets do
    if done.contains (toString n) then
      continue
    -- the totality gate already says, at the top of the file, what it refused and why;
    -- a declaration it refused is not a translation failure as well
    if rejections.any (·.name == n) then
      done := done.insert (toString n)
      rejectedSig := rejectedSig.insert (toString n)
      continue
    -- a mutual clique is translated once, as one ranked recursion
    let clique :=
      match LakeJs.Totality.recKind? env (LakeJs.Totality.resolveModel n) with
      | .ok (.structural _ c) => c
      | .ok (.wellFounded c) => c
      | _ => #[n]
    if clique.size > 1 then
      for m in clique do
        done := done.insert (toString m)
      try
        ds := ds ++ (← translateClique names targets clique [])
      catch e =>
        let msg ← e.toMessageData.toString
        for m in clique do
          match outsideLanguage? msg with
          | some why =>
              outside := outside.push (m, why)
              outsideSig := outsideSig.insert (toString m)
          | none => failures := failures.push (m, msg)
    else
      done := done.insert (toString n)
      try
        ds := ds.push (← translateDecl names true ⟨n, []⟩)
      catch e =>
        let msg ← e.toMessageData.toString
        match outsideLanguage? msg with
        | some why =>
            outside := outside.push (n, why)
            outsideSig := outsideSig.insert (toString n)
        | none => failures := failures.push (n, msg)
  -- pull in the declarations a translated body calls but that are not public entry
  -- points of their own (📦), until nothing is left to pull in
  let mut progress := true
  while progress && ds.size < 400 do
    progress := false
    let known : Std.HashSet String := ds.foldl (fun s d => s.insert d.sigName) {}
    let mut missing : Array Inst := #[]
    for d in ds do
      for inst in d.term.globalDecls do
        let sname ← instSigName inst
        if !known.contains sname && !done.contains sname then
          missing := missing.push inst
    for inst in missing do
      let n := inst.name
      let sname ← instSigName inst
      if done.contains sname then
        continue
      let rej ← LakeJs.Totality.check moduleIdxs #[n]
      if let some r := rej[0]? then
        done := done.insert sname
        rejectedSig := rejectedSig.insert sname
        unless rejections.any (·.name == r.name) do
          rejections := rejections.push r
        continue
      let clique :=
        match LakeJs.Totality.recKind? env (LakeJs.Totality.resolveModel n) with
        | .ok (.structural _ c) => c
        | .ok (.wellFounded c) => c
        | _ => #[n]
      -- `n` itself, as well as the clique its body belongs to: a core function compiled
      -- from a model of `LakeJs.CoreModels` is in a clique under the model's name
      done := done.insert sname
      for m in clique do
        done := done.insert (← instSigName ⟨m, inst.targs⟩)
      progress := true
      try
        if clique.size > 1 then
          ds := ds ++ (← translateClique names targets clique inst.targs)
        else
          ds := ds.push (← translateDecl names false inst)
      catch e =>
        let msg ← e.toMessageData.toString
        for m in clique do
          match outsideLanguage? msg with
          | some why =>
              outside := outside.push (m, why)
              outsideSig := outsideSig.insert (← instSigName ⟨m, inst.targs⟩)
          | none => failures := failures.push (m, msg)
  -- a declaration that calls one the front end refused cannot be written out either:
  -- drop it, and whatever calls it in turn, rather than emitting a dangling name
  let mut changed := true
  while changed do
    changed := false
    let known : Std.HashSet String := ds.foldl (fun s d => s.insert d.sigName) {}
    let mut kept : Array TransDecl := #[]
    for d in ds do
      match d.term.globals.find? (fun g => !known.contains g) with
      | some g =>
          if rejectedSig.contains g then
            rejections := rejections.push
              { name := d.name
                reason := "it calls `" ++ g ++ "`, which the totality gate refused" }
            rejectedSig := rejectedSig.insert d.sigName
          else if outsideSig.contains g then
            outside := outside.push
              (d.name, "it calls `" ++ g ++ "`, which is outside the language")
            outsideSig := outsideSig.insert d.sigName
          else
            failures := failures.push
              (d.name, "it calls `" ++ g ++ "`, which was not translated")
          changed := true
      | none => kept := kept.push d
    ds := kept
  let ordered ← topoSort ds
  -- a polymorphic declaration is written out once per instantiation a caller uses: the
  -- attempt to compile it at no instantiation of its own is not something to report,
  -- since the program does contain it
  let written : Std.HashSet Name := ordered.foldl (fun s d => s.insert d.name) {}
  outside := outside.filter (fun (n, _) => !written.contains n)
  failures := failures.filter (fun (n, _) => !written.contains n)
  return { text := programText mod ordered failures outside rejections
           leanSource := leanSourceOf mod ordered
           autoCheck := ← autoCheckText mod ordered
           descends := descendsText mod ordered
           decls := ordered, failures := failures, outside := outside
           rejections := rejections }

end LakeJs.FrontEnd
