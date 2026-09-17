import Lean
import LakeJs.Expr
import LakeJs.SurfaceParse

/-!
# `[LEAN| … ]`: writing a `Term` in its own syntax

`LakeJs.Expr.Term` is intrinsically scoped, typed and linked, so writing one by hand
means counting binders, counting signature entries and supplying three kinds of proof.
This module lets one write it the way it reads instead:

```
open LakeJs.Expr in
def addOne : Term [] [] (.fn [.nat] .nat) :=
  [LEAN|
sig (fn [nat] nat)
|glob
|vars
|
(fn [v0 : nat]
  (app
    (extern lean_nat_add)
    v0
    (lit nat 1)))
]
```

The four sections of the header are the four things a `Term` is written against:

* `sig` — the type the code has, which is the `τ` of `Term Sg Γ τ`;
* `glob` — the signature `Sg`: the top-level declarations the code may name, in the
  order the signature declares them, so that a name in the code is an index into it;
* `vars` — the context `Γ`, de Bruijn index 0 first, each slot named;
* the code itself.

A section may be left out, and they may be written in any order; what the delaborator
prints is the canonical order above.

What the elaborator does is resolve the names — a name is a variable of the context if
the context has it and a declaration of the signature otherwise — and recompute the
proofs: the evidence a `ctor`, a `proj`, a `tagOf` and a `case` carry is a proof of a
decidable fact about the types that are written down, so `rfl` supplies it.  Nothing
here is checked by this module: the fragment is turned into ordinary Lean syntax and
*Lean* checks it, so an ill-typed fragment is an ordinary type error.

`LakeJs.TermDeelab` is the other direction, and its output is exactly what the parser
here reads.
-/

namespace LakeJs.TermElab

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

open Lean
open LakeJs
open LakeJs.Surface

/-! ## The raw-text parser

The fragment is read as text, so that none of its words becomes a Lean token.  The
scan stops at the `]` that closes the `[LEAN|` — brackets inside the fragment are
counted, and a `]` inside a string or character literal is skipped. -/

namespace Embed

open Lean.Parser

/-- Skip a string or character literal, the opening quote already consumed. -/
def skipLit (c : ParserContext) (quote : Char) :
    Nat → String.Pos.Raw → Option String.Pos.Raw
  | 0, _ => none
  | fuel + 1, pos =>
    if c.atEnd pos then none
    else
      let ch := c.get pos
      if ch == quote then some (c.next pos)
      else if ch == '\\' then
        let pos := c.next pos
        if c.atEnd pos then none else skipLit c quote fuel (c.next pos)
      else skipLit c quote fuel (c.next pos)

/-- Scan to the `]` that closes the fragment, at bracket depth zero. -/
def scanToEnd (c : ParserContext) (s : ParserState) :
    Nat → Nat → String.Pos.Raw → ParserState
  | 0, _, pos => s.mkErrorAt "the `]` that closes `[LEAN|`" pos
  | fuel + 1, depth, pos =>
    if c.atEnd pos then s.mkErrorAt "the `]` that closes `[LEAN|`" pos
    else
      let ch := c.get pos
      if ch == '"' || ch == '\'' then
        match skipLit c ch fuel (c.next pos) with
        | none => s.mkErrorAt "the end of a literal" pos
        | some pos => scanToEnd c s fuel depth pos
      else if ch == '[' then scanToEnd c s fuel (depth + 1) (c.next pos)
      else if ch == ']' then
        match depth with
        | 0 => s.setPos pos
        | d + 1 => scanToEnd c s fuel d (c.next pos)
      else scanToEnd c s fuel depth (c.next pos)

/-- Consume the fragment up to, but not including, its closing `]`. -/
def bodyFn : ParserFn := fun c s =>
  scanToEnd c s (c.endPos.byteIdx + 1) 0 s.pos

/-- Read the fragment as one raw atom and consume the closing `]`. -/
def rawFn' : ParserFn := fun c s =>
  let s := rawFn bodyFn (trailingWs := false) c s
  if s.hasError then s
  else whitespace c (s.setPos (s.pos + "]"))

/-- The parser for the body of a `[LEAN| … ]` fragment. -/
def leanRaw : Parser where
  fn := rawFn'

@[combinator_formatter LakeJs.TermElab.Embed.leanRaw]
def leanRaw.formatter : PrettyPrinter.Formatter := pure ()

@[combinator_parenthesizer LakeJs.TermElab.Embed.leanRaw]
def leanRaw.parenthesizer : PrettyPrinter.Parenthesizer := pure ()

end Embed

open Embed in
/-- A `LakeJs.Expr.Term`, written in the surface syntax of this module. -/
syntax:max (name := leanTermEmbed) "[LEAN|" leanRaw : term

/-! ## From the written tree to Lean syntax

Every rule below builds the Lean term that *Lean* then elaborates, so the typing of a
fragment is Lean's own typing of the constructors of `Term`. -/

open Lean.Elab Lean.Elab.Term

/-- An integer, as Lean syntax. -/
def intStx (i : Int) : MacroM (TSyntax `term) :=
  if i < 0 then `(-$(Lean.quote i.natAbs)) else `($(Lean.quote i.natAbs))

/-- A terminal type, as Lean syntax. -/
def primStx (p : LeanPrimTy) : MacroM (TSyntax `term) :=
  match p with
  | .bitvec n _ => `(LakeJs.LeanPrimTy.bitvec $(Lean.quote n))
  | p => pure ⟨Lean.mkIdent (`LakeJs.LeanPrimTy ++ Name.mkSimple p.pretty)⟩

mutual

/-- A closed type, as Lean syntax. -/
partial def tyStx (t : Ty) : MacroM (TSyntax `term) := do
  match t with
  | .prim p => do `(LakeJs.Ty.prim $(← primStx p))
  | .typeParam => `(LakeJs.Ty.typeParam)
  | .fn ps r => do `(LakeJs.Ty.fn [$((← ps.mapM tyStx).toArray),*] $(← tyStx r))
  | .fn_returnsProd ps r1 rs => do
      `(LakeJs.Ty.fn_returnsProd [$((← ps.mapM tyStx).toArray),*] $(← tyStx r1)
          [$((← rs.mapM tyStx).toArray),*])
  | .array a => do `(LakeJs.Ty.array $(← tyStx a))
  | .list a => do `(LakeJs.Ty.list $(← tyStx a))
  | .task a => do `(LakeJs.Ty.task $(← tyStx a))
  | .promise a => do `(LakeJs.Ty.promise $(← tyStx a))
  | .thunk a => do `(LakeJs.Ty.thunk $(← tyStx a))
  | .lazy a => do `(LakeJs.Ty.lazy $(← tyStx a))
  | .enum e => do
      `(LakeJs.Ty.enum ⟨$(Lean.quote e.extraConstructors), $(← intStx e.shift)⟩)
  | .record fs => do `(LakeJs.Ty.record $(← tyA2Stx fs))
  | .taggedUnion cs => do `(LakeJs.Ty.taggedUnion $(← tyTUStx cs))
  | .recTaggedUnion ⟨cs⟩ => do `(LakeJs.Ty.recTaggedUnion ⟨$(← rtyTUStx cs)⟩)
  | .recObject ⟨fs⟩ => do `(LakeJs.Ty.recObject ⟨$(← rtyA2Stx fs)⟩)
  | .recAlias ⟨a⟩ => do `(LakeJs.Ty.recAlias ⟨$(← rtyStx a)⟩)
  | .mutualRecursiveFamily f => do
      `(LakeJs.Ty.mutualRecursiveFamily $(← familyStx f))

/-- A list of closed types, as the Lean syntax of a list. -/
partial def tyListStx (ts : List Ty) : MacroM (TSyntax `term) := do
  `([$((← ts.mapM tyStx).toArray),*])

/-- The fields of a record of closed types, as Lean syntax. -/
partial def tyA2Stx (fs : LeanRecordSchema Ty) : MacroM (TSyntax `term) := do
  `(⟨$(← tyStx fs.fst), $(← tyStx fs.snd), $(← tyListStx fs.rest)⟩)

/-- The fields of a constructor that has at least one, as Lean syntax. -/
partial def tyNEStx (f : NonEmptyList Ty) : MacroM (TSyntax `term) := do
  `(⟨$(← tyStx f.head), $(← tyListStx f.tail)⟩)

/-- The constructors of a tagged union of closed types, as Lean syntax. -/
partial def tyTUStx (c : LeanTaggedUnionSchema Ty) : MacroM (TSyntax `term) := do
  match c with
  | .payloadFirst f n r =>
      `(LakeJs.LeanTaggedUnionSchema.payloadFirst $(← tyNEStx f) $(← tyListStx n)
          [$((← r.mapM tyListStx).toArray),*])
  | .skip rest => do `(LakeJs.LeanTaggedUnionSchema.skip $(← tyCPStx rest))

/-- The constructors that follow a field-less one, as Lean syntax. -/
partial def tyCPStx (c : CtorsWithPayload Ty) : MacroM (TSyntax `term) := do
  match c with
  | .here f r =>
      `(LakeJs.CtorsWithPayload.here $(← tyNEStx f) [$((← r.mapM tyListStx).toArray),*])
  | .skip rest => do `(LakeJs.CtorsWithPayload.skip $(← tyCPStx rest))

/-- A type inside a recursive declaration, as Lean syntax. -/
partial def rtyStx (t : Ty.RTy) : MacroM (TSyntax `term) := do
  match t with
  | .self i => `(LakeJs.Ty.RTy.self $(Lean.quote i))
  | .prim p => do `(LakeJs.Ty.RTy.prim $(← primStx p))
  | .typeParam => `(LakeJs.Ty.RTy.typeParam)
  | .fn ps r => do `(LakeJs.Ty.RTy.fn [$((← ps.mapM rtyStx).toArray),*] $(← rtyStx r))
  | .fn_returnsProd ps r1 rs => do
      `(LakeJs.Ty.RTy.fn_returnsProd [$((← ps.mapM rtyStx).toArray),*] $(← rtyStx r1)
          [$((← rs.mapM rtyStx).toArray),*])
  | .array a => do `(LakeJs.Ty.RTy.array $(← rtyStx a))
  | .list a => do `(LakeJs.Ty.RTy.list $(← rtyStx a))
  | .task a => do `(LakeJs.Ty.RTy.task $(← rtyStx a))
  | .promise a => do `(LakeJs.Ty.RTy.promise $(← rtyStx a))
  | .thunk a => do `(LakeJs.Ty.RTy.thunk $(← rtyStx a))
  | .lazy a => do `(LakeJs.Ty.RTy.lazy $(← rtyStx a))
  | .enum e => do
      `(LakeJs.Ty.RTy.enum ⟨$(Lean.quote e.extraConstructors), $(← intStx e.shift)⟩)
  | .record fs => do `(LakeJs.Ty.RTy.record $(← rtyA2Stx fs))
  | .taggedUnion cs => do `(LakeJs.Ty.RTy.taggedUnion $(← rtyTUStx cs))
  | .recTaggedUnion ⟨cs⟩ => do `(LakeJs.Ty.RTy.recTaggedUnion ⟨$(← rtyTUStx cs)⟩)
  | .recObject ⟨fs⟩ => do `(LakeJs.Ty.RTy.recObject ⟨$(← rtyA2Stx fs)⟩)
  | .recAlias ⟨a⟩ => do `(LakeJs.Ty.RTy.recAlias ⟨$(← rtyStx a)⟩)
  | .mutualRecursiveFamily f => do
      `(LakeJs.Ty.RTy.mutualRecursiveFamily $(← familyStx f))

/-- A list of types inside a recursive declaration, as the Lean syntax of a list. -/
partial def rtyListStx (ts : List Ty.RTy) : MacroM (TSyntax `term) := do
  `([$((← ts.mapM rtyStx).toArray),*])

/-- The fields of a record, as Lean syntax. -/
partial def rtyA2Stx (fs : LeanRecordSchema Ty.RTy) : MacroM (TSyntax `term) := do
  `(⟨$(← rtyStx fs.fst), $(← rtyStx fs.snd), $(← rtyListStx fs.rest)⟩)

/-- The fields of a constructor that has at least one, as Lean syntax. -/
partial def rtyNEStx (f : NonEmptyList Ty.RTy) : MacroM (TSyntax `term) := do
  `(⟨$(← rtyStx f.head), $(← rtyListStx f.tail)⟩)

/-- The constructors of a tagged union, as Lean syntax. -/
partial def rtyTUStx (c : LeanTaggedUnionSchema Ty.RTy) : MacroM (TSyntax `term) := do
  match c with
  | .payloadFirst f n r =>
      `(LakeJs.LeanTaggedUnionSchema.payloadFirst $(← rtyNEStx f) $(← rtyListStx n)
          [$((← r.mapM rtyListStx).toArray),*])
  | .skip rest => do `(LakeJs.LeanTaggedUnionSchema.skip $(← rtyCPStx rest))

/-- The constructors that follow a field-less one, as Lean syntax. -/
partial def rtyCPStx (c : CtorsWithPayload Ty.RTy) : MacroM (TSyntax `term) := do
  match c with
  | .here f r =>
      `(LakeJs.CtorsWithPayload.here $(← rtyNEStx f) [$((← r.mapM rtyListStx).toArray),*])
  | .skip rest => do `(LakeJs.CtorsWithPayload.skip $(← rtyCPStx rest))

/-- A member of a mutual family, as Lean syntax. -/
partial def famStx (m : Ty.FamMember) : MacroM (TSyntax `term) := do
  match m with
  | .ctors cs => do `(LakeJs.LeanFamMemberSchema.ctors $(← rtyTUStx cs))
  | .record fs => do `(LakeJs.LeanFamMemberSchema.record $(← rtyA2Stx fs))
  | .alias t => do `(LakeJs.LeanFamMemberSchema.alias $(← rtyStx t))

/-- A mutual family, as Lean syntax. -/
partial def familyStx (f : LeanMutualRecFamily Ty.RTy) : MacroM (TSyntax `term) := do
  match f with
  | .selectedThenMore before current next after =>
      `(LakeJs.LeanMutualRecFamily.selectedThenMore
          [$((← before.mapM famStx).toArray),*] $(← famStx current) $(← famStx next)
          [$((← after.mapM famStx).toArray),*])
  | .selectedLast first before current =>
      `(LakeJs.LeanMutualRecFamily.selectedLast $(← famStx first)
          [$((← before.mapM famStx).toArray),*] $(← famStx current))

end

/-- A constant, as Lean syntax. -/
def litStx (l : SLit) : MacroM (TSyntax `term) := do
  match l with
  | .bool b => `(LakeJs.Expr.Lit.bool $(Lean.quote b))
  | .nat n => `(LakeJs.Expr.Lit.nat $(Lean.quote n))
  | .int i => do `(LakeJs.Expr.Lit.int $(← intStx i))
  | .bitvec w v =>
      `(LakeJs.Expr.Lit.bitvec (n := $(Lean.quote w)) (h := by decide)
          (BitVec.ofNat $(Lean.quote w) $(Lean.quote v)))
  | .uint8 n => `(LakeJs.Expr.Lit.uint8 (UInt8.ofNat $(Lean.quote n)))
  | .uint16 n => `(LakeJs.Expr.Lit.uint16 (UInt16.ofNat $(Lean.quote n)))
  | .uint32 n => `(LakeJs.Expr.Lit.uint32 (UInt32.ofNat $(Lean.quote n)))
  | .uint64 n => `(LakeJs.Expr.Lit.uint64 (UInt64.ofNat $(Lean.quote n)))
  | .usize n => `(LakeJs.Expr.Lit.usize (USize.ofNat $(Lean.quote n)))
  | .int8 i => do `(LakeJs.Expr.Lit.int8 (Int8.ofInt $(← intStx i)))
  | .int16 i => do `(LakeJs.Expr.Lit.int16 (Int16.ofInt $(← intStx i)))
  | .int32 i => do `(LakeJs.Expr.Lit.int32 (Int32.ofInt $(← intStx i)))
  | .int64 i => do `(LakeJs.Expr.Lit.int64 (Int64.ofInt $(← intStx i)))
  | .isize i => do `(LakeJs.Expr.Lit.isize (ISize.ofInt $(← intStx i)))
  | .char c => `(LakeJs.Expr.Lit.char (Char.ofNat $(Lean.quote c.toNat)))
  | .string s => `(LakeJs.Expr.Lit.string $(Syntax.mkStrLit s))
  | .byteArray bs =>
      `(LakeJs.Expr.Lit.byteArray
          #[$[(UInt8.ofNat $(bs.toArray.map Lean.quote))],*])
  | .name n => `(LakeJs.Expr.Lit.name $(Lean.quote (String.toName n)))
  | .stringPos p => `(LakeJs.Expr.Lit.stringPos $(Lean.quote p))
  | .substring s a b =>
      `(LakeJs.Expr.Lit.substring $(Syntax.mkStrLit s) $(Lean.quote a) $(Lean.quote b))
  | .stringSlice s a b =>
      `(LakeJs.Expr.Lit.stringSlice $(Syntax.mkStrLit s) $(Lean.quote a)
          $(Lean.quote b))
  | .float bits => `(LakeJs.Expr.Lit.float (Float.ofBits $(Lean.quote bits.toNat)))
  | .float32 bits =>
      `(LakeJs.Expr.Lit.float32 (Float32.ofBits $(Lean.quote bits.toNat)))
  | .floatArray bs =>
      `(LakeJs.Expr.Lit.floatArray
          #[$[(Float.ofBits $(bs.toArray.map fun b => Lean.quote b.toNat))],*])

/-- An operation that is JavaScript's rather than Lean's, as Lean syntax. -/
def opStx (o : SOp) : MacroM (TSyntax `term) := do
  match o with
  | .cast a b => do `(LakeJs.Expr.JsOp.cast $(← tyStx a) $(← tyStx b))
  | .boolAnd => `(LakeJs.Expr.JsOp.boolAnd)
  | .boolOr => `(LakeJs.Expr.JsOp.boolOr)
  | .boolNot => `(LakeJs.Expr.JsOp.boolNot)
  | .boolBEq => `(LakeJs.Expr.JsOp.boolBEq)
  | .charBEq => `(LakeJs.Expr.JsOp.charBEq)
  | .natSubExact => `(LakeJs.Expr.JsOp.natSubExact)
  | .toStr t => do `(LakeJs.Expr.JsOp.toStr $(← tyStx t))

/-- The de Bruijn index `i`, as a variable of the context. -/
def varStx : Nat → MacroM (TSyntax `term)
  | 0 => `(LakeJs.Expr.Var.head)
  | n + 1 => do `(LakeJs.Expr.Var.tail $(← varStx n))

/-- The index `i` of the signature, as a reference to a declaration. -/
def globalStx : Nat → MacroM (TSyntax `term)
  | 0 => `(LakeJs.Expr.GlobalRef.here)
  | n + 1 => do `(LakeJs.Expr.GlobalRef.there $(← globalStx n))

/-- Where a name is bound: in the context, in the signature, or nowhere. -/
def resolve (locals globals : List String) (n : String) : MacroM (TSyntax `term) :=
  match locals.idxOf? n with
  | some i => do `(LakeJs.Expr.Term.var $(← varStx i))
  | none =>
    match globals.idxOf? n with
    | some j => do `(LakeJs.Expr.Term.global $(← globalStx j))
    | none => Macro.throwError s!"`{n}` is neither a variable of the context nor a \
        declaration of the signature"

/-- The names a list of binders introduces, innermost first: a lambda's context is
    `params.reverse ++ Γ`, so the *last* parameter is index 0. -/
def binderNames (ps : List SParam) : List String := (ps.map (·.1)).reverse

mutual

/-- A written term, as Lean syntax. -/
partial def termStx (locals globals : List String) (t : STerm) :
    MacroM (TSyntax `term) := do
  match t with
  | .var n => resolve locals globals n
  | .lit l => do `(LakeJs.Expr.Term.lit $(← litStx l))
  | .extern nm tys => do
      let head : TSyntax `term := ⟨Lean.mkIdent (`LakeJs.Externs ++ Name.mkSimple nm)⟩
      let args ← tys.mapM tyStx
      `(LakeJs.Expr.Term.extern $(← args.foldlM (fun f a => `($f $a)) head))
  | .lam ps b => do
      let body ← termStx (binderNames ps ++ locals) globals b
      `(LakeJs.Expr.Term.lamN (params := [$((← (ps.map (·.2)).mapM tyStx).toArray),*]) $body)
  | .app f args => do
      `(LakeJs.Expr.Term.apN $(← termStx locals globals f)
          $(← spineStx locals globals args))
  | .lamProd ps rets => do
      let body ← spineStx (binderNames ps ++ locals) globals rets
      `(LakeJs.Expr.Term.lamProd (params := [$((← (ps.map (·.2)).mapM tyStx).toArray),*]) $body)
  | .callProd i f args => do
      `(LakeJs.Expr.Term.callProd $(← termStx locals globals f)
          $(← spineStx locals globals args) ⟨$(Lean.quote i), by decide⟩)
  | .op o args => do
      `(LakeJs.Expr.Term.jsOp $(← opStx o) $(← spineStx locals globals args))
  | .letE n ty v b => do
      `(LakeJs.Expr.Term.letE (σ := $(← tyStx ty)) $(← termStx locals globals v)
          $(← termStx (n :: locals) globals b))
  | .ite c t e => do
      `(LakeJs.Expr.Term.ite $(← termStx locals globals c)
          $(← termStx locals globals t) $(← termStx locals globals e))
  | .ctor i ty args => do
      `(LakeJs.Expr.Term.ctor (τ := $(← tyStx ty)) $(Lean.quote i) _ rfl
          $(← spineStx locals globals args))
  | .proj i j e => do
      `(LakeJs.Expr.Term.proj $(← termStx locals globals e) $(Lean.quote i)
          $(Lean.quote j) rfl)
  | .tagOf e => do `(LakeJs.Expr.Term.tagOf $(← termStx locals globals e) rfl)
  | .lazyMk e => do `(LakeJs.Expr.Term.lazyMk $(← termStx locals globals e))
  | .lazyForce e => do `(LakeJs.Expr.Term.lazyForce $(← termStx locals globals e))
  | .caseTag s alts => do
      `(LakeJs.Expr.Term.caseTag $(← termStx locals globals s)
          $(← altsStx locals globals alts) rfl)
  | .loop slots inits b => do
      let body ← bodyStx (binderNames slots ++ locals) globals b
      `(LakeJs.Expr.Term.loop (σs := [$((← (slots.map (·.2)).mapM tyStx).toArray),*])
          $(← spineStx locals globals inits) $body)
  | .joinPoint n ps ret b r => do
      let body ← termStx (binderNames ps ++ locals) globals b
      let rest ← termStx (n :: locals) globals r
      `(LakeJs.Expr.Term.joinPoint
          (params := [$((← (ps.map (·.2)).mapM tyStx).toArray),*])
          (σ := $(← tyStx ret)) $body $rest)
  | .jump n args => do
      match locals.idxOf? n with
      | some i =>
          `(LakeJs.Expr.Term.jump $(← varStx i) $(← spineStx locals globals args))
      | none => Macro.throwError s!"`{n}` is not a join point of the context"

/-- A written spine, as Lean syntax. -/
partial def spineStx (locals globals : List String) (s : SSpine) :
    MacroM (TSyntax `term) := do
  match s with
  | .nil => `(LakeJs.Expr.Spine.nil)
  | .cons t rest => do
      `(LakeJs.Expr.Spine.cons $(← termStx locals globals t)
          $(← spineStx locals globals rest))

/-- The written branches of a case, as Lean syntax. -/
partial def altsStx (locals globals : List String) (a : SAlts) :
    MacroM (TSyntax `term) := do
  match a with
  | .deflt t => do `(LakeJs.Expr.Alts.deflt $(← termStx locals globals t))
  | .cons tag t rest => do
      `(LakeJs.Expr.Alts.cons $(Lean.quote tag) $(← termStx locals globals t)
          $(← altsStx locals globals rest))

/-- A written loop body, as Lean syntax. -/
partial def bodyStx (locals globals : List String) (b : SBody) :
    MacroM (TSyntax `term) := do
  match b with
  | .ret t => do `(LakeJs.Expr.Body.ret $(← termStx locals globals t))
  | .cont args => do `(LakeJs.Expr.Body.cont $(← spineStx locals globals args))
  | .letB n ty v rest => do
      `(LakeJs.Expr.Body.letB (σ := $(← tyStx ty)) $(← termStx locals globals v)
          $(← bodyStx (n :: locals) globals rest))
  | .iteB c t e => do
      `(LakeJs.Expr.Body.iteB $(← termStx locals globals c)
          $(← bodyStx locals globals t) $(← bodyStx locals globals e))
  | .joinPointB n ps ret b r => do
      let body ← termStx (binderNames ps ++ locals) globals b
      let rest ← bodyStx (n :: locals) globals r
      `(LakeJs.Expr.Body.joinPointB
          (params := [$((← (ps.map (·.2)).mapM tyStx).toArray),*])
          (σ := $(← tyStx ret)) $body $rest)

end

/-- A whole fragment, as Lean syntax: the code, ascribed to the type the header gives
    it. -/
def embedStx (e : SEmbed) : MacroM (TSyntax `term) := do
  let sg ← e.glob.mapM fun (n, t) => do
    `(LakeJs.Expr.GlobalDecl.mk $(Syntax.mkStrLit n) $(← tyStx t))
  let ctx ← (e.vars.map (·.2)).mapM tyStx
  let code ← termStx (e.vars.map (·.1)) (e.glob.map (·.1)) e.code
  match e.sig with
  | some τ => do
      `(($code : LakeJs.Expr.Term [$(sg.toArray),*] [$(ctx.toArray),*] $(← tyStx τ)))
  | none => `(($code : LakeJs.Expr.Term [$(sg.toArray),*] [$(ctx.toArray),*] _))

/-- `[LEAN| … ]`: read the fragment, and elaborate the term it writes. -/
@[term_elab leanTermEmbed]
def elabLeanTerm : TermElab := fun stx expected? => do
  match parseEmbed stx[1].getAtomVal with
  | .error msg => throwErrorAt stx msg
  | .ok e =>
      match ← liftMacroM (embedStx e) with
      | s => elabTerm s expected?

end LakeJs.TermElab
