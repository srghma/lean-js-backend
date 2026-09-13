/-!
# JavaScript MiniAST and Pretty Printer

Deterministic JavaScript AST and Wadler-style pretty printer.
-/

namespace Language.JavaScript.Doc

/-- A document. -/
inductive Doc where
  /-- The empty document. -/
  | nil
  /-- Literal text.  It may contain newlines, in which case the current
  column is recomputed from the text. -/
  | text (s : String)
  /-- A space if the enclosing group is flat, a newline otherwise. -/
  | line
  /-- Nothing if the enclosing group is flat, a newline otherwise. -/
  | softline
  /-- Always a newline; it also forces every enclosing group to break. -/
  | hardline
  | cat (a b : Doc)
  /-- Increase the indentation of the newlines inside. -/
  | nest (n : Nat) (d : Doc)
  /-- Print flat if it fits, broken otherwise. -/
  | group (d : Doc)
  /-- Choose according to whether the enclosing group is broken. -/
  | ifBreak (whenBroken whenFlat : Doc)
deriving Inhabited

namespace Doc

instance : Append Doc := ⟨Doc.cat⟩

/-- Concatenate a list of documents, separated by `sep`. -/
def joinWith (sep : Doc) : List Doc → Doc
  | [] => .nil
  | [d] => d
  | d :: ds => d ++ sep ++ joinWith sep ds

/-- Whether the group being laid out is flat or broken. -/
inductive Mode where
  | flat | broken
deriving Inhabited, BEq

/-- The size of a document. -/
def size : Doc → Nat
  | .nil | .text _ | .line | .softline | .hardline => 1
  | .cat a b => size a + size b + 1
  | .nest _ d => size d + 1
  | .group d => size d + 1
  | .ifBreak b f => size b + size f + 1

/-- The size of a work list. -/
def itemsSize : List (Nat × Mode × Doc) → Nat
  | [] => 0
  | (_, _, d) :: rest => d.size + itemsSize rest

/-- Whether pending documents fit in `width` columns. -/
def fits (width : Int) (items : List (Nat × Mode × Doc)) : Bool :=
  if width < 0 then false else
  match items with
  | [] => true
  | (i, m, d) :: rest =>
    match d with
    | .nil => fits width rest
    | .text s =>
        if s.contains '\n' then true else fits (width - s.length) rest
    | .line => match m with
      | .flat => fits (width - 1) rest
      | .broken => true
    | .softline => match m with
      | .flat => fits width rest
      | .broken => true
    | .hardline => match m with
      | .flat => false
      | .broken => true
    | .cat a b => fits width ((i, m, a) :: (i, m, b) :: rest)
    | .nest n d => fits width ((i + n, m, d) :: rest)
    | .group d => fits width ((i, .flat, d) :: rest)
    | .ifBreak b f => match m with
      | .flat => fits width ((i, m, f) :: rest)
      | .broken => fits width ((i, m, b) :: rest)
termination_by itemsSize items
decreasing_by all_goals (simp only [itemsSize, size]; omega)

/-- The column reached after emitting `s` starting at column `col`. -/
private def columnAfter (col : Nat) (s : String) : Nat :=
  s.foldl (fun c ch => if ch == '\n' then 0 else c + 1) col

private def newlineWith (indent : Nat) : String :=
  String.pushn "\n" ' ' indent

private def go (width : Nat) (out : String) (col : Nat) :
    List (Nat × Mode × Doc) → String
  | [] => out
  | (i, m, d) :: rest =>
    match d with
    | .nil => go width out col rest
    | .text s => go width (out ++ s) (columnAfter col s) rest
    | .line => match m with
      | .flat => go width (out ++ " ") (col + 1) rest
      | .broken => go width (out ++ newlineWith i) i rest
    | .softline => match m with
      | .flat => go width out col rest
      | .broken => go width (out ++ newlineWith i) i rest
    | .hardline => go width (out ++ newlineWith i) i rest
    | .cat a b => go width out col ((i, m, a) :: (i, m, b) :: rest)
    | .nest n d => go width out col ((i + n, m, d) :: rest)
    | .group d =>
        let flat := fits ((width : Int) - col) ((i, .flat, d) :: rest)
        go width out col ((i, if flat then .flat else .broken, d) :: rest)
    | .ifBreak b f => match m with
      | .flat => go width out col ((i, m, f) :: rest)
      | .broken => go width out col ((i, m, b) :: rest)
termination_by items => itemsSize items
decreasing_by all_goals (simp only [itemsSize, size]; omega)

/-- Lay out a document, breaking groups that do not fit into `width`
columns. -/
def render (width : Nat) (d : Doc) : String := go width "" 0 [(0, .broken, d)]

end Doc

end Language.JavaScript.Doc

/-! ## Refined component types -/

namespace Language.JavaScript

/-! ## Non-empty strings -/

/-- A string that is known not to be empty. -/
structure NEString where
  /-- The characters of the string. -/
  val : String
  /-- The proof that makes the type non-trivial. -/
  ne : val ≠ ""
deriving DecidableEq

namespace NEString

instance : Inhabited NEString := ⟨⟨"_", by decide⟩⟩
instance : Repr NEString := ⟨fun s _ => repr s.val⟩
instance : ToString NEString := ⟨fun s => s.val⟩
instance : Hashable NEString := ⟨fun s => hash s.val⟩

/-- The non-empty string `s`, or `none` if `s` is empty. -/
def ofString? (s : String) : Option NEString :=
  if h : s ≠ "" then some ⟨s, h⟩ else none

/-- The non-empty string `s`; a placeholder if `s` is empty. -/
def ofString! (s : String) : NEString :=
  if h : s ≠ "" then ⟨s, h⟩ else default

end NEString

/-! ## Non-empty lists -/

/-- A list that is known not to be empty. -/
structure NEList (α : Type) where
  /-- The first element. -/
  hd : α
  /-- The remaining elements. -/
  tl : List α
deriving Repr, BEq, DecidableEq, Inhabited

namespace NEList

variable {α β : Type}

/-- The elements, as an ordinary list. -/
def toList (l : NEList α) : List α := l.hd :: l.tl

/-- A non-empty list from a list, or `none` if it is empty. -/
def ofList? : List α → Option (NEList α)
  | [] => none
  | a :: as => some ⟨a, as⟩

/-- A non-empty list from a list; a singleton placeholder if it is empty. -/
def ofList! [Inhabited α] : List α → NEList α
  | [] => ⟨default, []⟩
  | a :: as => ⟨a, as⟩

end NEList

/-! ## Numeric literals -/

/-- The base a numeric literal is written in. -/
inductive NumBase where
  /-- `0b1010` -/
  | binary
  /-- `0o17`, and the legacy `017` -/
  | octal
  /-- `17`, `1.5`, `1e3` -/
  | decimal
  /-- `0xff` -/
  | hexadecimal
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace NumBase

/-- The radix: 2, 8, 10 or 16. -/
def radix : NumBase → Nat
  | .binary => 2
  | .octal => 8
  | .decimal => 10
  | .hexadecimal => 16

/-- The `0b`/`0o`/`0x` prefix a literal in this base is written with; base
ten literals have none. -/
def prefixText : NumBase → String
  | .binary => "0b"
  | .octal => "0o"
  | .decimal => ""
  | .hexadecimal => "0x"

end NumBase

/-- A JavaScript numeric literal: decimal, radix (base 2/8/16), or BigInt. -/
inductive JSNumber where
  /-- A base ten literal denoting exactly `mantissa * 10 ^ exponent`. -/
  | decimal (mantissa : Nat) (exponent : Int)
  /-- A literal in base two, eight or sixteen. -/
  | radix (base : NumBase) (value : Nat)
  /-- A `BigInt` literal, written in `base`. -/
  | bigint (base : NumBase) (value : Nat)
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace JSNumber

/-- Strip the trailing zeros of a base ten mantissa, moving them into the exponent. -/
private def stripZerosAux : Nat → Nat → Int → Nat × Int
  | 0, m, e => (m, e)
  | fuel + 1, m, e => if m % 10 == 0 then stripZerosAux fuel (m / 10) (e + 1) else (m, e)

/-- Strip the trailing zeros of a base ten mantissa, moving them into the
exponent. -/
private def stripZeros (m : Nat) (e : Int) : Nat × Int :=
  if m == 0 then (0, 0) else stripZerosAux m m e

/-- The canonical form of a literal: the mantissa of a base ten literal has
no trailing zeros, zero is `decimal 0 0`, and a base ten `radix` literal is
a `decimal` one. -/
def normalize : JSNumber → JSNumber
  | .decimal m e => let (m', e') := stripZeros m e; .decimal m' e'
  | .radix .decimal v => let (m', e') := stripZeros v 0; .decimal m' e'
  | .radix b v => .radix b v
  | .bigint b v => .bigint b v

/-- The literal denoting the natural number `n` in base ten. -/
def ofNat (n : Nat) : JSNumber := normalize (.decimal n 0)

instance : OfNat JSNumber n := ⟨ofNat n⟩

/-! ### Rendering -/

/-- The character a digit of value `d < 16` is written with. -/
def digitChar (d : Nat) : Char :=
  if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + d - 10)

/-- The digits of `n` in base `base`, most significant first. -/
def digitsAux (base : Nat) : Nat → Nat → String → String
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      let rest := n / base
      let acc := if rest == 0 then acc else digitsAux base fuel rest acc
      acc.push (digitChar (n % base))

/-- The spelling of `n` in base `base`. -/
def digitsOf (base : Nat) (n : Nat) : String :=
  if n == 0 then "0" else digitsAux base (n + 1) n ""

private def repeatChar (c : Char) (n : Nat) : String := String.pushn "" c n

/-- Render a base ten literal. -/
private def renderDecimal (mantissa : Nat) (exponent : Int) : String :=
  if mantissa == 0 then "0"
  else
    let s := digitsOf 10 mantissa
    let k : Int := Int.ofNat s.length
    -- the value is `0.s * 10 ^ n`
    let n : Int := k + exponent
    if k ≤ n && n ≤ 21 then
      s ++ repeatChar '0' (n - k).toNat
    else if 0 < n && n ≤ 21 then
      -- a digit is one byte wide, so the point falls at the byte index `n`
      String.Pos.Raw.extract s ⟨0⟩ ⟨n.toNat⟩ ++ "." ++
        String.Pos.Raw.extract s ⟨n.toNat⟩ ⟨s.utf8ByteSize⟩
    else if -6 < n && n ≤ 0 then
      "0." ++ repeatChar '0' (-n).toNat ++ s
    else
      let head := String.Pos.Raw.extract s ⟨0⟩ ⟨1⟩
      let tail := String.Pos.Raw.extract s ⟨1⟩ ⟨s.utf8ByteSize⟩
      let e := n - 1
      (if tail.isEmpty then head else head ++ "." ++ tail) ++ "e" ++
        (if e < 0 then "-" ++ toString (-e) else toString e)

/-- The canonical spelling of the literal.  Letters are lower case, there
are no superfluous zeros, and the value is not changed. -/
def render (x : JSNumber) : String :=
  match x.normalize with
  | .decimal m e => renderDecimal m e
  | .radix b v => b.prefixText ++ digitsOf b.radix v
  | .bigint b v => b.prefixText ++ digitsOf b.radix v ++ "n"


instance : ToString JSNumber := ⟨render⟩

end JSNumber

/-! ## Regular expression literals -/

/-- The flags of a regular expression literal. -/
structure RegExpFlags where
  /-- `d`, `hasIndices`. -/
  hasIndices : Bool := false
  /-- `g`, `global`.  A global regular expression object is stateful. -/
  global : Bool := false
  /-- `i`, `ignoreCase`. -/
  ignoreCase : Bool := false
  /-- `m`, `multiline`. -/
  multiline : Bool := false
  /-- `s`, `dotAll`. -/
  dotAll : Bool := false
  /-- `u`, `unicode`. -/
  unicode : Bool := false
  /-- `v`, `unicodeSets`. -/
  unicodeSets : Bool := false
  /-- `y`, `sticky`.  A sticky regular expression object is stateful. -/
  sticky : Bool := false
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace RegExpFlags

/-- The flags, in the canonical order `dgimsuvy`. -/
def render (f : RegExpFlags) : String :=
  (if f.hasIndices then "d" else "") ++
  (if f.global then "g" else "") ++
  (if f.ignoreCase then "i" else "") ++
  (if f.multiline then "m" else "") ++
  (if f.dotAll then "s" else "") ++
  (if f.unicode then "u" else "") ++
  (if f.unicodeSets then "v" else "") ++
  (if f.sticky then "y" else "")

instance : ToString RegExpFlags := ⟨render⟩

end RegExpFlags

/-- A regular expression literal: the pattern between the slashes, and the
flags after the closing one. -/
structure RegExpLit where
  /-- The pattern, without the delimiting slashes.  It cannot be empty:
  `//` starts a comment, and an empty pattern is written `/(?:)/`. -/
  source : NEString
  /-- The flags. -/
  flags : RegExpFlags := {}
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace RegExpLit

/-- The literal, as it is written in source: `/source/flags`. -/
def render (r : RegExpLit) : String :=
  "/" ++ r.source.val ++ "/" ++ r.flags.render

instance : ToString RegExpLit := ⟨render⟩

end RegExpLit

/-! ## Component types -/

/-! ## Operators -/

/-- Binary operators. -/
inductive BinOp where
  | and | or
  /-- `??`, the nullish coalescing operator. -/
  | coalesce
  | bitAnd | bitOr | bitXor
  | eq | neq | strictEq | strictNeq
  | lt | le | gt | ge
  | lsh | rsh | ursh
  | plus | minus | times | divide | mod
  | inOp | instanceOf
deriving Repr, BEq, DecidableEq, Inhabited

/-- Prefix operators. -/
inductive UnaryOp where
  | not | tilde | plus | minus
  | typeof | void | delete
  | preIncr | preDecr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Postfix operators. -/
inductive PostfixOp where
  | incr | decr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Assignment operators. -/
inductive AssignOp where
  | assign
  | plus | minus | times | divide | mod
  | lsh | rsh | ursh
  | bitAnd | bitXor | bitOr
  /-- `&&=` -/
  | logicalAnd
  /-- `||=` -/
  | logicalOr
  /-- `??=` -/
  | coalesce
deriving Repr, BEq, DecidableEq, Inhabited

/-- The keyword introducing a variable declaration. -/
inductive VarKind where
  | var | let_ | const
deriving Repr, BEq, DecidableEq, Inhabited

/-- What kind of method a member of an object or class literal is. -/
inductive MethodKind where
  | normal | generator | get | set
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Import and export clauses -/

/-- One `name` or `name as alias` of an import or export clause. -/
structure Specifier where
  /-- The exported name. -/
  name : NEString
  /-- The local name, when it differs. -/
  alias_ : Option NEString
deriving Repr, BEq, DecidableEq, Inhabited

/-- One import attribute, e.g. `type: "json"`. -/
structure ImportAttr where
  /-- The key. -/
  key : String
  /-- The value. -/
  value : String
deriving Repr, BEq, DecidableEq, Inhabited

end Language.JavaScript

namespace Language.JavaScript.MiniAST

/-! ## Imports -/

/-- `import def, * as ns, { a, b as c } from "mod";`.  Each of the three
clauses is optional, but at least one of them has to be there. -/
structure MiniImportClause where
  /-- The default import, `import def from "mod"`. -/
  default_ : Option NEString
  /-- The namespace import, `import * as ns from "mod"`. -/
  namespace_ : Option NEString
  /-- The named imports, `import { a, b as c } from "mod"`. -/
  named : Option (List Specifier)
  /-- The module the names come from. -/
  mod : NEString
  /-- The import attributes, `with { type: "json" }`. -/
  attrs : List ImportAttr := []
  /-- An import must bind something. -/
  binds : default_.isSome ∨ namespace_.isSome ∨ named.isSome
deriving DecidableEq

instance : Inhabited MiniImportClause :=
  ⟨{ default_ := some default, namespace_ := .none, named := .none, mod := default,
     attrs := [], binds := Or.inl rfl }⟩

namespace MiniImportClause

/-- Build an import clause, checking that it binds something. -/
def mk? (default_ namespace_ : Option NEString) (named : Option (List Specifier))
    (mod : NEString) (attrs : List ImportAttr := []) : Option MiniImportClause :=
  if h : default_.isSome ∨ namespace_.isSome ∨ named.isSome then
    some ⟨default_, namespace_, named, mod, attrs, h⟩
  else
    Option.none

/-- Build an import clause; a placeholder if it binds nothing. -/
def mk! (default_ namespace_ : Option NEString) (named : Option (List Specifier))
    (mod : NEString) (attrs : List ImportAttr := []) : MiniImportClause :=
  (mk? default_ namespace_ named mod attrs).getD default

end MiniImportClause

/-- An `import` declaration. -/
inductive MiniImportDeclaration where
  /-- `import "mod";`, possibly with import attributes. -/
  | bare (mod : NEString) (attrs : List ImportAttr)
  /-- `import ... from "mod";` -/
  | clause (clause : MiniImportClause)
deriving DecidableEq, Inhabited

/-! ## The syntax tree -/

mutual

/-- Expressions. -/
inductive MiniExpr where
  /-- An identifier. -/
  | ident (name : NEString)
  /-- A numeric literal, as the number it denotes. -/
  | number (value : JSNumber)
  /-- A string literal, holding the characters it denotes (not the source text). -/
  | string (value : String)
  /-- A regular expression literal: its pattern and its flags. -/
  | regex (re : RegExpLit)
  | null
  | true_
  | false_
  | this
  /-- `super.name`, the only forms `super` may be written in being a
  member access and a call; `super` on its own is not an expression. -/
  | superDot (name : NEString)
  /-- `super[idx]` -/
  | superIndex (idx : MiniExpr)
  /-- `super(args)`, the call to the constructor of the parent class. -/
  | superCall (args : List MiniExpr)
  /-- `new.target` -/
  | newTarget
  /-- `[a, , b]` -/
  | array (elements : List MiniArrayElement)
  /-- `{ a: 1 }` -/
  | object (properties : List MiniProperty)
  /-- `lhs op rhs`, for an assignment operator `op`. -/
  | assign (lhs : MiniExpr) (op : AssignOp) (rhs : MiniExpr)
  /-- A destructuring assignment, `[a, b] = xs` or `({ a } = o)`: the left
  hand side is a pattern rather than an expression. -/
  | assignPattern (lhs : MiniPattern) (rhs : MiniExpr)
  | await (expr : MiniExpr)
  /-- `callee(args)` -/
  | call (callee : MiniExpr) (args : List MiniExpr)
  /-- `obj.name` -/
  | dot (obj : MiniExpr) (name : NEString)
  /-- `obj.#name`, the access to a private class member. -/
  | privateDot (obj : MiniExpr) (name : NEString)
  /-- A private name used on its own, which only `#x in obj` allows. -/
  | privateName (name : NEString)
  /-- `obj[index]` -/
  | index (obj : MiniExpr) (idx : MiniExpr)
  /-- An optional chain expression. -/
  | chain (base : MiniExpr) (links : NEList MiniChainLink)
  /-- `import.meta` -/
  | importMeta
  /-- A dynamic import, `import(specifier)` or `import(specifier, options)`. -/
  | importCall (specifier : MiniExpr) (options : Option MiniExpr)
  /-- `class name extends heritage { body }` used as an expression. -/
  | classExpr (decorators : List MiniExpr) (name : Option NEString)
      (heritage : Option MiniExpr) (body : List MiniClassElement)
  /-- The comma operator, `lhs, rhs`. -/
  | seq (lhs : MiniExpr) (rhs : MiniExpr)
  | binary (lhs : MiniExpr) (op : BinOp) (rhs : MiniExpr)
  | postfix (expr : MiniExpr) (op : PostfixOp)
  /-- `cond ? thenE : elseE` -/
  | ternary (cond : MiniExpr) (thenE : MiniExpr) (elseE : MiniExpr)
  /-- `(params) => body` -/
  | arrow (params : List MiniParam) (body : MiniArrowBody)
  /-- A function expression; `isAsync` and `isGenerator` select `async` and `*`. -/
  | func (isAsync : Bool) (isGenerator : Bool) (name : Option NEString)
      (params : List MiniParam) (body : List MiniStatement)
  /-- `new callee(args)` -/
  | new (callee : MiniExpr) (args : List MiniExpr)
  /-- `...expr` -/
  | spread (expr : MiniExpr)
  /-- A template literal: an optional tag, the text before the first
  substitution, and one part per substitution. -/
  | template (tag : Option MiniExpr) (head : String) (parts : List MiniTemplatePart)
  | unary (op : UnaryOp) (expr : MiniExpr)
  /-- `yield expr` -/
  | yield (expr : Option MiniExpr)
  /-- `yield* expr` -/
  | yieldFrom (expr : MiniExpr)

/-- One link of an optional chain: a member access or a call, `optional`
saying whether it is written with `?.`. -/
inductive MiniChainLink where
  /-- `.name` or `?.name` -/
  | dot (optional : Bool) (name : NEString)
  /-- `.#name` or `?.#name` -/
  | privateDot (optional : Bool) (name : NEString)
  /-- `[idx]` or `?.[idx]` -/
  | index (optional : Bool) (idx : MiniExpr)
  /-- `(args)` or `?.(args)` -/
  | call (optional : Bool) (args : List MiniExpr)

/-- A binding pattern. -/
inductive MiniPattern where
  /-- `x` -/
  | ident (name : NEString)
  /-- `[a, , b, ...r]` -/
  | array (elements : List MiniArrayPatternElem)
  /-- `{ a, b: c, ...r }`; `rest` is the `...r`, if there is one. -/
  | object (props : List MiniObjectPatternProp) (rest : Option MiniPattern)
  /-- `pat = value`: the value is used when what is matched is `undefined`. -/
  | withDefault (pat : MiniPattern) (value : MiniExpr)
  /-- A target which is not a binding, as in `[o.p] = xs`: the expression
  the value is assigned to.  A declaration cannot have one. -/
  | target (expr : MiniExpr)

/-- One element of an array pattern. -/
inductive MiniArrayPatternElem where
  /-- An elision, as in `[a, , b]`. -/
  | hole
  | elem (pat : MiniPattern)
  /-- `...rest`, which JavaScript only allows last. -/
  | rest (pat : MiniPattern)

/-- One property of an object pattern, `{ key: value }`; `{ a }` is the
property whose key is `a` and whose value is the pattern `a`. -/
structure MiniObjectPatternProp where
  /-- The property read from the object. -/
  key : MiniPropertyName
  /-- The pattern the property is matched against. -/
  value : MiniPattern

/-- A parameter of a function, an arrow or a method: a pattern, or a rest
parameter, which JavaScript only allows last. -/
inductive MiniParam where
  /-- An ordinary parameter, `x`, `x = 1` or `{ a, b }`. -/
  | plain (pat : MiniPattern)
  /-- `...rest` -/
  | rest (pat : MiniPattern)

/-- An element of an array literal; `hole` is an elision, as in `[1, , 2]`. -/
inductive MiniArrayElement where
  | elem (expr : MiniExpr)
  | hole

/-- The body of an arrow function. -/
inductive MiniArrowBody where
  | expr (expr : MiniExpr)
  | block (body : List MiniStatement)

/-- The `${...}` substitution of a template literal together with the text
following it. -/
structure MiniTemplatePart where
  /-- The substituted expression. -/
  expr : MiniExpr
  /-- The template text following the substitution. -/
  suffix : String

/-- The name of a property or method. -/
inductive MiniPropertyName where
  | ident (name : NEString)
  /-- A private name, `#x`, without its `#`; only a class member has one. -/
  | private_ (name : NEString)
  /-- A quoted name, holding the characters it denotes. -/
  | string (value : String)
  /-- A numeric name, as the number it denotes. -/
  | number (value : JSNumber)
  /-- `[expr]` -/
  | computed (expr : MiniExpr)

/-- A member of an object literal. -/
inductive MiniProperty where
  | keyValue (key : MiniPropertyName) (value : MiniExpr)
  /-- `{ x }` -/
  | shorthand (name : NEString)
  /-- `{ ...rest }` -/
  | spread (expr : MiniExpr)
  | method (kind : MethodKind) (key : MiniPropertyName) (params : List MiniParam)
      (body : List MiniStatement)

/-- A member of a class body: a method, a field or a static block. -/
inductive MiniClassElement where
  /-- A method, a generator, a getter or a setter. -/
  | method (decorators : List MiniExpr) (isStatic : Bool) (kind : MethodKind)
      (key : MiniPropertyName) (params : List MiniParam) (body : List MiniStatement)
  /-- A field, `x = 1;`, `#x;` or `static x = 1;`. -/
  | field (decorators : List MiniExpr) (isStatic : Bool) (key : MiniPropertyName)
      (init : Option MiniExpr)
  /-- A static initialisation block, `static { ... }`. -/
  | staticBlock (body : List MiniStatement)

/-- One declarator of a `var`/`let`/`const` statement. -/
structure MiniDeclarator where
  /-- The name, or destructuring pattern, being bound. -/
  lhs : MiniPattern
  /-- The initialiser, if any. -/
  init : Option MiniExpr

/-- The first clause of a `for (;;)` statement. -/
inductive MiniForInit where
  | none
  | expr (expr : MiniExpr)
  | decl (kind : VarKind) (decls : NEList MiniDeclarator)

/-- The binder of a `for (... in ...)` or `for (... of ...)` statement:
either an assignment to something which already exists, or a declaration. -/
inductive MiniForHead where
  | pattern (lhs : MiniPattern)
  | decl (kind : VarKind) (lhs : MiniPattern)

/-- One `case`/`default` of a `switch`. -/
inductive MiniSwitchCase where
  | case (test : MiniExpr) (body : List MiniStatement)
  | default (body : List MiniStatement)

/-- The `catch` clause of a `try`; `guard` is the (non standard) `if` guard. -/
structure MiniCatchClause where
  /-- The bound exception. -/
  param : MiniPattern
  /-- The guard of a `catch (e if cond)` clause. -/
  guard : Option MiniExpr
  /-- The body. -/
  body : List MiniStatement

/-- The `finally` clause of a `try`. -/
inductive MiniFinallyClause where
  | none
  | some (body : List MiniStatement)

/-- What follows the block of a `try`.  A `try` needs at least one `catch`
or a `finally`, which this makes structurally impossible to violate. -/
inductive MiniTryTail where
  /-- At least one `catch` clause, and possibly a `finally`. -/
  | catches (catches : NEList MiniCatchClause) (fin : MiniFinallyClause)
  /-- No `catch` clause, only a `finally`. -/
  | finallyOnly (body : List MiniStatement)

/-- Statements. -/
inductive MiniStatement where
  | block (body : List MiniStatement)
  | break_ (label : Option NEString)
  | continue_ (label : Option NEString)
  /-- `class name extends heritage { body }` as a declaration. -/
  | classDecl (decorators : List MiniExpr) (name : NEString) (heritage : Option MiniExpr)
      (body : List MiniClassElement)
  /-- `var`/`let`/`const` declaration; it declares at least one name. -/
  | decl (kind : VarKind) (decls : NEList MiniDeclarator)
  /-- `using x = e;` and `await using x = e;`, the explicit resource
  management declarations; `isAwait` selects the second. -/
  | using_ (isAwait : Bool) (decls : NEList MiniDeclarator)
  | doWhile (body : MiniStatement) (cond : MiniExpr)
  | for_ (init : MiniForInit) (cond : Option MiniExpr) (step : Option MiniExpr)
      (body : MiniStatement)
  | forIn (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
  | forOf (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
  | funcDecl (isAsync : Bool) (isGenerator : Bool) (name : NEString)
      (params : List MiniParam) (body : List MiniStatement)
  | if_ (cond : MiniExpr) (thenS : MiniStatement) (elseS : Option MiniStatement)
  | labelled (label : NEString) (stmt : MiniStatement)
  | empty
  /-- An expression statement. -/
  | expr (expr : MiniExpr)
  | return_ (expr : Option MiniExpr)
  | switch (disc : MiniExpr) (cases : List MiniSwitchCase)
  | throw (expr : MiniExpr)
  | try_ (body : List MiniStatement) (tail : MiniTryTail)
  | while_ (cond : MiniExpr) (body : MiniStatement)
  | with_ (obj : MiniExpr) (body : MiniStatement)

/-- An `export` declaration. -/
inductive MiniExportDeclaration where
  /-- `export { a } from "mod";`, possibly with import attributes. -/
  | fromClause (specs : List Specifier) (mod : NEString) (attrs : List ImportAttr)
  /-- `export { a };` -/
  | locals (specs : List Specifier)
  /-- `export * from "mod";` and `export * as ns from "mod";`; `alias_` is
  the `ns` of the second form. -/
  | all (alias_ : Option NEString) (mod : NEString) (attrs : List ImportAttr)
  /-- `export default <expression>;` -/
  | defaultExpr (expr : MiniExpr)
  /-- `export <declaration>` -/
  | decl (stmt : MiniStatement)

/-- A top level item: a statement, or an `import`/`export` declaration. -/
inductive MiniModuleItem where
  | stmt (stmt : MiniStatement)
  | importDecl (decl : MiniImportDeclaration)
  | exportDecl (decl : MiniExportDeclaration)

end

/-! ## Default values -/

instance : Inhabited MiniExpr := ⟨.null⟩
instance : Inhabited MiniStatement := ⟨.empty⟩
instance : Inhabited MiniPattern := ⟨.ident default⟩
instance : Inhabited MiniArrayPatternElem := ⟨.hole⟩
instance : Inhabited MiniObjectPatternProp := ⟨⟨.ident default, .ident default⟩⟩
instance : Inhabited MiniChainLink := ⟨.dot true default⟩
instance : Inhabited MiniParam := ⟨.plain (.ident default)⟩
instance : Inhabited MiniArrayElement := ⟨.hole⟩
instance : Inhabited MiniArrowBody := ⟨.block []⟩
instance : Inhabited MiniTemplatePart := ⟨⟨default, ""⟩⟩
instance : Inhabited MiniPropertyName := ⟨.ident default⟩
instance : Inhabited MiniProperty := ⟨.shorthand default⟩
instance : Inhabited MiniClassElement := ⟨.staticBlock []⟩
instance : Inhabited MiniDeclarator := ⟨⟨.ident default, none⟩⟩
instance : Inhabited MiniForInit := ⟨.none⟩
instance : Inhabited MiniForHead := ⟨.pattern default⟩
instance : Inhabited MiniSwitchCase := ⟨.default []⟩
instance : Inhabited MiniCatchClause := ⟨⟨.ident default, none, []⟩⟩
instance : Inhabited MiniFinallyClause := ⟨.none⟩
instance : Inhabited MiniTryTail := ⟨.finallyOnly []⟩
instance : Inhabited MiniExportDeclaration := ⟨.locals []⟩
instance : Inhabited MiniModuleItem := ⟨.stmt default⟩

/-- A whole program: a list of top level items. -/
structure MiniProgram where
  /-- The top level items. -/
  items : List MiniModuleItem
deriving Inhabited

/-! ## Equality -/

deriving instance BEq for MiniExpr, MiniStatement, MiniModuleItem

instance : BEq MiniProgram := ⟨fun a b => a.items == b.items⟩

/-! ## String literals -/

/-- Push the spelling of `c` in a literal quoted with `quote` onto `acc`. -/
private def pushEscaped (quote : Char) (acc : String) (c : Char) : String :=
  if c == quote then (acc.push '\\').push quote
  else if c == '\\' then (acc.push '\\').push '\\'
  else if c == '\n' then (acc.push '\\').push 'n'
  else if c == '\r' then (acc.push '\\').push 'r'
  else if c == '\t' then (acc.push '\\').push 't'
  else if c.toNat == 8 then (acc.push '\\').push 'b'
  else if c.toNat == 12 then (acc.push '\\').push 'f'
  else if c.toNat == 11 then (acc.push '\\').push 'v'
  else if c.toNat < 0x20 || c.toNat == 0x7F then
    let hex := Nat.toDigits 16 c.toNat
    let acc := (acc.push '\\').push 'x'
    let acc := if hex.length == 1 then acc.push '0' else acc
    hex.foldl (fun acc d => acc.push d) acc
  else acc.push c

/-- Render a string value as a JavaScript literal. -/
def encodeStringLiteral (value : String) : String :=
  let (doubles, singles) :=
    value.foldl (fun (n : Nat × Nat) c =>
      if c == '"' then (n.1 + 1, n.2) else if c == '\'' then (n.1, n.2 + 1) else n) (0, 0)
  let quote := if doubles > singles then '\'' else '"'
  (value.foldl (pushEscaped quote) (String.singleton quote)).push quote

open Language.JavaScript.Doc

namespace Printer

/-- The line width the layout aims at. -/
def defaultWidth : Nat := 80

/-- The number of spaces of one indentation step. -/
def indentWidth : Nat := 2

private def t (s : String) : Doc := .text s

private def parens (d : Doc) : Doc := t "(" ++ d ++ t ")"

/-! ## Operators -/

def binOpText : BinOp → String
  | .and => "&&" | .or => "||" | .coalesce => "??"
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .eq => "==" | .neq => "!=" | .strictEq => "===" | .strictNeq => "!=="
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .lsh => "<<" | .rsh => ">>" | .ursh => ">>>"
  | .plus => "+" | .minus => "-" | .times => "*" | .divide => "/" | .mod => "%"
  | .inOp => "in" | .instanceOf => "instanceof"

/-- Binary operator precedence level; higher binds tighter. -/
def binOpPrec : BinOp → Nat
  | .or | .coalesce => 4
  | .and => 5
  | .bitOr => 6
  | .bitXor => 7
  | .bitAnd => 8
  | .eq | .neq | .strictEq | .strictNeq => 9
  | .lt | .le | .gt | .ge | .inOp | .instanceOf => 10
  | .lsh | .rsh | .ursh => 11
  | .plus | .minus => 12
  | .times | .divide | .mod => 13

def unaryOpText : UnaryOp → String
  | .not => "!" | .tilde => "~" | .plus => "+" | .minus => "-"
  | .typeof => "typeof " | .void => "void " | .delete => "delete "
  | .preIncr => "++" | .preDecr => "--"

def postfixOpText : PostfixOp → String
  | .incr => "++" | .decr => "--"

/-- `??` cannot be mixed with `&&` or `||` without parentheses. -/
def logicalMix (op : BinOp) (child : MiniExpr) : Bool :=
  match child with
  | .binary _ childOp _ =>
      (op == .coalesce && (childOp == .and || childOp == .or))
        || ((op == .and || op == .or) && childOp == .coalesce)
  | _ => false

def assignOpText : AssignOp → String
  | .assign => "="
  | .logicalAnd => "&&=" | .logicalOr => "||=" | .coalesce => "??="
  | .plus => "+=" | .minus => "-=" | .times => "*=" | .divide => "/=" | .mod => "%="
  | .lsh => "<<=" | .rsh => ">>=" | .ursh => ">>>="
  | .bitAnd => "&=" | .bitXor => "^=" | .bitOr => "|="

def varKindText : VarKind → String
  | .var => "var" | .let_ => "let" | .const => "const"

/-! ## Precedence -/

/-- Precedence of an expression (1 for comma to 17 for primary). -/
def exprPrec : MiniExpr → Nat
  | .seq _ _ => 1
  | .assign .. | .assignPattern .. | .arrow .. | .yield _ | .yieldFrom _ | .spread _ => 2
  | .ternary .. => 3
  | .binary _ op _ => binOpPrec op
  | .unary .. | .await _ => 14
  | .postfix .. => 15
  | .call .. | .dot .. | .privateDot .. | .index .. | .new .. | .chain .. | .importCall .. => 16
  | .superDot .. | .superIndex .. | .superCall .. => 16
  | .template (some _) _ _ => 16
  | _ => 17

/-- Can this expression be the callee of a `new` without parentheses?  It
has to be a member expression that does not itself contain a call. -/
def newCalleeOk : MiniExpr → Bool
  | .ident _ | .this => true
  | .dot o _ => newCalleeOk o
  | .privateDot o _ => newCalleeOk o
  | .index o _ => newCalleeOk o
  | _ => false

/-- Would printing `op` directly in front of `e` run the two operators
together, as `-` in front of `-1` would give `--1`? -/
def unaryClash (op : UnaryOp) (e : MiniExpr) : Bool :=
  match e with
  | .unary op' _ =>
      let plusLike (o : UnaryOp) := o == .plus || o == .preIncr
      let minusLike (o : UnaryOp) := o == .minus || o == .preDecr
      (plusLike op && plusLike op') || (minusLike op && minusLike op')
  | _ => false

/-- Whether an expression needs parentheses when printed as a statement. -/
def needsStatementParens : MiniExpr → Bool
  | .object _ => true
  | .func .. => true
  | .classExpr .. => true
  -- the callee of a call is parenthesised already when it is a function
  | .call (.func ..) _ => false
  | .call f _ => needsStatementParens f
  | .index (.ident n) _ => n.val == "let"
  | .dot o _ | .privateDot o _ | .index o _ | .postfix o _ | .chain o _ =>
      needsStatementParens o
  -- `{ a } = o` at the start of a statement would be read as a block
  | .assignPattern (.object ..) _ => true
  | .binary l _ _ | .seq l _ | .assign l _ _ => needsStatementParens l
  | .ternary c _ _ => needsStatementParens c
  | .template (some tag) _ _ => needsStatementParens tag
  | _ => false

/-! ## Layout helpers -/

/-- A bracketed, comma-separated list. -/
def sepList (opener closer : String) (spaced : Bool) (trailingComma : Bool)
    (items : List Doc) : Doc :=
  if items.isEmpty then t (opener ++ closer)
  else
    let br : Doc := if spaced then .line else .softline
    let trailer : Doc := if trailingComma then .ifBreak (t ",") .nil else .nil
    .group (t opener ++ .nest indentWidth (br ++ Doc.joinWith (t "," ++ .line) items ++ trailer)
      ++ br ++ t closer)

/-! ## The printer -/

/-- Parenthesise `d` when `cond` holds. -/
def parenIf (cond : Bool) (d : Doc) : Doc := if cond then parens d else d

/-- An expression in a position that requires precedence `minPrec`, given
the document the expression itself prints as. -/
def exprDocWith (minPrec : Nat) (e : MiniExpr) (d : Doc) : Doc :=
  parenIf (exprPrec e < minPrec) d

/-- The object of a `.` or `[]` access, given the document it prints as. -/
def memberObjectWith (e : MiniExpr) (d : Doc) : Doc :=
  match e with
  | .number n => parens (t n.render)
  -- a chain written as the object of a plain access was parenthesised in the
  -- source, and has to stay so: `(a?.b).c` is not `a?.b.c`
  | .chain _ _ => parens d
  | _ => exprDocWith 16 e d

/-- The callee of a call, parenthesised if a function expression. -/
def calleeWith (e : MiniExpr) (d : Doc) : Doc :=
  match e with
  | .func .. => parens d
  | _ => memberObjectWith e d

/-- A parameter list, given the documents of the parameters. -/
def paramsDocOf (params : List MiniParam) (items : List Doc) : Doc :=
  let restLast := match params.getLast? with
    | some (.rest _) => true
    | _ => false
  sepList "(" ")" false (!restLast) items

/-- An array literal, given the documents of its elements. -/
def arrayDocOf (els : List MiniArrayElement) (items : List Doc) : Doc :=
  if els.isEmpty then t "[]"
  else
    let lastIsHole := match els.getLast? with
      | some .hole => true
      | _ => false
    -- an elision at the end needs its comma in both layouts
    let trailer : Doc := if lastIsHole then t "," else .ifBreak (t ",") .nil
    .group (t "[" ++ .nest indentWidth
      (.softline ++ Doc.joinWith (t "," ++ .line) items ++ trailer) ++ .softline ++ t "]")

/-- An array pattern, given the documents of its elements. -/
def arrayPatternDocOf (els : List MiniArrayPatternElem) (items : List Doc) : Doc :=
  if els.isEmpty then t "[]"
  else
    let trailer : Doc := match els.getLast? with
      | some .hole => t ","
      | some (.rest _) => Doc.nil
      | _ => .ifBreak (t ",") .nil
    .group (t "[" ++ .nest indentWidth
      (.softline ++ Doc.joinWith (t "," ++ .line) items ++ trailer) ++ .softline ++ t "]")

/-- An object pattern, given the documents of its properties and of its
rest element; a trailing comma may not follow the rest element. -/
def objectPatternDocOf (rest : Option MiniPattern) (items : List Doc) : Doc :=
  sepList "{" "}" true rest.isNone items

/-- May the property `key: value` of an object pattern be written in the
short form, as `{ a }` or `{ a = 1 }`? -/
def patternShorthand (key : MiniPropertyName) (value : MiniPattern) : Bool :=
  match key, value with
  | .ident k, .ident v => k == v
  | .ident k, .withDefault (.ident v) _ => k == v
  | _, _ => false

/-- The decorators in front of a class or of a class member, given their
documents. -/
def decoratorsPrefix (items : List Doc) : Doc :=
  Doc.joinWith Doc.nil (items.map (fun d => d ++ t " "))

/-- A brace enclosed statement list, given the document of the list. -/
def blockDocOf (body : List MiniStatement) (inner : Doc) : Doc :=
  if body.isEmpty then t "{}"
  else t "{" ++ .nest indentWidth (.hardline ++ inner) ++ .hardline ++ t "}"

/-- A class body, given the documents of its members. -/
def classBodyOf (body : List MiniClassElement) (items : List Doc) : Doc :=
  if body.isEmpty then t "{}"
  else
    t "{" ++ .nest indentWidth (.hardline ++ Doc.joinWith .hardline items)
      ++ .hardline ++ t "}"

/-- A class, given the documents of its decorators, of its heritage clause
(`" extends …"`, or nothing) and of its members. -/
def classDocOf (decorators : List Doc) (name : Option NEString) (heritage : Doc)
    (body : List MiniClassElement) (items : List Doc) : Doc :=
  decoratorsPrefix decorators
    ++ t "class"
    ++ (match name with | none => Doc.nil | some n => t (" " ++ n.val))
    ++ heritage ++ t " " ++ classBodyOf body items

/-- A function, given the documents of its parameters and of its body. -/
def functionDocOf (isAsync isGen : Bool) (name : Option NEString)
    (params : List MiniParam) (paramItems : List Doc)
    (body : List MiniStatement) (bodyInner : Doc) : Doc :=
  t (if isAsync then "async function" else "function")
    ++ t (if isGen then "*" else "")
    ++ (match name with | none => t " " | some n => t (" " ++ n.val))
    ++ paramsDocOf params paramItems ++ t " " ++ blockDocOf body bodyInner

/-- A method, given the documents of its name, its parameters and its
body. -/
def methodDocOf (kind : MethodKind) (key : Doc)
    (params : List MiniParam) (paramItems : List Doc)
    (body : List MiniStatement) (bodyInner : Doc) : Doc :=
  let prefix_ := match kind with
    | .normal => ""
    | .generator => "*"
    | .get => "get "
    | .set => "set "
  t prefix_ ++ key ++ paramsDocOf params paramItems ++ t " " ++ blockDocOf body bodyInner

/-- The body attached to a control flow header. -/
def attachedBodyWith (s : MiniStatement) (d : Doc) : Doc :=
  match s with
  | .block _ => t " " ++ d
  | .empty => t ";"
  | _ => .group (.nest indentWidth (.line ++ d))

/-- The statements of one `case` of a `switch`, given the document their
list prints as. -/
def caseBodyWith (body : List MiniStatement) (inner : Doc) : Doc :=
  match body with
  | [] => Doc.nil
  | [.block _] => t " " ++ inner
  | _ => .nest indentWidth (.hardline ++ inner)

mutual

/-- An expression, without the parentheses its context may require. -/
def exprCore : MiniExpr → Doc
  | .ident n => t n.val
  | .number n => t n.render
  | .string v => t (encodeStringLiteral v)
  | .regex r => t r.render
  | .null => t "null"
  | .true_ => t "true"
  | .false_ => t "false"
  | .this => t "this"
  | .superDot n => t ("super." ++ n.val)
  | .superIndex i => t "super[" ++ exprDocWith 1 i (exprCore i) ++ t "]"
  | .superCall args => t "super" ++ sepList "(" ")" false true (argDocs args)
  | .newTarget => t "new.target"
  | .array els => arrayDocOf els (arrayItemDocs els)
  | .object props => sepList "{" "}" true true (propertyDocs props)
  | .assign l op r =>
      exprDocWith 16 l (exprCore l) ++ t (" " ++ assignOpText op ++ " ")
        ++ exprDocWith 2 r (exprCore r)
  | .assignPattern l r =>
      patternDoc l ++ t " = " ++ exprDocWith 2 r (exprCore r)
  | .await e => t "await " ++ exprDocWith 14 e (exprCore e)
  | .call f args =>
      calleeWith f (exprCore f) ++ sepList "(" ")" false true (argDocs args)
  | .dot o n => memberObjectWith o (exprCore o) ++ t ("." ++ n.val)
  | .privateDot o n => memberObjectWith o (exprCore o) ++ t (".#" ++ n.val)
  | .privateName n => t ("#" ++ n.val)
  | .index o i =>
      memberObjectWith o (exprCore o) ++ t "[" ++ exprDocWith 1 i (exprCore i) ++ t "]"
  | .chain base ⟨hd, tl⟩ =>
      memberObjectWith base (exprCore base) ++ chainLinksAux (chainLinkDoc hd) tl
  | .importMeta => t "import.meta"
  | .importCall spec none =>
      t "import(" ++ exprDocWith 2 spec (exprCore spec) ++ t ")"
  | .importCall spec (some o) =>
      t "import(" ++ exprDocWith 2 spec (exprCore spec) ++ t ", "
        ++ exprDocWith 2 o (exprCore o) ++ t ")"
  | .classExpr decorators name heritage body =>
      classDocOf (decoratorDocs decorators) name
        (match heritage with
          | none => Doc.nil
          | some e => t " extends " ++ exprDocWith 16 e (exprCore e))
        body (classElemDocs body)
  | .seq l r => exprDocWith 1 l (exprCore l) ++ t ", " ++ exprDocWith 2 r (exprCore r)
  | .binary l op r =>
      let p := binOpPrec op
      .group (parenIf (logicalMix op l) (exprDocWith p l (exprCore l)) ++ t (" " ++ binOpText op)
        ++ .nest indentWidth
            (.line ++ parenIf (logicalMix op r) (exprDocWith (p + 1) r (exprCore r))))
  | .postfix e op => exprDocWith 16 e (exprCore e) ++ t (postfixOpText op)
  | .ternary c a b =>
      .group (exprDocWith 4 c (exprCore c) ++ .nest indentWidth
        (.line ++ t "? " ++ exprDocWith 2 a (exprCore a)
          ++ .line ++ t ": " ++ exprDocWith 2 b (exprCore b)))
  | .arrow params body =>
      paramsDocOf params (paramDocs params) ++ t " => " ++ arrowBodyDoc body
  | .func isAsync isGen name params body =>
      functionDocOf isAsync isGen name params (paramDocs params) body
        (Doc.joinWith .hardline (statementDocs body))
  | .new callee args =>
      t "new " ++ (if newCalleeOk callee then exprCore callee else parens (exprCore callee))
        ++ sepList "(" ")" false true (argDocs args)
  | .spread e => t "..." ++ exprDocWith 2 e (exprCore e)
  | .template tag head parts =>
      (match tag with
        | none => Doc.nil
        | some tg => exprDocWith 16 tg (exprCore tg))
        ++ t "`" ++ t head ++ templatePartsAux .nil parts ++ t "`"
  | .unary op e =>
      t (unaryOpText op)
        ++ (if unaryClash op e then parens (exprCore e) else exprDocWith 14 e (exprCore e))
  | .yield none => t "yield"
  | .yield (some e) => t "yield " ++ exprDocWith 2 e (exprCore e)
  | .yieldFrom e => t "yield* " ++ exprDocWith 2 e (exprCore e)

/-- The arguments of a call or of a `new`. -/
def argDocs : List MiniExpr → List Doc
  | [] => []
  | a :: rest => exprDocWith 2 a (exprCore a) :: argDocs rest

/-- One link of an optional chain. -/
def chainLinkDoc : MiniChainLink → Doc
  | .dot optional n => t ((if optional then "?." else ".") ++ n.val)
  | .privateDot optional n => t ((if optional then "?.#" else ".#") ++ n.val)
  | .index optional i =>
      t (if optional then "?.[" else "[") ++ exprDocWith 1 i (exprCore i) ++ t "]"
  | .call optional args =>
      t (if optional then "?." else "") ++ sepList "(" ")" false true (argDocs args)

/-- The links of an optional chain, appended to the document of the base. -/
def chainLinksAux (acc : Doc) : List MiniChainLink → Doc
  | [] => acc
  | l :: rest => chainLinksAux (acc ++ chainLinkDoc l) rest

/-- The decorators of a class or of a class member, each written `@expr`. -/
def decoratorDocs : List MiniExpr → List Doc
  | [] => []
  | d :: rest => (t "@" ++ exprDocWith 16 d (exprCore d)) :: decoratorDocs rest

/-- A binding pattern. -/
def patternDoc : MiniPattern → Doc
  | .ident n => t n.val
  | .array els => arrayPatternDocOf els (arrayPatternElemDocs els)
  | .object props none => objectPatternDocOf none (objectPatternPropDocs props)
  | .object props (some r) =>
      objectPatternDocOf (some r)
        (objectPatternPropDocs props ++ [t "..." ++ patternDoc r])
  | .withDefault p v => patternDoc p ++ t " = " ++ exprDocWith 2 v (exprCore v)
  | .target e => exprDocWith 2 e (exprCore e)

def arrayPatternElemDocs : List MiniArrayPatternElem → List Doc
  | [] => []
  | .hole :: rest => Doc.nil :: arrayPatternElemDocs rest
  | .elem p :: rest => patternDoc p :: arrayPatternElemDocs rest
  | .rest p :: rest => (t "..." ++ patternDoc p) :: arrayPatternElemDocs rest

def objectPatternPropDocs : List MiniObjectPatternProp → List Doc
  | [] => []
  | ⟨key, value⟩ :: rest =>
      (if patternShorthand key value then patternDoc value
        else propertyNameDoc key ++ t ": " ++ patternDoc value)
        :: objectPatternPropDocs rest

/-- The elements of an array literal; an elision prints as nothing. -/
def arrayItemDocs : List MiniArrayElement → List Doc
  | [] => []
  | .elem e :: rest => exprDocWith 2 e (exprCore e) :: arrayItemDocs rest
  | .hole :: rest => Doc.nil :: arrayItemDocs rest

/-- The `${…}` substitutions of a template literal, and the text between
them. -/
def templatePartsAux (acc : Doc) : List MiniTemplatePart → Doc
  | [] => acc
  | ⟨e, suffix⟩ :: rest =>
      templatePartsAux
        (acc ++ (t "${" ++ exprDocWith 1 e (exprCore e) ++ t "}" ++ t suffix)) rest

def propertyNameDoc : MiniPropertyName → Doc
  | .ident n => t n.val
  | .private_ n => t ("#" ++ n.val)
  | .string v => t (encodeStringLiteral v)
  | .number n => t n.render
  | .computed e => t "[" ++ exprDocWith 2 e (exprCore e) ++ t "]"

def propertyDoc : MiniProperty → Doc
  | .keyValue k v => propertyNameDoc k ++ t ": " ++ exprDocWith 2 v (exprCore v)
  | .shorthand n => t n.val
  | .spread e => t "..." ++ exprDocWith 2 e (exprCore e)
  | .method kind key params body =>
      methodDocOf kind (propertyNameDoc key) params (paramDocs params) body
        (Doc.joinWith .hardline (statementDocs body))

def propertyDocs : List MiniProperty → List Doc
  | [] => []
  | p :: rest => propertyDoc p :: propertyDocs rest

/-- One parameter. -/
def paramDoc : MiniParam → Doc
  | .plain p => patternDoc p
  | .rest p => t "..." ++ patternDoc p

def paramDocs : List MiniParam → List Doc
  | [] => []
  | p :: rest => paramDoc p :: paramDocs rest

def classElemDoc : MiniClassElement → Doc
  | .method decorators isStatic kind key params body =>
      decoratorsPrefix (decoratorDocs decorators)
        ++ (if isStatic then t "static " else Doc.nil)
        ++ methodDocOf kind (propertyNameDoc key) params (paramDocs params) body
            (Doc.joinWith .hardline (statementDocs body))
  | .field decorators isStatic key init =>
      decoratorsPrefix (decoratorDocs decorators)
        ++ (if isStatic then t "static " else Doc.nil)
        ++ propertyNameDoc key
        ++ (match init with
            | none => Doc.nil
            | some e => t " = " ++ exprDocWith 2 e (exprCore e))
        ++ t ";"
  | .staticBlock body =>
      t "static " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body))

def classElemDocs : List MiniClassElement → List Doc
  | [] => []
  | el :: rest => classElemDoc el :: classElemDocs rest

def arrowBodyDoc : MiniArrowBody → Doc
  | .block body => blockDocOf body (Doc.joinWith .hardline (statementDocs body))
  | .expr (.object props) => parens (sepList "{" "}" true true (propertyDocs props))
  | .expr e => exprDocWith 2 e (exprCore e)

def declaratorDoc : MiniDeclarator → Doc
  | ⟨lhs, init⟩ =>
      patternDoc lhs ++ (match init with
        | none => Doc.nil
        | some e => t " = " ++ exprDocWith 2 e (exprCore e))

def declaratorDocs : List MiniDeclarator → List Doc
  | [] => []
  | d :: rest => declaratorDoc d :: declaratorDocs rest

def forInitDoc : MiniForInit → Doc
  | .none => Doc.nil
  | .expr e => exprDocWith 1 e (exprCore e)
  | .decl kind ⟨hd, tl⟩ =>
      t (varKindText kind ++ " ")
        ++ Doc.joinWith (t ", ") (declaratorDoc hd :: declaratorDocs tl)

def forHeadDoc : MiniForHead → Doc
  | .pattern p => patternDoc p
  | .decl kind lhs => t (varKindText kind ++ " ") ++ patternDoc lhs

def switchCaseDoc : MiniSwitchCase → Doc
  | .case test body =>
      t "case " ++ exprDocWith 2 test (exprCore test) ++ t ":"
        ++ caseBodyWith body (Doc.joinWith .hardline (statementDocs body))
  | .default body =>
      t "default:" ++ caseBodyWith body (Doc.joinWith .hardline (statementDocs body))

def switchCaseDocs : List MiniSwitchCase → List Doc
  | [] => []
  | c :: rest => switchCaseDoc c :: switchCaseDocs rest

def catchDoc : MiniCatchClause → Doc
  | ⟨param, guard, body⟩ =>
      t " catch (" ++ patternDoc param
        ++ (match guard with
            | none => Doc.nil
            | some g => t " if " ++ exprDocWith 1 g (exprCore g))
        ++ t ") " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body))

def catchDocsAux (acc : Doc) : List MiniCatchClause → Doc
  | [] => acc
  | c :: rest => catchDocsAux (acc ++ catchDoc c) rest

def tryTailDoc : MiniTryTail → Doc
  | .finallyOnly body =>
      t " finally " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body))
  | .catches ⟨hd, tl⟩ fin =>
      catchDocsAux (Doc.nil ++ catchDoc hd) tl
        ++ (match fin with
            | .none => Doc.nil
            | .some body =>
                t " finally " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body)))

def statementDoc : MiniStatement → Doc
  | .block body => blockDocOf body (Doc.joinWith .hardline (statementDocs body))
  | .break_ none => t "break;"
  | .break_ (some l) => t ("break " ++ l.val ++ ";")
  | .continue_ none => t "continue;"
  | .continue_ (some l) => t ("continue " ++ l.val ++ ";")
  | .classDecl decorators name heritage body =>
      classDocOf (decoratorDocs decorators) (some name)
        (match heritage with
          | none => Doc.nil
          | some e => t " extends " ++ exprDocWith 16 e (exprCore e))
        body (classElemDocs body)
  | .decl kind ⟨hd, tl⟩ =>
      t (varKindText kind ++ " ")
        ++ .group (Doc.joinWith (t "," ++ .line) (declaratorDoc hd :: declaratorDocs tl))
        ++ t ";"
  | .using_ isAwait ⟨hd, tl⟩ =>
      t (if isAwait then "await using " else "using ")
        ++ .group (Doc.joinWith (t "," ++ .line) (declaratorDoc hd :: declaratorDocs tl))
        ++ t ";"
  | .doWhile body cond =>
      t "do" ++ attachedBodyWith body (statementDoc body)
        ++ (match body with | .block _ => t " " | _ => .hardline)
        ++ t "while (" ++ exprDocWith 1 cond (exprCore cond) ++ t ");"
  | .for_ init cond step body =>
      t "for (" ++ forInitDoc init ++ t ";"
        ++ (match cond with
            | none => Doc.nil
            | some c => t " " ++ exprDocWith 1 c (exprCore c)) ++ t ";"
        ++ (match step with
            | none => Doc.nil
            | some s => t " " ++ exprDocWith 1 s (exprCore s)) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)
  | .forIn head obj body =>
      t "for (" ++ forHeadDoc head ++ t " in " ++ exprDocWith 2 obj (exprCore obj) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)
  | .forOf head obj body =>
      t "for (" ++ forHeadDoc head ++ t " of " ++ exprDocWith 2 obj (exprCore obj) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)
  | .funcDecl isAsync isGen name params body =>
      functionDocOf isAsync isGen (some name) params (paramDocs params) body
        (Doc.joinWith .hardline (statementDocs body))
  | .if_ cond thenS elseS =>
      let head :=
        t "if (" ++ exprDocWith 1 cond (exprCore cond) ++ t ")"
          ++ attachedBodyWith thenS (statementDoc thenS)
      match elseS with
      | none => head
      | some e =>
          let kw := match thenS with
            | .block _ => t " else"
            | _ => .hardline ++ t "else"
          let tail := match e with
            | .if_ .. => t " " ++ statementDoc e
            | _ => attachedBodyWith e (statementDoc e)
          head ++ kw ++ tail
  | .labelled l s => t (l.val ++ ": ") ++ statementDoc s
  | .empty => t ";"
  | .expr e =>
      let d := exprDocWith 1 e (exprCore e)
      if needsStatementParens e then parens d ++ t ";" else d ++ t ";"
  | .return_ none => t "return;"
  | .return_ (some e) => t "return " ++ exprDocWith 1 e (exprCore e) ++ t ";"
  | .switch disc cases =>
      t "switch (" ++ exprDocWith 1 disc (exprCore disc) ++ t ") "
        ++ (if cases.isEmpty then t "{}"
            else t "{" ++ .nest indentWidth
              (.hardline ++ Doc.joinWith .hardline (switchCaseDocs cases))
              ++ .hardline ++ t "}")
  | .throw e => t "throw " ++ exprDocWith 1 e (exprCore e) ++ t ";"
  | .try_ body tail =>
      t "try " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body))
        ++ tryTailDoc tail
  | .while_ cond body =>
      t "while (" ++ exprDocWith 1 cond (exprCore cond) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)
  | .with_ obj body =>
      t "with (" ++ exprDocWith 1 obj (exprCore obj) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)

def statementDocs : List MiniStatement → List Doc
  | [] => []
  | s :: rest => statementDoc s :: statementDocs rest

end

/-! ### Document builders for AST nodes -/

/-- An expression in a position that requires precedence `minPrec`. -/
def exprDoc (minPrec : Nat) (e : MiniExpr) : Doc := exprDocWith minPrec e (exprCore e)

/-- The object of a `.` or `[]` access. -/
def memberObjectDoc (e : MiniExpr) : Doc := memberObjectWith e (exprCore e)

/-- The callee of a call. -/
def calleeDoc (e : MiniExpr) : Doc := calleeWith e (exprCore e)

def argsDoc (args : List MiniExpr) : Doc := sepList "(" ")" false true (argDocs args)

/-- A parameter list. -/
def paramsDoc (params : List MiniParam) : Doc := paramsDocOf params (paramDocs params)

def arrayDoc (els : List MiniArrayElement) : Doc := arrayDocOf els (arrayItemDocs els)

def classBodyDoc (body : List MiniClassElement) : Doc := classBodyOf body (classElemDocs body)

def classElementDoc (el : MiniClassElement) : Doc := classElemDoc el

/-- A binding pattern. -/
def patternDocOf (p : MiniPattern) : Doc := patternDoc p

/-- One decorator, `@expr`. -/
def decoratorDoc (e : MiniExpr) : Doc := t "@" ++ exprDoc 16 e

def classDoc (decorators : List MiniExpr) (name : Option NEString)
    (heritage : Option MiniExpr) (body : List MiniClassElement) : Doc :=
  classDocOf (decoratorDocs decorators) name
    (match heritage with | none => Doc.nil | some e => t " extends " ++ exprDoc 16 e)
    body (classElemDocs body)

def methodDoc (kind : MethodKind) (key : MiniPropertyName)
    (params : List MiniParam) (body : List MiniStatement) : Doc :=
  methodDocOf kind (propertyNameDoc key) params (paramDocs params) body
    (Doc.joinWith .hardline (statementDocs body))

def functionDoc (isAsync isGen : Bool) (name : Option NEString)
    (params : List MiniParam) (body : List MiniStatement) : Doc :=
  functionDocOf isAsync isGen name params (paramDocs params) body
    (Doc.joinWith .hardline (statementDocs body))

/-- A statement list, one statement per line. -/
def statementsDoc (body : List MiniStatement) : Doc :=
  Doc.joinWith .hardline (statementDocs body)

/-- A brace enclosed statement list. -/
def blockDoc (body : List MiniStatement) : Doc := blockDocOf body (statementsDoc body)

/-- The body of an `if`, `for`, `while` or `with`, attached to its head. -/
def attachedBodyDoc (s : MiniStatement) : Doc := attachedBodyWith s (statementDoc s)

/-- The statements of one `case` of a `switch`. -/
def caseBodyDoc (body : List MiniStatement) : Doc := caseBodyWith body (statementsDoc body)

def declarationDoc (kind : VarKind) (decls : NEList MiniDeclarator) : Doc :=
  t (varKindText kind ++ " ")
    ++ .group (Doc.joinWith (t "," ++ .line) (declaratorDocs decls.toList))

/-! ## Modules -/

def specifierDoc (s : Specifier) : Doc :=
  t s.name.val ++ (match s.alias_ with | none => Doc.nil | some a => t (" as " ++ a.val))

def specifiersDoc (specs : List Specifier) : Doc :=
  sepList "{" "}" true true (specs.map specifierDoc)

/-- The `with { type: "json" }` of an import; nothing when there is no
attribute. -/
def importAttrsDoc (attrs : List ImportAttr) : Doc :=
  if attrs.isEmpty then Doc.nil
  else
    t " with "
      ++ sepList "{" "}" true true
          (attrs.map fun a =>
            t (encodeStringLiteral a.key ++ ": " ++ encodeStringLiteral a.value))

def importDoc : MiniImportDeclaration → Doc
  | .bare mod attrs =>
      t ("import " ++ encodeStringLiteral mod.val) ++ importAttrsDoc attrs ++ t ";"
  | .clause c =>
      let parts : List Doc :=
        (match c.default_ with | none => [] | some d => [t d.val])
        ++ (match c.namespace_ with | none => [] | some n => [t ("* as " ++ n.val)])
        ++ (match c.named with | none => [] | some specs => [specifiersDoc specs])
      t "import " ++ Doc.joinWith (t ", ") parts
        ++ t (" from " ++ encodeStringLiteral c.mod.val) ++ importAttrsDoc c.attrs ++ t ";"

def exportDoc : MiniExportDeclaration → Doc
  | .fromClause specs mod attrs =>
      t "export " ++ specifiersDoc specs ++ t (" from " ++ encodeStringLiteral mod.val)
        ++ importAttrsDoc attrs ++ t ";"
  | .locals specs => t "export " ++ specifiersDoc specs ++ t ";"
  | .all alias_ mod attrs =>
      t "export *"
        ++ (match alias_ with | none => Doc.nil | some n => t (" as " ++ n.val))
        ++ t (" from " ++ encodeStringLiteral mod.val) ++ importAttrsDoc attrs ++ t ";"
  | .defaultExpr e => t "export default " ++ exprDocWith 2 e (exprCore e) ++ t ";"
  | .decl s => t "export " ++ statementDoc s

def moduleItemDoc : MiniModuleItem → Doc
  | .stmt s => statementDoc s
  | .importDecl d => importDoc d
  | .exportDecl d => exportDoc d

def programDoc (p : MiniProgram) : Doc :=
  Doc.joinWith .hardline (p.items.map moduleItemDoc)

end Printer

/-! ## Entry points -/

/-- Print a program in the canonical style, at a given line width. -/
def printProgramWidth (width : Nat) (p : MiniProgram) : String :=
  if p.items.isEmpty then ""
  else Doc.render width (Printer.programDoc p) ++ "\n"

/-- Print a program in the canonical style: two space indentation, double
quotes, semicolons, and lines of at most 80 columns. -/
def printProgram (p : MiniProgram) : String :=
  printProgramWidth Printer.defaultWidth p

/-- Print a single statement. -/
def printStatement (s : MiniStatement) : String :=
  Doc.render Printer.defaultWidth (Printer.statementDoc s)

/-- Print a single expression. -/
def printExpr (e : MiniExpr) : String :=
  Doc.render Printer.defaultWidth (Printer.exprDoc 1 e)

end Language.JavaScript.MiniAST
