import LakeJs.Surface

/-!
# Reading the surface syntax

A hand-written tokeniser and recursive-descent parser for the text inside
`[LEAN| … ]`.  It is a parser of its own rather than Lean syntax on purpose: the
fragment is read as text, so none of its words — `let`, `case`, `nat`, `ret` — becomes
a Lean token, and the *same* parser reads the text that `LakeJs.TermDeelab` prints.  So
the round trip is a fact about two functions of this package and not about Lean's
parser.

Everything here is total: the recursion is on a fuel that starts at the number of
tokens, which no well-formed fragment can exhaust, and a fragment that would is
refused with a message rather than looping.
-/

namespace LakeJs.Surface

open LakeJs
open LakeJs.Ty

/-! ## Tokens -/

/-- A token of the surface syntax. -/
inductive Tok where
  /-- A name: a variable, a keyword, an extern, a type. -/
  | id (s : String)
  /-- A run of digits. -/
  | num (s : String)
  /-- A string literal, with its escapes already resolved. -/
  | str (s : String)
  /-- A character literal. -/
  | chr (c : Char)
  /-- One of `( ) [ ] , : = | -`. -/
  | punct (s : String)
  deriving BEq, Inhabited

/-- How a token reads in an error message. -/
def Tok.print : Tok → String
  | .id s => s
  | .num s => s
  | .str s => quoteString s
  | .chr c => quoteChar c
  | .punct s => s

/-- Is this a character a name may start with? -/
def isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'

/-- Is this a character a name may continue with? -/
def isIdCont (c : Char) : Bool :=
  isIdStart c || c.isDigit || c == '.' || c == '\''

/-- The escape a backslash introduces. -/
def unescape (c : Char) : Except String Char :=
  match c with
  | 'n' => .ok '\n'
  | 't' => .ok '\t'
  | 'r' => .ok '\r'
  | '\\' => .ok '\\'
  | '"' => .ok '"'
  | '\'' => .ok '\''
  | c => .error s!"unknown escape `\\{c}`"

/-- Read a string literal, the opening quote already consumed. -/
def lexString : Nat → List Char → String → Except String (String × List Char)
  | 0, _, _ => .error "unterminated string literal"
  | _ + 1, [], _ => .error "unterminated string literal"
  | _ + 1, '"' :: rest, acc => .ok (acc, rest)
  | fuel + 1, '\\' :: c :: rest, acc => do
      lexString fuel rest (acc ++ String.singleton (← unescape c))
  | _ + 1, '\\' :: [], _ => .error "unterminated string literal"
  | fuel + 1, c :: rest, acc => lexString fuel rest (acc ++ String.singleton c)

/-- Read a character literal, the opening quote already consumed. -/
def lexChar : List Char → Except String (Char × List Char)
  | '\\' :: c :: '\'' :: rest => do .ok (← unescape c, rest)
  | c :: '\'' :: rest => .ok (c, rest)
  | _ => .error "malformed character literal"

/-- The longest name at the front of `cs`. -/
def takeIdent : List Char → String → (String × List Char)
  | c :: rest, acc => if isIdCont c then takeIdent rest (acc ++ String.singleton c)
      else (acc, c :: rest)
  | [], acc => (acc, [])

/-- The longest run of digits at the front of `cs`. -/
def takeDigits : List Char → String → (String × List Char)
  | c :: rest, acc => if c.isDigit then takeDigits rest (acc ++ String.singleton c)
      else (acc, c :: rest)
  | [], acc => (acc, [])

/-- The tokens of a fragment. -/
def tokenize : Nat → List Char → List Tok → Except String (List Tok)
  | 0, _, _ => .error "the fragment is too long to read"
  | _ + 1, [], acc => .ok acc.reverse
  | fuel + 1, c :: rest, acc =>
      if c == ' ' || c == '\n' || c == '\t' || c == '\r' then tokenize fuel rest acc
      else if c == '"' then do
        let (s, rest') ← lexString (fuel + 1) rest ""
        tokenize fuel rest' (.str s :: acc)
      else if c == '\'' then do
        let (ch, rest') ← lexChar rest
        tokenize fuel rest' (.chr ch :: acc)
      else if isIdStart c then
        let (s, rest') := takeIdent (c :: rest) ""
        tokenize fuel rest' (.id s :: acc)
      else if c.isDigit then
        let (s, rest') := takeDigits (c :: rest) ""
        tokenize fuel rest' (.num s :: acc)
      else if c == '(' || c == ')' || c == '[' || c == ']' || c == ',' || c == ':'
            || c == '=' || c == '|' || c == '-' then
        tokenize fuel rest (.punct (String.singleton c) :: acc)
      else .error s!"unexpected character `{c}`"

/-- The tokens of a fragment. -/
def lex (s : String) : Except String (List Tok) :=
  tokenize (s.length + 1) s.toList []

/-! ## The little helpers every rule uses -/

/-- What was read where a token was expected. -/
def unexpected (what : String) : List Tok → String
  | [] => s!"expected {what}, but the fragment ends"
  | t :: _ => s!"expected {what}, but read `{t.print}`"

/-- Consume the punctuation `p`. -/
def expectPunct (p : String) (ts : List Tok) : Except String (List Tok) :=
  match ts with
  | .punct q :: rest => if q == p then .ok rest else .error (unexpected s!"`{p}`" ts)
  | _ => .error (unexpected s!"`{p}`" ts)

/-- Is the next token the punctuation `p`? -/
def peekPunct (p : String) : List Tok → Bool
  | .punct q :: _ => q == p
  | _ => false

/-- Is the next token the name `n`? -/
def peekId (n : String) : List Tok → Bool
  | .id m :: _ => m == n
  | _ => false

/-- Consume a name. -/
def expectId (ts : List Tok) : Except String (String × List Tok) :=
  match ts with
  | .id s :: rest => .ok (s, rest)
  | _ => .error (unexpected "a name" ts)

/-- Consume the name `n`. -/
def expectKw (n : String) (ts : List Tok) : Except String (List Tok) :=
  match ts with
  | .id m :: rest => if m == n then .ok rest else .error (unexpected s!"`{n}`" ts)
  | _ => .error (unexpected s!"`{n}`" ts)

/-- Consume a natural number. -/
def expectNat (ts : List Tok) : Except String (Nat × List Tok) :=
  match ts with
  | .num s :: rest => .ok (s.toNat!, rest)
  | _ => .error (unexpected "a number" ts)

/-- Consume an integer, which may be written with a leading `-`. -/
def expectInt (ts : List Tok) : Except String (Int × List Tok) :=
  match ts with
  | .punct "-" :: .num s :: rest => .ok (-(Int.ofNat s.toNat!), rest)
  | .num s :: rest => .ok (Int.ofNat s.toNat!, rest)
  | _ => .error (unexpected "an integer" ts)

/-- Consume a string literal. -/
def expectStr (ts : List Tok) : Except String (String × List Tok) :=
  match ts with
  | .str s :: rest => .ok (s, rest)
  | _ => .error (unexpected "a string literal" ts)

/-- Consume a character literal. -/
def expectChr (ts : List Tok) : Except String (Char × List Tok) :=
  match ts with
  | .chr c :: rest => .ok (c, rest)
  | _ => .error (unexpected "a character literal" ts)

/-- Consume a bracketed, comma-separated list of numbers. -/
def parseNats : Nat → List Tok → List Nat → Except String (List Nat × List Tok)
  | 0, _, _ => .error "list too long"
  | fuel + 1, ts, acc => do
      if peekPunct "]" ts then .ok (acc.reverse, ← expectPunct "]" ts)
      else
        let (n, ts) ← expectNat ts
        if peekPunct "," ts then parseNats fuel (← expectPunct "," ts) (n :: acc)
        else .ok ((n :: acc).reverse, ← expectPunct "]" ts)

/-! ## Types -/

mutual

/-- A written type. -/
def parseRawTy : Nat → List Tok → Except String (RawTy × List Tok)
  | 0, _ => .error "the type is nested too deeply"
  | fuel + 1, ts => do
    match ts with
    | .id n :: rest => .ok (.prim n, rest)
    | .punct "(" :: .id head :: rest =>
      match head with
      | "bitvec" => do
          let (n, ts) ← expectNat rest
          .ok (.bitvec n, ← expectPunct ")" ts)
      | "self" => do
          let (n, ts) ← expectNat rest
          .ok (.self n, ← expectPunct ")" ts)
      | "fn" => do
          let ts ← expectPunct "[" rest
          let (ps, ts) ← parseRawTys fuel ts []
          let (r, ts) ← parseRawTy fuel ts
          .ok (.fn ps r, ← expectPunct ")" ts)
      | "fnProd" => do
          let ts ← expectPunct "[" rest
          let (ps, ts) ← parseRawTys fuel ts []
          let ts ← expectPunct "[" ts
          let (rs, ts) ← parseRawTys fuel ts []
          .ok (.fnProd ps rs, ← expectPunct ")" ts)
      | "array" => do
          let (t, ts) ← parseRawTy fuel rest
          .ok (.array t, ← expectPunct ")" ts)
      | "list" => do
          let (t, ts) ← parseRawTy fuel rest
          .ok (.list t, ← expectPunct ")" ts)
      | "task" => do
          let (t, ts) ← parseRawTy fuel rest
          .ok (.task t, ← expectPunct ")" ts)
      | "promise" => do
          let (t, ts) ← parseRawTy fuel rest
          .ok (.promise t, ← expectPunct ")" ts)
      | "thunk" => do
          let (t, ts) ← parseRawTy fuel rest
          .ok (.thunk t, ← expectPunct ")" ts)
      | "lazy" => do
          let (t, ts) ← parseRawTy fuel rest
          .ok (.lazy t, ← expectPunct ")" ts)
      | "enum" => do
          let (n, ts) ← expectNat rest
          let (s, ts) ← expectInt ts
          .ok (.enum n s, ← expectPunct ")" ts)
      | "record" => do
          let ts ← expectPunct "[" rest
          let (fs, ts) ← parseRawTys fuel ts []
          .ok (.record fs, ← expectPunct ")" ts)
      | "union" => do
          let ts ← expectPunct "[" rest
          let (cs, ts) ← parseRawTyCtors fuel ts []
          .ok (.union cs, ← expectPunct ")" ts)
      | "recUnion" => do
          let ts ← expectPunct "[" rest
          let (cs, ts) ← parseRawTyCtors fuel ts []
          .ok (.recUnion cs, ← expectPunct ")" ts)
      | "recObject" => do
          let ts ← expectPunct "[" rest
          let (fs, ts) ← parseRawTys fuel ts []
          .ok (.recObject fs, ← expectPunct ")" ts)
      | "recAlias" => do
          let (t, ts) ← parseRawTy fuel rest
          .ok (.recAlias t, ← expectPunct ")" ts)
      | "family" => do
          let (i, ts) ← expectNat rest
          let ts ← expectPunct "[" ts
          let (ms, ts) ← parseRawTys fuel ts []
          .ok (.family ms i, ← expectPunct ")" ts)
      | "famCtors" => do
          let ts ← expectPunct "[" rest
          let (cs, ts) ← parseRawTyCtors fuel ts []
          .ok (.famCtors cs, ← expectPunct ")" ts)
      | "famAlias" => do
          let (t, ts) ← parseRawTy fuel rest
          .ok (.famAlias t, ← expectPunct ")" ts)
      | h => .error s!"unknown type former `{h}`"
    | _ => .error (unexpected "a type" ts)

/-- A comma-separated list of written types, terminated by `]`, which is consumed.
    The opening bracket has been consumed already. -/
def parseRawTys : Nat → List Tok → List RawTy → Except String (List RawTy × List Tok)
  | 0, _, _ => .error "the type list is too long"
  | fuel + 1, ts, acc => do
      if peekPunct "]" ts then .ok (acc.reverse, ← expectPunct "]" ts)
      else
        let (t, ts) ← parseRawTy fuel ts
        if peekPunct "," ts then parseRawTys fuel (← expectPunct "," ts) (t :: acc)
        else .ok ((t :: acc).reverse, ← expectPunct "]" ts)

/-- A comma-separated list of bracketed type lists, terminated by `]`. -/
def parseRawTyCtors :
    Nat → List Tok → List (List RawTy) → Except String (List (List RawTy) × List Tok)
  | 0, _, _ => .error "the constructor list is too long"
  | fuel + 1, ts, acc => do
      if peekPunct "]" ts then .ok (acc.reverse, ← expectPunct "]" ts)
      else
        let ts ← expectPunct "[" ts
        let (c, ts) ← parseRawTys fuel ts []
        if peekPunct "," ts then parseRawTyCtors fuel (← expectPunct "," ts) (c :: acc)
        else .ok ((c :: acc).reverse, ← expectPunct "]" ts)

end

/-- A written type, read as a closed type. -/
def parseTy (fuel : Nat) (ts : List Tok) : Except String (Ty × List Tok) := do
  let (raw, ts) ← parseRawTy fuel ts
  .ok (← raw.toTy, ts)

/-- A comma-separated list of `name : type` binders, which ends where neither a name
    nor a comma follows. -/
def parseDecls : Nat → List Tok → List SParam → Except String (List SParam × List Tok)
  | 0, _, _ => .error "too many declarations"
  | fuel + 1, ts, acc => do
      match ts with
      | .id n :: rest =>
          let ts ← expectPunct ":" rest
          let (t, ts) ← parseTy (fuel + 1) ts
          if peekPunct "," ts then parseDecls fuel (← expectPunct "," ts) ((n, t) :: acc)
          else .ok (((n, t) :: acc).reverse, ts)
      | _ => .ok (acc.reverse, ts)

/-! ## Terms -/

/-- The list of terms of a spine, as a spine. -/
def spineOfList : List STerm → SSpine
  | [] => .nil
  | t :: ts => .cons t (spineOfList ts)

/-- A written constant. -/
def parseLit (ts : List Tok) : Except String (SLit × List Tok) := do
  let (kind, ts) ← expectId ts
  match kind with
  | "bool" => do
      let (b, ts) ← expectId ts
      if b == "true" then .ok (.bool true, ts)
      else if b == "false" then .ok (.bool false, ts)
      else .error s!"`{b}` is not a boolean"
  | "nat" => do let (n, ts) ← expectNat ts; .ok (.nat n, ts)
  | "int" => do let (i, ts) ← expectInt ts; .ok (.int i, ts)
  | "bitvec" => do
      let (w, ts) ← expectNat ts
      let (v, ts) ← expectNat ts
      .ok (.bitvec w v, ts)
  | "uint8" => do let (n, ts) ← expectNat ts; .ok (.uint8 n, ts)
  | "uint16" => do let (n, ts) ← expectNat ts; .ok (.uint16 n, ts)
  | "uint32" => do let (n, ts) ← expectNat ts; .ok (.uint32 n, ts)
  | "uint64" => do let (n, ts) ← expectNat ts; .ok (.uint64 n, ts)
  | "usize" => do let (n, ts) ← expectNat ts; .ok (.usize n, ts)
  | "int8" => do let (i, ts) ← expectInt ts; .ok (.int8 i, ts)
  | "int16" => do let (i, ts) ← expectInt ts; .ok (.int16 i, ts)
  | "int32" => do let (i, ts) ← expectInt ts; .ok (.int32 i, ts)
  | "int64" => do let (i, ts) ← expectInt ts; .ok (.int64 i, ts)
  | "isize" => do let (i, ts) ← expectInt ts; .ok (.isize i, ts)
  | "char" => do let (c, ts) ← expectChr ts; .ok (.char c, ts)
  | "string" => do let (s, ts) ← expectStr ts; .ok (.string s, ts)
  | "byteArray" => do
      let ts ← expectPunct "[" ts
      let (ns, ts) ← parseNats (ts.length + 1) ts []
      .ok (.byteArray ns, ts)
  | "name" => do let (s, ts) ← expectStr ts; .ok (.name s, ts)
  | "stringPos" => do let (n, ts) ← expectNat ts; .ok (.stringPos n, ts)
  | "substring" => do
      let (s, ts) ← expectStr ts
      let (a, ts) ← expectNat ts
      let (b, ts) ← expectNat ts
      .ok (.substring s a b, ts)
  | "stringSlice" => do
      let (s, ts) ← expectStr ts
      let (a, ts) ← expectNat ts
      let (b, ts) ← expectNat ts
      .ok (.stringSlice s a b, ts)
  | "float" => do let (n, ts) ← expectNat ts; .ok (.float (UInt64.ofNat n), ts)
  | "float32" => do let (n, ts) ← expectNat ts; .ok (.float32 (UInt32.ofNat n), ts)
  | "floatArray" => do
      let ts ← expectPunct "[" ts
      let (ns, ts) ← parseNats (ts.length + 1) ts []
      .ok (.floatArray (ns.map UInt64.ofNat), ts)
  | k => .error s!"unknown literal `{k}`"

/-- A written operation that is JavaScript's rather than Lean's. -/
def parseOp (fuel : Nat) (ts : List Tok) : Except String (SOp × List Tok) := do
  let (nm, ts) ← expectId ts
  match nm with
  | "cast" => do
      let (a, ts) ← parseTy fuel ts
      let (b, ts) ← parseTy fuel ts
      .ok (.cast a b, ts)
  | "toStr" => do let (t, ts) ← parseTy fuel ts; .ok (.toStr t, ts)
  | "boolAnd" => .ok (.boolAnd, ts)
  | "boolOr" => .ok (.boolOr, ts)
  | "boolNot" => .ok (.boolNot, ts)
  | "boolBEq" => .ok (.boolBEq, ts)
  | "charBEq" => .ok (.charBEq, ts)
  | "natSubExact" => .ok (.natSubExact, ts)
  | n => .error s!"unknown operation `{n}`"

mutual

/-- A written term. -/
def parseTerm : Nat → List Tok → Except String (STerm × List Tok)
  | 0, _ => .error "the term is nested too deeply"
  | fuel + 1, ts => do
    match ts with
    | .id n :: rest => .ok (.var n, rest)
    | .punct "(" :: .id head :: rest =>
      match head with
      | "lit" => do
          let (l, ts) ← parseLit rest
          .ok (.lit l, ← expectPunct ")" ts)
      | "extern" => do
          let (nm, ts) ← expectId rest
          let (tys, ts) ← parseTysUntilClose fuel ts []
          .ok (.extern nm tys, ts)
      | "fn" => do
          let ts ← expectPunct "[" rest
          let (ps, ts) ← parseParams fuel ts []
          let (b, ts) ← parseTerm fuel ts
          .ok (.lam ps b, ← expectPunct ")" ts)
      | "app" => do
          let (f, ts) ← parseTerm fuel rest
          let (args, ts) ← parseTermsUntilClose fuel ts []
          .ok (.app f (spineOfList args), ts)
      | "prodFn" => do
          let ts ← expectPunct "[" rest
          let (ps, ts) ← parseParams fuel ts []
          let (rets, ts) ← parseTermsUntilClose fuel ts []
          if rets.isEmpty then .error "`prodFn` must answer with at least one value"
          else .ok (.lamProd ps (spineOfList rets), ts)
      | "callProd" => do
          let (i, ts) ← expectNat rest
          let (f, ts) ← parseTerm fuel ts
          let (args, ts) ← parseTermsUntilClose fuel ts []
          .ok (.callProd i f (spineOfList args), ts)
      | "op" => do
          let (o, ts) ← parseOp fuel rest
          let (args, ts) ← parseTermsUntilClose fuel ts []
          .ok (.op o (spineOfList args), ts)
      | "let" => do
          let (n, ts) ← expectId rest
          let ts ← expectPunct ":" ts
          let (t, ts) ← parseTy fuel ts
          let ts ← expectPunct "=" ts
          let (v, ts) ← parseTerm fuel ts
          let (b, ts) ← parseTerm fuel ts
          .ok (.letE n t v b, ← expectPunct ")" ts)
      | "if" => do
          let (c, ts) ← parseTerm fuel rest
          let (t, ts) ← parseTerm fuel ts
          let (e, ts) ← parseTerm fuel ts
          .ok (.ite c t e, ← expectPunct ")" ts)
      | "ctor" => do
          let (i, ts) ← expectNat rest
          let ts ← expectPunct ":" ts
          let (t, ts) ← parseTy fuel ts
          let (args, ts) ← parseTermsUntilClose fuel ts []
          .ok (.ctor i t (spineOfList args), ts)
      | "proj" => do
          let (i, ts) ← expectNat rest
          let (j, ts) ← expectNat ts
          let (e, ts) ← parseTerm fuel ts
          .ok (.proj i j e, ← expectPunct ")" ts)
      | "tagOf" => do
          let (e, ts) ← parseTerm fuel rest
          .ok (.tagOf e, ← expectPunct ")" ts)
      | "lazy" => do
          let (e, ts) ← parseTerm fuel rest
          .ok (.lazyMk e, ← expectPunct ")" ts)
      | "force" => do
          let (e, ts) ← parseTerm fuel rest
          .ok (.lazyForce e, ← expectPunct ")" ts)
      | "case" => do
          let (s, ts) ← parseTerm fuel rest
          let (alts, ts) ← parseAlts fuel ts
          .ok (.caseTag s alts, ← expectPunct ")" ts)
      | "loop" => do
          let ts ← expectPunct "[" rest
          let (slots, ts) ← parseParams fuel ts []
          let (inits, ts) ← parseTermsN fuel slots.length ts []
          let (b, ts) ← parseBody fuel ts
          .ok (.loop slots (spineOfList inits) b, ← expectPunct ")" ts)
      | "join" => do
          let (n, ts) ← expectId rest
          let ts ← expectPunct "[" ts
          let (ps, ts) ← parseParams fuel ts []
          let ts ← expectPunct ":" ts
          let (ret, ts) ← parseTy fuel ts
          let (body, ts) ← parseTerm fuel ts
          let (r, ts) ← parseTerm fuel ts
          .ok (.joinPoint n ps ret body r, ← expectPunct ")" ts)
      | "jump" => do
          let (n, ts) ← expectId rest
          let (args, ts) ← parseTermsUntilClose fuel ts []
          .ok (.jump n (spineOfList args), ts)
      | h => .error s!"unknown term former `{h}`"
    | _ => .error (unexpected "a term" ts)

/-- Terms up to the closing parenthesis, which is consumed. -/
def parseTermsUntilClose :
    Nat → List Tok → List STerm → Except String (List STerm × List Tok)
  | 0, _, _ => .error "too many arguments"
  | fuel + 1, ts, acc => do
      if peekPunct ")" ts then .ok (acc.reverse, ← expectPunct ")" ts)
      else
        let (t, ts) ← parseTerm fuel ts
        parseTermsUntilClose fuel ts (t :: acc)

/-- Exactly `n` terms. -/
def parseTermsN :
    Nat → Nat → List Tok → List STerm → Except String (List STerm × List Tok)
  | 0, _, _, _ => .error "too many arguments"
  | _ + 1, 0, ts, acc => .ok (acc.reverse, ts)
  | fuel + 1, n + 1, ts, acc => do
      let (t, ts) ← parseTerm fuel ts
      parseTermsN fuel n ts (t :: acc)

/-- Types up to the closing parenthesis, which is consumed. -/
def parseTysUntilClose :
    Nat → List Tok → List Ty → Except String (List Ty × List Tok)
  | 0, _, _ => .error "too many type arguments"
  | fuel + 1, ts, acc => do
      if peekPunct ")" ts then .ok (acc.reverse, ← expectPunct ")" ts)
      else
        let (t, ts) ← parseTy fuel ts
        parseTysUntilClose fuel ts (t :: acc)

/-- A comma-separated list of `name : type` binders, terminated by `]`. -/
def parseParams :
    Nat → List Tok → List SParam → Except String (List SParam × List Tok)
  | 0, _, _ => .error "too many binders"
  | fuel + 1, ts, acc => do
      if peekPunct "]" ts then .ok (acc.reverse, ← expectPunct "]" ts)
      else
        let (n, ts) ← expectId ts
        let ts ← expectPunct ":" ts
        let (t, ts) ← parseTy fuel ts
        if peekPunct "," ts then parseParams fuel (← expectPunct "," ts) ((n, t) :: acc)
        else .ok (((n, t) :: acc).reverse, ← expectPunct "]" ts)

/-- The branches of a case: tagged ones, then the default. -/
def parseAlts : Nat → List Tok → Except String (SAlts × List Tok)
  | 0, _ => .error "too many branches"
  | fuel + 1, ts => do
      match ts with
      | .punct "(" :: .id "tag" :: rest => do
          let (tag, ts) ← expectNat rest
          let (t, ts) ← parseTerm fuel ts
          let ts ← expectPunct ")" ts
          let (rest', ts) ← parseAlts fuel ts
          .ok (.cons tag t rest', ts)
      | .punct "(" :: .id "default" :: rest => do
          let (t, ts) ← parseTerm fuel rest
          .ok (.deflt t, ← expectPunct ")" ts)
      | _ => .error (unexpected "a `(tag …)` or `(default …)` branch" ts)

/-- A written loop body. -/
def parseBody : Nat → List Tok → Except String (SBody × List Tok)
  | 0, _ => .error "the loop body is nested too deeply"
  | fuel + 1, ts => do
      match ts with
      | .punct "(" :: .id "ret" :: rest => do
          let (t, ts) ← parseTerm fuel rest
          .ok (.ret t, ← expectPunct ")" ts)
      | .punct "(" :: .id "cont" :: rest => do
          let (args, ts) ← parseTermsUntilClose fuel rest []
          .ok (.cont (spineOfList args), ts)
      | .punct "(" :: .id "letB" :: rest => do
          let (n, ts) ← expectId rest
          let ts ← expectPunct ":" ts
          let (t, ts) ← parseTy fuel ts
          let ts ← expectPunct "=" ts
          let (v, ts) ← parseTerm fuel ts
          let (b, ts) ← parseBody fuel ts
          .ok (.letB n t v b, ← expectPunct ")" ts)
      | .punct "(" :: .id "ifB" :: rest => do
          let (c, ts) ← parseTerm fuel rest
          let (t, ts) ← parseBody fuel ts
          let (e, ts) ← parseBody fuel ts
          .ok (.iteB c t e, ← expectPunct ")" ts)
      | .punct "(" :: .id "joinB" :: rest => do
          let (n, ts) ← expectId rest
          let ts ← expectPunct "[" ts
          let (ps, ts) ← parseParams fuel ts []
          let ts ← expectPunct ":" ts
          let (ret, ts) ← parseTy fuel ts
          let (body, ts) ← parseTerm fuel ts
          let (r, ts) ← parseBody fuel ts
          .ok (.joinPointB n ps ret body r, ← expectPunct ")" ts)
      | _ => .error (unexpected "a `(ret …)`, `(cont …)`, `(letB …)`, `(ifB …)` or \
`(joinB …)`" ts)

end

/-! ## A whole fragment -/

/-- The header sections, in any order, each ended by `|`. -/
def parseSections :
    Nat → List Tok → SEmbed → Except String (SEmbed × List Tok)
  | 0, _, e => .ok (e, [])
  | fuel + 1, ts, e => do
      if peekId "sig" ts then
        let ts ← expectKw "sig" ts
        if peekPunct "|" ts then parseSections fuel (← expectPunct "|" ts) e
        else
          let (t, ts) ← parseTy (fuel + 1) ts
          parseSections fuel (← expectPunct "|" ts) { e with sig := some t }
      else if peekId "glob" ts then
        let ts ← expectKw "glob" ts
        let (ds, ts) ← parseDecls (fuel + 1) ts []
        parseSections fuel (← expectPunct "|" ts) { e with glob := ds }
      else if peekId "vars" ts then
        let ts ← expectKw "vars" ts
        let (ds, ts) ← parseDecls (fuel + 1) ts []
        parseSections fuel (← expectPunct "|" ts) { e with vars := ds }
      else .ok (e, ts)

/-- Read a whole fragment: the header sections, then the code. -/
def parseEmbed (input : String) : Except String SEmbed := do
  let ts ← lex input
  let fuel := ts.length + 1
  let (e, ts) ← parseSections fuel ts { code := .var "?" }
  let (code, ts) ← parseTerm fuel ts
  if ts.isEmpty then .ok { e with code := code }
  else .error s!"the fragment does not end where the code does: `{(ts.map Tok.print).take 5}`"

end LakeJs.Surface
