/-!
# What the shape of the emitted JavaScript must be

The term language the backend translates into has no recursive-definition node: the only
repetition a `Term` can express is `Term.loop`, and no `Term` can be an Omega, because
`Ty.ne_arrow_self` says a self-application does not typecheck (both are proved in
`LakeJs/TermTotal.lean`).  This module checks the same thing of the *output*, on every
snapshot the test run compiles: the printed module may loop with `while` and with `for`
and in no other way.

What that rules out, concretely:

* `function` — a function declaration, which can name and so call itself; the backend
  prints arrows only;
* `eval`, `new` (as in `new Function(…)`), `import(` — building code at run time;
* `do`, so a `do … while` never slips past the `while (…)` check;
* `throw`, `undefined` — a `Term` is pure and total, and nothing it drops may come back
  as an `undefined`;
* a self-application `x(x)`, the core of `ω = λx. x x` and of every fixed point built
  from one;
* a `while` or `for` that is not the head of a `while (…)` / `for (…)` statement.

The check reads the text as JavaScript tokens rather than as a string, so a `"catch"`
*inside a string literal* — several snapshots return exactly that string — is data, not
a keyword.
-/

namespace LakeJsTest.JsShape

/-- Is this a character a JavaScript identifier is made of? -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

/-- Is this token an identifier rather than punctuation or a number? -/
def isIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: _ => isIdentChar c && !c.isDigit

/-- Everything up to the end of a string literal opened with `q`. -/
partial def skipString (q : Char) : List Char → List Char
  | [] => []
  | '\\' :: _ :: cs => skipString q cs
  | c :: cs => if c == q then cs else skipString q cs

/-- The tokens of a JavaScript source: identifiers and numbers as one token each, every
    other character on its own, whitespace dropped and string literals skipped. -/
partial def tokens : List Char → List String
  | [] => []
  | '"' :: cs => tokens (skipString '"' cs)
  | '\'' :: cs => tokens (skipString '\'' cs)
  | c :: cs =>
    if isIdentChar c then
      let w := (c :: cs).takeWhile isIdentChar
      String.ofList w :: tokens ((c :: cs).drop w.length)
    else if c.isWhitespace then tokens cs
    else String.singleton c :: tokens cs

/-- The words the emitted JavaScript may not use. -/
def bannedWords : List String :=
  [ "function", "eval", "arguments", "new", "throw", "undefined", "do", "var", "with",
    "delete", "yield", "await", "class", "try", "catch", "finally", "switch", "goto",
    "Function" ]

/-- A `while` or a `for` that does not open a loop, which would mean the printer emitted
    something this check cannot read. -/
partial def loopIssues : List String → List String
  | [] => []
  | "while" :: "(" :: rest => loopIssues rest
  | "for" :: "(" :: rest => loopIssues rest
  | "while" :: rest => "a `while` that does not open a `while (…)`" :: loopIssues rest
  | "for" :: rest => "a `for` that does not open a `for (…)`" :: loopIssues rest
  | _ :: rest => loopIssues rest

/-- A self-application `x(x)`: the one term shape every untyped fixed point is built
    from, and one no `Term` has. -/
partial def selfAppIssues : List String → List String
  | a :: "(" :: b :: ")" :: rest =>
      if isIdent a && a == b then
        s!"the self-application `{a}({a})`, which is how an Omega is written"
          :: selfAppIssues rest
      else selfAppIssues ("(" :: b :: ")" :: rest)
  | _ :: rest => selfAppIssues rest
  | [] => []

/-- One top-level `const` of an emitted module, and the text of its value. -/
structure TopDecl where
  /-- The name it binds. -/
  name : String
  /-- What it is bound to. -/
  body : String

/-- The top-level declarations of an emitted module.  Every one of them is a
    `const <name> = …` beginning a line, and the `export { … }` at the end — which
    mentions every name and so is not part of any value — is dropped. -/
def topDecls (js : String) : List TopDecl :=
  let step : Option (String × List String) × List TopDecl → String →
      Option (String × List String) × List TopDecl := fun (cur, acc) line =>
    let flush : List TopDecl :=
      match cur with
      | some (n, bs) => acc ++ [{ name := n, body := String.intercalate "\n" bs.reverse }]
      | none => acc
    if line.startsWith "const " then
      let rest := (line.drop 6).toString
      let nm := String.ofList (rest.toList.takeWhile isIdentChar)
      (some (nm, [(rest.drop nm.length).toString]), flush)
    else if line.startsWith "export " then
      (none, flush)
    else
      match cur with
      | some (n, bs) => (some (n, line :: bs), acc)
      | none => (none, acc)
  match (js.splitOn "\n").foldl step (none, []) with
  | (some (n, bs), acc) => acc ++ [{ name := n, body := String.intercalate "\n" bs.reverse }]
  | (none, acc) => acc

/-- The declarations of an emitted module that call themselves, directly or through one
    another: the places where the Lean recursion was not a tail call and so did not
    become a loop.  These are not Omegas — the Lean functions they come from are total —
    but they are the output's only repetition that is not a `while`. -/
def recursiveNames (js : String) : List String :=
  let ds := topDecls js
  let names := ds.map (·.name)
  let direct : List (String × List String) := ds.map fun d =>
    (d.name, ((tokens d.body.toList).filter names.contains).eraseDups)
  let step (m : List (String × List String)) : List (String × List String) :=
    m.map fun (n, rs) => (n, (rs ++ rs.flatMap fun r => (m.lookup r).getD []).eraseDups)
  let closure := (List.range names.length).foldl (fun m _ => step m) direct
  names.filter fun n => ((closure.lookup n).getD []).contains n

/-- Everything wrong with the shape of `js`; `[]` when its only repetition is a `while`
    or a `for` loop. -/
def issues (js : String) : List String :=
  let ts := tokens js.toList
  let used := bannedWords.filter fun w => ts.contains w
  (used.map fun w => s!"the output uses `{w}`, which is not a `while` or a `for` loop")
    ++ loopIssues ts ++ selfAppIssues ts

end LakeJsTest.JsShape
