module

public import MiniAST
public import LakeJs.Expr
public import LakeJs.ExternsMeta

@[expose] public section

namespace LakeJs.EmitJs

/-!
# Printing a `Term` as JavaScript

The whole of the JavaScript the backend emits is built here, as a `MiniProgram` of
`MiniAST`, and printed by `MiniAST.printProgram`.  Nothing in this file can emit a
recursive JavaScript function: a `Term` has no recursive node to translate, so the only
repetition it can print is the `while` loop of `Term.loop`.

Names are chosen from the *depth* of the binder — the variable bound in a context of
length `k` is `v{k}` — which is deterministic, needs no gensym counter, and cannot
shadow, since two binders in the same scope chain always sit at different depths.

The shape of a loop follows the one the snapshots use:

```js
const test = (test$a0$copy) => {
  let test$a0 = test$a0$copy, test$c = true, test$r;
  while (test$c) { … test$c = false; test$r = n; continue; … }
  return test$r;
};
```
-/


open Language.JavaScript
open Language.JavaScript.MiniAST

/-- A non-empty JavaScript identifier from a string that the backend built. -/
def ident (s : String) : NEString := NEString.ofString! (if s.isEmpty then "_" else s)

/-- `e` as an identifier expression. -/
def var (s : String) : MiniExpr := .ident (ident s)

/-- The JavaScript name of the variable bound in a context of length `depth`. -/
def depthName (depth : Nat) : String := "v" ++ toString depth

/-- The JavaScript name of field number `j` of a constructor: fields are positional,
    and they are numbered from one. -/
def fieldName (j : Nat) : String := "_" ++ toString (j + 1)

/-- The name of the flag of the loop whose body starts at context length `depth`. -/
def loopFlag (depth : Nat) : String := "c$" ++ toString depth

/-- The name of the result of the loop whose body starts at context length `depth`. -/
def loopRes (depth : Nat) : String := "r$" ++ toString depth

/-- The name the runtime prelude binds an extern under. -/
def externName {τ : Ty} (e : LeanPureExtern τ) : String := "$" ++ e.cName

/-- A number literal. -/
def num (n : Nat) : MiniExpr := .number (JSNumber.ofNat n)

/-- An integer literal, negative ones included. -/
def intLit (i : Int) : MiniExpr :=
  if i < 0 then .unary .minus (num i.natAbs) else num i.toNat

/-- `Math.max(0, e)`, for the truncated subtraction of `Nat`. -/
def mathMax0 (e : MiniExpr) : MiniExpr :=
  .call (.dot (var "Math") (ident "max")) [num 0, e]

/-- A literal. -/
def litExpr : ∀ {τ : Ty}, Lit τ → MiniExpr
  | _, .nat n => num n
  | _, .int i => intLit i
  | _, .bool b => if b then .true_ else .false_
  | _, .str s => .string s
  | _, .char c => .string (String.singleton c)
  | _, .float s => .ident (NEString.ofString! s)

/-- The de Bruijn index of a variable, as a number. -/
abbrev varIndex {Γ : Ctx} {τ : Ty} (v : Γ ∋ τ) : Nat := v.index

/-- The curried wrapper of an extern used as a *value* rather than called:
    `(x0) => (x1) => $lean_nat_add(x0, x1)`, so that a partially applied extern still
    reaches the runtime function with all of its arguments at once. -/
def externValue (depth : Nat) {τ : Ty} (e : LeanPureExtern τ) : MiniExpr :=
  let n := e.arity
  let names := (List.range n).map fun i => depthName (depth + i)
  let call : MiniExpr := .call (var (externName e)) (names.map var)
  names.foldr (fun nm acc => .arrow [MiniParam.plain (.ident (ident nm))] (.expr acc)) call

mutual

/-- A term in expression position.  `depth` is the length of the context, so the binder
    `i` de Bruijn steps out is the one at depth `depth - 1 - i`. -/
partial def exprOf (depth : Nat) : ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → MiniExpr
  | _, _, _, .var v => var (depthName (depth - 1 - varIndex v))
  | _, _, _, .lamN (params := ps) b =>
      let n := ps.length
      let names := (List.range n).map (fun i => MiniParam.plain (.ident (ident (depthName (depth + i)))))
      .arrow names (arrowBody (depth + n) b)
  | _, _, _, t@(.apN f args) =>
      match externCall? depth t [] with
      | some e => e
      | none => .call (exprOf depth f) (spineOf depth args)
  | _, _, _, .lamProd (params := ps) rets =>
      let n := ps.length
      let names := (List.range n).map (fun i => MiniParam.plain (.ident (ident (depthName (depth + i)))))
      let vals := spineOf (depth + n) rets
      .arrow names (.block [.return_ (some (.array (vals.map MiniArrayElement.elem)))])
  | _, _, _, .callProd f args i => .index (.call (exprOf depth f) (spineOf depth args)) (num i.val)
  | _, _, _, .lit l => litExpr l
  | _, _, _, .global r => var r.name
  | _, _, _, .extern e => externValue depth e
  | _, _, _, .prim op args => primExpr depth op args
  | _, _, _, .ctor i _ _ args => ctorExpr i (spineOf depth args)
  | _, _, _, .proj e _ j _ => .dot (exprOf depth e) (ident (fieldName j))
  | _, _, _, .tagOf e _ => .dot (exprOf depth e) (ident "tag")
  | _, _, _, t@(.letE ..) => iife (stmtsOf depth t)
  | _, _, _, t@(.caseTag ..) => iife (stmtsOf depth t)
  | _, _, _, t@(.loop ..) => iife (stmtsOf depth t)
  | _, _, _, .ite c t e => .ternary (exprOf depth c) (exprOf depth t) (exprOf depth e)

/-- A call whose head is an extern, printed as **one** call of the runtime function:
    `$lean_nat_add(a, b)`.  It answers `none` when the head is not an extern, or when the
    extern does not get exactly the arguments the runtime function takes — the curried
    wrapper of `externValue` handles that case instead. -/
partial def externCall? (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → List MiniExpr → Option MiniExpr
  | _, _, _, .extern e, args =>
      if args.length == e.arity then some (.call (var (externName e)) args) else none
  | _, _, _, .apN f args, acc => externCall? depth f (spineOf depth args ++ acc)
  | _, _, _, _, _ => none

/-- A primitive, applied to exactly the arguments its type gives it. -/
partial def primExpr (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}, JsPrim σs τ → Spine Sg Γ σs → MiniExpr
  | _, _, _, _, .add _, .cons a (.cons b .nil) => .binary (exprOf depth a) .plus (exprOf depth b)
  | _, _, _, _, .sub _, .cons a (.cons b .nil) => .binary (exprOf depth a) .minus (exprOf depth b)
  | _, _, _, _, .natSub, .cons a (.cons b .nil) =>
      mathMax0 (.binary (exprOf depth a) .minus (exprOf depth b))
  | _, _, _, _, .mul _, .cons a (.cons b .nil) => .binary (exprOf depth a) .times (exprOf depth b)
  | _, _, _, _, .div _, .cons a (.cons b .nil) =>
      .call (.dot (var "Math") (ident "trunc")) [.binary (exprOf depth a) .divide (exprOf depth b)]
  | _, _, _, _, .mod _, .cons a (.cons b .nil) => .binary (exprOf depth a) .mod (exprOf depth b)
  | _, _, _, _, .lt _, .cons a (.cons b .nil) => .binary (exprOf depth a) .lt (exprOf depth b)
  | _, _, _, _, .le _, .cons a (.cons b .nil) => .binary (exprOf depth a) .le (exprOf depth b)
  | _, _, _, _, .gt _, .cons a (.cons b .nil) => .binary (exprOf depth a) .gt (exprOf depth b)
  | _, _, _, _, .ge _, .cons a (.cons b .nil) => .binary (exprOf depth a) .ge (exprOf depth b)
  | _, _, _, _, .beq _, .cons a (.cons b .nil) => .binary (exprOf depth a) .strictEq (exprOf depth b)
  | _, _, _, _, .bne _, .cons a (.cons b .nil) => .binary (exprOf depth a) .strictNeq (exprOf depth b)
  | _, _, _, _, .and, .cons a (.cons b .nil) => .binary (exprOf depth a) .and (exprOf depth b)
  | _, _, _, _, .or, .cons a (.cons b .nil) => .binary (exprOf depth a) .or (exprOf depth b)
  | _, _, _, _, .not, .cons a .nil => .unary .not (exprOf depth a)
  | _, _, _, _, .strAppend, .cons a (.cons b .nil) => .binary (exprOf depth a) .plus (exprOf depth b)
  | _, _, _, _, .strLength, .cons a .nil => .dot (exprOf depth a) (ident "length")
  | _, _, _, _, .strGet, .cons a (.cons i .nil) =>
      .call (.dot (exprOf depth a) (ident "charAt")) [exprOf depth i]
  | _, _, _, _, .toInt32, .cons a .nil => .binary (exprOf depth a) .bitOr (num 0)
  | _, _, _, _, .arraySize _, .cons a .nil => .dot (exprOf depth a) (ident "length")
  | _, _, _, _, .arrayGet _, .cons a (.cons i .nil) => .index (exprOf depth a) (exprOf depth i)
  | _, _, _, _, .arrayPush _, .cons a (.cons x .nil) =>
      .array [.elem (.spread (exprOf depth a)), .elem (exprOf depth x)]
  | _, _, _, _, .arrayEmpty _, .nil => .array []
  | _, _, _, _, .arrayBack _, .cons a .nil =>
      let e := exprOf depth a
      .index e (.binary (.dot e (ident "length")) .minus (num 1))
  | _, _, _, _, .toStr _, .cons a .nil => .call (var "String") [exprOf depth a]
  | _, _, _, _, .natAbs, .cons a .nil => .call (.dot (var "Math") (ident "abs")) [exprOf depth a]
  | _, _, _, _, .cast _ _, .cons a .nil => exprOf depth a

/-- The body of an arrow function: an expression when the term is one, a block when it
    needs statements. -/
partial def arrowBody (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → MiniArrowBody
  | _, _, _, .letE e b => .block (stmtsOf depth (.letE e b))
  | _, _, _, .caseTag s alts h => .block (stmtsOf depth (.caseTag s alts h))
  | _, _, _, .loop init body => .block (stmtsOf depth (.loop init body))
  | _, _, _, .ite c t e => .block (stmtsOf depth (.ite c t e))
  | _, _, _, t => .expr (exprOf depth t)

/-- `(() => { … })()`, for a block in expression position. -/
partial def iife (body : List MiniStatement) : MiniExpr :=
  .call (.arrow [] (.block body)) []

/-- The arguments of a call, in order. -/
partial def spineOf (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → List MiniExpr
  | _, _, _, .nil => []
  | _, _, _, .cons t rest => exprOf depth t :: spineOf depth rest

/-- `{ tag: i, _1: …, _2: … }`: a value of constructor number `i` holding these
    fields, which are named by their position. -/
partial def ctorExpr (i : Nat) (vals : List MiniExpr) : MiniExpr :=
  .object (.keyValue (.ident (ident "tag")) (num i) ::
    vals.zipIdx.map fun (v, j) => MiniProperty.keyValue (.ident (ident (fieldName j))) v)

/-- A term in tail position: a block of statements ending in a `return`. -/
partial def stmtsOf (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → List MiniStatement
  | _, _, _, .letE e b =>
      .decl .const ⟨⟨.ident (ident (depthName depth)), some (exprOf depth e)⟩, []⟩ ::
        stmtsOf (depth + 1) b
  | _, _, _, .ite c t e =>
      [.if_ (exprOf depth c) (.block (stmtsOf depth t)) (some (.block (stmtsOf depth e)))]
  | _, _, _, .caseTag s alts _ =>
      let sc := exprOf depth s
      altStmts depth sc alts
  | _, _, _, .loop init body =>
      let n := spineLen init
      let inits := spineOf depth init
      let decls := (List.range n).map fun i =>
        (⟨.ident (ident (depthName (depth + i))), inits[i]?⟩ : MiniDeclarator)
      let flag := loopFlag depth
      let res := loopRes depth
      let ctl : List MiniDeclarator :=
        [⟨.ident (ident flag), some .true_⟩, ⟨.ident (ident res), none⟩]
      let all := decls ++ ctl
      let declStmt : MiniStatement :=
        match all with
        | [] => .empty
        | d :: ds => .decl .let_ ⟨d, ds⟩
      [ declStmt
      , .while_ (var flag) (.block (bodyStmts (depth + n) depth n body))
      , .return_ (some (var res)) ]
  | _, _, _, t => [.return_ (some (exprOf depth t))]

/-- The branches of a case, as a chain of `if`s on the tag. -/
partial def altStmts (depth : Nat) (sc : MiniExpr) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → List MiniStatement
  | _, _, _, _, .deflt t => stmtsOf depth t
  | _, _, _, _, .cons tag t rest =>
      .if_ (.binary (.dot sc (ident "tag")) .strictEq (num tag))
          (.block (stmtsOf depth t)) none ::
        altStmts depth sc rest

/-- The body of a loop.  `base` is the context length the loop variables start at, and
    `n` is how many of them there are. -/
partial def bodyStmts (depth : Nat) (base : Nat) (n : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → List MiniStatement
  | _, _, _, _, .ret t =>
      [ .expr (.assign (var (loopFlag base)) .assign .false_)
      , .expr (.assign (var (loopRes base)) .assign (exprOf depth t))
      , .continue_ none ]
  | _, _, _, _, .cont args =>
      let vals := spineOf depth args
      -- The new values are computed into temporaries first, so that a loop variable
      -- that appears in a later argument still has its old value.
      let tmps := (List.range n).map fun i => "t$" ++ toString base ++ "$" ++ toString i
      let tmpDecls : List MiniStatement :=
        (List.range n).filterMap fun i =>
          (vals[i]?).map fun v =>
            .decl .const ⟨⟨.ident (ident tmps[i]!), some v⟩, []⟩
      let assigns : List MiniStatement :=
        (List.range n).map fun i =>
          .expr (.assign (var (depthName (base + i))) .assign (var tmps[i]!))
      tmpDecls ++ assigns ++ [.continue_ none]
  | _, _, _, _, .letB e b =>
      .decl .const ⟨⟨.ident (ident (depthName depth)), some (exprOf depth e)⟩, []⟩ ::
        bodyStmts (depth + 1) base n b
  | _, _, _, _, .iteB c t e =>
      [ .if_ (exprOf depth c)
          (.block (bodyStmts depth base n t))
          (some (.block (bodyStmts depth base n e))) ]

/-- How many values a spine holds. -/
partial def spineLen : ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Nat
  | _, _, _, .nil => 0
  | _, _, _, .cons _ rest => spineLen rest + 1

end

/-- One compiled top-level declaration: its JavaScript name and its value.  The value is
    a term of the signature `Sg`, which is the signature the whole module is emitted
    against, so a declaration can only mention names that signature declares. -/
structure JsDecl (Sg : Sig) where
  /-- The name the declaration is bound to, and exported under. -/
  name : String
  /-- Whether the module exports it. -/
  exported : Bool := true
  /-- Its value, as a closed term. -/
  value : Σ τ : Ty, Term Sg [] τ

/-- `const <name> = <value>;` -/
def declStatement {Sg : Sig} (d : JsDecl Sg) : MiniStatement :=
  .decl .const ⟨⟨.ident (ident d.name), some (exprOf 0 d.value.2)⟩, []⟩

/-- A whole compiled module: the declarations, then one `export { … }`. -/
def program {Sg : Sig} (ds : List (JsDecl Sg)) : MiniProgram :=
  let stmts := ds.map fun d => MiniModuleItem.stmt (declStatement d)
  let exported := ds.filter (·.exported) |>.map fun d =>
    ({ name := ident d.name, alias_ := none } : Specifier)
  { items := stmts ++ (if exported.isEmpty then [] else [.exportDecl (.locals exported)]) }

/-- The text of a compiled module. -/
def render {Sg : Sig} (ds : List (JsDecl Sg)) : String := printProgram (program ds)

end LakeJs.EmitJs
