# --------------------------------------------------------------- Externs: Int.toNat
p = 'LakeJs/Externs.lean'
s = open(p).read()
anchor = '''-- | lean_int_dec_le          | def         | Int.decLe         | (a : @& Int) \u2192 (b : @& Int) \u2192 Decidable (Int.instLEInt.le a b) |'''
row = '''-- | lean_int_to_nat          | def         | Int.toNat         | (@& Int) \u2192 Nat                                                 |
  | lean_int_to_nat          : Externs [.int] .nat
''' + anchor
assert anchor in s
s = s.replace(anchor, row, 1)
open(p, 'w').write(s)

# --------------------------------------------------------------- EmitJs: two fixes
p = 'LakeJs/EmitJs.lean'
s = open(p).read()
s = s.replace('''  | _, _, .lean_nat_blt, [a, b] => some (.binary a .lt b)\n''', '')
s = s.replace('''  -- `Int.natAbs`''',
              '''  -- `Int.toNat`, which truncates a negative integer to zero
  | _, _, .lean_int_to_nat, [a] => some (mathMax0 a)
  -- `Int.natAbs`''')
open(p, 'w').write(s)

# --------------------------------------------------------------- FromLcnf
p = 'LakeJs/FromLcnf.lean'
s = open(p).read()

s = s.replace('''* an operation the backend prints inline becomes `Term.prim`, whose `JsPrim` is indexed
  by the types of its arguments, so it is applied to exactly the arguments it takes \u2014 a
  constant like `instDecidableEqString` used as a *value* is eta-expanded into
  `(v0, v1) => v0 === v1` rather than printed as a call of no arguments;''',
'''* the few operations that are not Lean functions at all \u2014 a reinterpretation of a value
  at another type, `Bool.and`, and the rest of `JsOp` \u2014 become `Term.jsOp`, which is
  indexed by the types of its arguments in the same way, so it too is applied to exactly
  the arguments it takes;  a constant like `instDecidableEqString` used as a *value* is
  eta-expanded into `(v0, v1) => v0 === v1` rather than printed as a call of no
  arguments;''')

start = s.index("/-! ## Primitives -/")
end = s.index("/-! ## Class instances")
new = '''/-! ## The operations a call is translated into directly

A call of one of the declarations below is not a call of anything the module declares:
it is the operation itself, applied to the arguments of the call.  Almost every one of
them is a Lean function the runtime implements, and so a row of the catalogue
`LakeJs.Externs` \u2014 `Nat.add` is `lean_nat_add`, and `LakeJs.EmitJs` decides whether that
prints as `a + b` or as a call of the runtime function.  The handful that are *not*
`@[extern]` functions are the `JsOp` of `LakeJs.Expr`. -/

/-- An operation a call becomes directly: a Lean function of the extern catalogue, or one
    of the few operations that are not Lean functions. -/
inductive DirectOp : List Ty \u2192 Ty \u2192 Type where
  /-- A function Lean implements with `@[extern]`. -/
  | ext : \u2200 {\u03c3s : List Ty} {\u03c4 : Ty}, Externs \u03c3s \u03c4 \u2192 DirectOp \u03c3s \u03c4
  /-- An operation that is JavaScript\u2019s rather than Lean\u2019s. -/
  | js : \u2200 {\u03c3s : List Ty} {\u03c4 : Ty}, JsOp \u03c3s \u03c4 \u2192 DirectOp \u03c3s \u03c4

/-- The operation applied to exactly the arguments its type asks for. -/
def DirectOp.apply {Sg : Sig} {\u0393 : Ctx} {\u03c3s : List Ty} {\u03c4 : Ty} :
    DirectOp \u03c3s \u03c4 \u2192 Spine Sg \u0393 \u03c3s \u2192 Term Sg \u0393 \u03c4
  | .ext e, args => .callExtern e args
  | .js o, args => .jsOp o args

/-- An operation together with the types it is applied at. -/
structure SomeDirect where
  /-- The types of its arguments. -/
  {\u03c3s : List Ty}
  /-- What it answers with. -/
  {\u03c4 : Ty}
  /-- The operation. -/
  op : DirectOp \u03c3s \u03c4

/-- The Lean declarations a call becomes an operation of, and which operation \u2014 at the
    types of the call it is looking at, since both `Externs` and `JsOp` carry them.

    A name that is missing here is not missing from the backend: a call of any other
    `@[extern]` function is recognised further down (`externFor?`), and printed as a call
    of the runtime function.  What this table adds is the *shape*: the operation is
    applied to the arguments of the call at once, and is eta-expanded where the call is
    partial. -/
def directFor (n : Name) (argTys : List Ty) (ret : Ty) : Option SomeDirect :=
  let arg (i : Nat) : Ty := argTys[i]?.getD Ty.typeParam
  let elemOf : Ty \u2192 Ty := fun t => match t with | .array \u03b1 => \u03b1 | _ => Ty.typeParam
  match n with
  | ``Nat.add => some \u27e8.ext .lean_nat_add\u27e9
  | ``Nat.mul => some \u27e8.ext .lean_nat_mul\u27e9
  | ``Nat.sub => some \u27e8.ext .lean_nat_sub\u27e9
  | ``Nat.div => some \u27e8.ext .lean_nat_div\u27e9
  | ``Nat.mod => some \u27e8.ext .lean_nat_mod\u27e9
  | ``Nat.pred => some \u27e8.ext .lean_nat_pred\u27e9
  | ``Nat.beq => some \u27e8.ext .lean_nat_beq\u27e9
  | ``Nat.decEq | ``instDecidableEqNat => some \u27e8.ext .lean_nat_dec_eq\u27e9
  | ``Nat.ble => some \u27e8.ext .lean_nat_ble\u27e9
  | ``Nat.decLe => some \u27e8.ext .lean_nat_dec_le\u27e9
  -- Lean implements `Nat.blt` with the runtime function of `Nat.decLt`
  | ``Nat.blt | ``Nat.decLt => some \u27e8.ext .lean_nat_dec_lt\u27e9
  | ``Int.add => some \u27e8.ext .lean_int_add\u27e9
  | ``Int.sub => some \u27e8.ext .lean_int_sub\u27e9
  | ``Int.mul => some \u27e8.ext .lean_int_mul\u27e9
  | ``Int.neg => some \u27e8.ext .lean_int_neg\u27e9
  | ``Int.decEq => some \u27e8.ext .lean_int_dec_eq\u27e9
  | ``Int.decLt => some \u27e8.ext .lean_int_dec_lt\u27e9
  | ``Int.decLe => some \u27e8.ext .lean_int_dec_le\u27e9
  | ``Int.ofNat => some \u27e8.ext .lean_nat_to_int\u27e9
  | ``Int.toNat => some \u27e8.ext .lean_int_to_nat\u27e9
  | ``Int.natAbs => some \u27e8.ext .lean_nat_abs\u27e9
  -- `Bool.and`, `Bool.or` and `Bool.not` are Lean functions, but not `@[extern]` ones
  | ``Bool.and => some \u27e8.js .boolAnd\u27e9
  | ``Bool.or => some \u27e8.js .boolOr\u27e9
  | ``Bool.not => some \u27e8.js .boolNot\u27e9
  | ``String.append => some \u27e8.ext .lean_string_append\u27e9
  -- `String.push` is *not* string concatenation: its second argument is a `Char`, which
  -- is not a `String`, so it goes to the extern `lean_string_push` instead
  | ``String.length => some \u27e8.ext .lean_string_length\u27e9
  | ``String.decEq | ``instDecidableEqString => some \u27e8.ext .lean_string_dec_eq\u27e9
  -- Lean decides `Bool` and `Char` equality by a match rather than with a runtime
  -- function, and both are `===` on the representation the backend gives them
  | ``instDecidableEqBool => some \u27e8.js .boolBEq\u27e9
  | ``instDecidableEqChar => some \u27e8.js .charBEq\u27e9
  | ``Array.size => some \u27e8.ext (.lean_array_get_size (elemOf (arg 0)))\u27e9
  | ``Array.push => some \u27e8.ext (.lean_array_push (elemOf (arg 0)))\u27e9
  | ``Array.getInternal => some \u27e8.ext (.lean_array_fget (elemOf (arg 0)))\u27e9
  | ``Array.mkEmpty | ``Array.emptyWithCapacity =>
      some \u27e8.ext (.lean_empty_array_with_capacity
        (match ret with | .array \u03b1 => \u03b1 | _ => Ty.typeParam))\u27e9
  | ``UInt8.add => some \u27e8.ext .lean_uint8_add\u27e9
  | ``UInt16.add => some \u27e8.ext .lean_uint16_add\u27e9
  | ``UInt32.add => some \u27e8.ext .lean_uint32_add\u27e9
  | ``UInt64.add => some \u27e8.ext .lean_uint64_add\u27e9
  | ``USize.add => some \u27e8.ext .lean_usize_add\u27e9
  | ``UInt8.sub => some \u27e8.ext .lean_uint8_sub\u27e9
  | ``UInt16.sub => some \u27e8.ext .lean_uint16_sub\u27e9
  | ``UInt32.sub => some \u27e8.ext .lean_uint32_sub\u27e9
  | ``UInt64.sub => some \u27e8.ext .lean_uint64_sub\u27e9
  | ``USize.sub => some \u27e8.ext .lean_usize_sub\u27e9
  | ``UInt32.mul => some \u27e8.ext .lean_uint32_mul\u27e9
  | ``UInt64.mul => some \u27e8.ext .lean_uint64_mul\u27e9
  | ``UInt32.decEq => some \u27e8.ext .lean_uint32_dec_eq\u27e9
  | ``UInt64.decEq => some \u27e8.ext .lean_uint64_dec_eq\u27e9
  | ``Float.add => some \u27e8.ext .lean_float_add\u27e9
  | ``Float.sub => some \u27e8.ext .lean_float_sub\u27e9
  | ``Float.mul => some \u27e8.ext .lean_float_mul\u27e9
  | ``Float.div => some \u27e8.ext .lean_float_div\u27e9
  | ``Float.decLt => some \u27e8.ext .lean_float_decLt\u27e9
  | ``Float.decLe => some \u27e8.ext .lean_float_decLe\u27e9
  -- deciding a proposition and reading the answer as a boolean costs nothing at run time
  | ``Decidable.decide => some \u27e8.js (.cast (arg 0) ret)\u27e9
  | ``toString => some \u27e8.js (.toStr (arg 0))\u27e9
  | _ => none

'''
s = s[:start] + new + s[end:]

reps = [
("""  match primFor n argTys ty with
  | some p =>
      if ts.length == p.\u03c3s.length then
        return \u27e8p.\u03c4, .jsOp p.op (\u2190 mkSpine p.\u03c3s ts)\u27e9""",
 """  match directFor n argTys ty with
  | some p =>
      if ts.length == p.\u03c3s.length then
        return \u27e8p.\u03c4, p.op.apply (\u2190 mkSpine p.\u03c3s ts)\u27e9"""),
("""        return \u27e8.fn p.\u03c3s p.\u03c4, .lamN (.jsOp p.op (\u2190 mkSpine p.\u03c3s vars))\u27e9""",
 """        return \u27e8.fn p.\u03c3s p.\u03c4, .lamN (p.op.apply (\u2190 mkSpine p.\u03c3s vars))\u27e9"""),
("""          return \u27e8Ty.nat, .jsOp (.add .nat) (.cons (coerce Ty.nat a) (.cons one .nil))\u27e9""",
 """          return \u27e8Ty.nat, .callExtern .lean_nat_add
            (.cons (coerce Ty.nat a) (.cons one .nil))\u27e9"""),
("""          return \u27e8Ty.int, .jsOp (.sub .int) (.cons minusOne (.cons (coerce Ty.int a) .nil))\u27e9""",
 """          return \u27e8Ty.int, .callExtern .lean_int_sub
            (.cons minusOne (.cons (coerce Ty.int a) .nil))\u27e9"""),
("""        .jsOp .natSub (.cons (coerce Ty.nat d) (.cons (.lit (.nat 1)) .nil))""",
 """        .callExtern .lean_nat_sub (.cons (coerce Ty.nat d) (.cons (.lit (.nat 1)) .nil))"""),
("""    let pred : Term Sg \u0393 Ty.nat := .jsOp .natSub (.cons dNat (.cons (.lit (.nat 1)) .nil))""",
 """    let pred : Term Sg \u0393 Ty.nat :=
      .callExtern .lean_nat_sub (.cons dNat (.cons (.lit (.nat 1)) .nil))"""),
("""      .jsOp (.beq .nat) (.cons dNat (.cons (.lit (.nat 0)) .nil))""",
 """      .callExtern .lean_nat_dec_eq (.cons dNat (.cons (.lit (.nat 0)) .nil))"""),
("""      coerce Ty.nat \u27e8Ty.int, .jsOp (.sub .int) (.cons (.lit (.int (-1))) (.cons v .nil))\u27e9""",
 """      coerce Ty.nat
        \u27e8Ty.int, .callExtern .lean_int_sub (.cons (.lit (.int (-1))) (.cons v .nil))\u27e9"""),
("""      .jsOp (.lt .int) (.cons (coerce Ty.int d) (.cons (.lit (.int 0)) .nil))""",
 """      .callExtern .lean_int_dec_lt (.cons (coerce Ty.int d) (.cons (.lit (.int 0)) .nil))"""),
("""        .jsOp (.beq .nat) (.cons (\u2190 tagAt d) (.cons (.lit (.nat idx)) .nil))""",
 """        .callExtern .lean_nat_dec_eq (.cons (\u2190 tagAt d) (.cons (.lit (.nat idx)) .nil))"""),
("""    wrapped in `JsPrim.cast`, which prints as the term itself.""",
 """    wrapped in `JsOp.cast`, which prints as the term itself."""),
("""    `JsPrim.cast`. -/""", """    `JsOp.cast`. -/"""),
]
for a, b in reps:
    assert a in s, a[:70]
    s = s.replace(a, b)
open(p, 'w').write(s)

# --------------------------------------------------------------- Simp / Rename docs
p = 'LakeJs/Simp.lean'
s = open(p).read()
s = s.replace("/-- Read a term at the type a `JsPrim.cast` expects.",
              "/-- Read a term at the type a `JsOp.cast` expects.")
open(p, 'w').write(s)
p = 'LakeJs/Rename.lean'
s = open(p).read()
s = s.replace("the term `JsPrim.cast` builds from it.", "the term `JsOp.cast` builds from it.")
open(p, 'w').write(s)
print('ok')
