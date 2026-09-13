WE SHOULD add more configurations for our js backend.

How datatypes should be represented:

**Numbers**

- `Nat` — BigInt if backend is configured with `JsNatRepr.bigint` (should pass through LakeJs/JsPrims.lean etc?) OR JS number if backend is configured with `JsNatRepr.num` (default is num)
- `Int` — BigInt if backend is configured with `JsIntRepr.bigint` OR JS number if backend is configured with `JsIntRepr.num` (default is num)
- small fixed-width (`UInt8/16/32`, `Int8/16/32`) — always should be compiled into number
- small big- and maybe-big-width (`USize`, `UInt64`, `Int64`) — should be configured with `JsUSizeRepr`, `JsUInt64Repr`, `JsInt64Repr` (bigint or num too) (default is bigint)
- `Float` / `Float32` — always JS number; (NOTE: for `Float32` operations never do a `Math.fround` after each step in runtime. We dont care much about js code being 100% correct at runtime)

**Scalars**

- `Char` — js always string
- `Bool` — JS boolean
- `String` — JS string

**Data**

- constructor objects — RENDERER SHOULD TAKE CONFIG AND ALLOW TO PRINT constructors as `{tag: "cons", _1, _2}` OR positional array `["cons", a, b]` OR `{tag: 1, …}`
- field naming — RENDERER SHOULD TAKE CONFIG AND ALLOW TO PRINT AS `_1`, `_2` vs the declared field names of the structure
- enum-like inductives (all constructors nullary) — RENDERER (?) SHOULD TAKE CONFIG AND ALLOW TO PRINT AS a plain small integer vs a tagged object
- structures that are isomorphic to `PUnit` — always erased from code or rendered as `undefined`
- one-field structures (aka haskell newtypes) — always unwrapped (NOTE: proofs are always eliminated)
- unit types (`Unit`, `PUnit`, any nullary constructor of a single-constructor type) — always eliminated or replaced with `undefined` if needed
- `Option` — always printed as constructor objects (bc of `some none` ambiguity)
- `List` — RENDERER (?) SHOULD TAKE CONFIG AND ALLOW TO PRINT AS constructor chain (default) vs JS array
- `Array` — JS array; updates are in-place when linearity says it is safe
- erased arguments (types, proofs) — always erased
- IO.RealWorld — always erased

**Totality knobs**

- `Nat` subtraction — SHOULD BE CONFIGURABLE emit the truncation guard vs assume no underflow (default)
- division/modulo by zero — SHOULD BE CONFIGURABLE emit Lean's `= 0` guard vs assume nonzero (default)
- array indexing — trust the `Fin`&proof argument
- array indexing with ! — emit the bounds check

Refine the type lattice (uint8 ⊑ … ⊑ bigint, fin n ⊑ nat ⊑ int ⊑ bigint) and below number (float ⊑ number, float32 ⊑ float) etc.
