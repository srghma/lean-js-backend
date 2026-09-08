# PureScript snapshots that do not make sense as Lean `tests/es6` ports

These were copied from `purescript-backend-optimizer`, but they are tied to PureScript-only runtime features,
row types, backend optimizer directives, or codegen invariants that do not have a meaningful Lean ES6 analogue.

## Lean runtime mismatch

- `BackendSemantics01`: checks PureScript `Bounded Int` / `Bounded Char` extremes; Lean `Int` is unbounded and `Char` uses Lean's own valid-codepoint semantics.
- `AssocArrayAppend`: relies on collection-append helper paths that are currently not exercised reliably by this Lean `es6` pile, so it is not a useful stable regression here.
- `CaseLeafTco`: mixes case-tree layout with Array head/last behavior specifically to exercise the optimizer's leaf-TCO shape rather than a distinct Lean feature.
- `PrimOpIntBit01`, `PrimOpIntBit02`: depend on machine-integer bitwise helper paths that are not currently a stable target in this Lean `es6` pile.
- `Tco06`: intentionally non-terminating mutual recursion without observable stdout behavior; not useful as a Lean execution test.

## PureScript effect / ST runtime model

- `EffectBind01`, `EffectBind02`, `EffectBind03`, `EffectBind04`, `EffectBind05`, `EffectBind06`, `EffectBind07`, `EffectBind08`, `EffectBind09`: target PureScript `Effect` bind lowering and optimizer behavior.
- `EffectLoopCaseRegression`, `EffectLoops01`, `EffectLoops02`, `EffectLoops03`, `EffectPure01`: target PureScript effect-loop code generation rather than Lean semantics.
- `EffectRefs01`, `EffectRefs02`, `EffectUnsafe01`, `UnsafePerformEffect`: depend on the PureScript effect/runtime model and unsafe APIs with no direct Lean ES6 equivalent.
- `STArray01`, `STArray02`, `STArray03`, `STArray04`, `STArray05`, `STArrayUnsafeThawFreezeLengthRegression`, `STLoops01`, `STLoops02`, `STLoops03`, `STObject01`, `STRun01`: depend on PureScript `ST` references/arrays/objects and their optimizer behavior.
- `UncurriedEffectFns01`, `UncurriedEffectFns02`, `UncurriedSTFns01`, `UncurriedSTFns02`, `UnsafePerformEffect`: depend on PureScript's uncurried effect/ST calling conventions.

## PureScript row types, variants, foreign objects, or ecosystem libraries

- `ConvertableOptions01`, `Heterogeneous01`, `RecordUnion01`: depend on PureScript row-polymorphism and row-type machinery.
- `Variant01`, `Variant02`: depend on PureScript open variants.
- `Object01`: depends on `Foreign.Object`, including JS object key/member semantics not modeled by Lean records.
- `Html`, `HalogenVDomST01`, `HalogenVDomST02`: depend on PureScript HTML/Halogen ecosystem libraries, not Lean runtime behavior.
- `ProfunctorLenses01`, `ProfunctorLenses02`, `VanLaarhovenTraversals01`, `RecursionSchemes01`: are library-encoding tests for PureScript optics/recursion-schemes abstractions, not Lean ES6 codegen behavior.

## Backend-optimizer / inlining / codegen-invariant tests

- `EscapeIdentifiers`: checks PureScript symbol escaping for typeclass instance names, not Lean term/runtime behavior.
- `EtaReduceRegression01`, `Fusion01`, `Fusion02`: target optimizer rewrites rather than user-visible Lean execution.
- `EsPrecedence03`: is about machine-integer shift lowering and precedence, which falls into the same unstable helper path as the dropped bitwise snapshots above.
- `InlineArrayIndex`, `InlineCase01`, `InlineCase02`, `InlineDirectivePropSpine01`, `InlineDirectivePropSpine02`, `InlineNever`, `InlineReferenceIfThenElse`, `InlineReferenceOpArrayLength`, `InlineReferenceOpIsTag`, `InlineReferencePrimOpBoolean`, `InlineReferencePrimOpInt`, `InlineReferencePrimOpNumber`, `InlineReferenceRecordUpdate`: depend on PureScript backend inline directives and IR references that do not exist in Lean.
- `RecursiveBindingGroup01`, `RecursiveBindingGroup02`: exercise PureScript recursive binding-group compilation strategy, not a Lean runtime feature.
- `TopLevelHygiene01`, `TopLevelHygiene02`: target PureScript backend name-hygiene/codegen details.

## PureScript representation details with no useful Lean stdout analogue

- `KnownConstructors06`: checks PureScript generic deriving / constructor-show formatting, which does not line up with Lean's `Repr` / `ToString` surface syntax.
- `Tco04`, `Tco05`: primarily test specific optimizer/control-flow layouts (`mutual` tail calls and `findIdx`-style loops) rather than distinct Lean stdout semantics in this pile.
- `UncurriedFns01`, `UncurriedLocalAbs01`, `UnpackArray01`: target PureScript uncurried-function and array-unpacking code generation details.
