| Variant                             | Constructors | Fields per Constructor | Lean Syntax Equivalent                 | Examples                                   |
| :---------------------------------- | :----------- | :--------------------- | :------------------------------------- | :----------------------------------------- | ------------------- |
| **Empty Type**                      | 0            | None                   | `inductive Empty : Type`               | `Empty`, `False`                           | ❌ Cannot be mutual |
| **Unit / Singleton**                | 1            | 0 fields               | `inductive Unit \| unit`               | `Unit`, `PUnit`, `True`                    | ❌ Cannot be mutual |
| **Newtype / Wrapper**               | 1            | 1 field                | `structure` or 1-ctor `inductive`      | `inductive Id (α : Type) \| mk : α → Id α` | Can be mutual       |
| **Record / Product**                | 1            | $\ge 1$ fields         | `structure` (preferred) or `inductive` | `Prod α β`, `Point`                        |
| **Enumeration (Enum)**              | $\ge 2$      | 0 fields               | `inductive` with bare tags             | `Bool`, `Ordering`                         |
| **Algebraic Data Type (ADT / Sum)** | $\ge 2$      | Arbitrary fields       | `inductive`                            | `Option α`, `Except ε α`, `List α`         |

# Empty type

```lean
inductive Void where
```

> should be eliminated

# Non-recursive enum

```lean
inductive Direction | north | south | east | west
```

> should be compiled to `0, 1, 2, 3` or `"north", "south", "east", "west"` (based on config)

# Non-recursive structure

```lean
structure Point where
  x : Float
  y : Float
```

> should be compiled to `{ _x: ..., _y: ... }` or `{ _1: ..., _1: ... }` (based on config)

```lean
structure PointInner where
  x : Float
  y : Float

structure Point where
  p : PointInner
  z : Float
```

> should be compiled to `{ _p: { _x: ..., _y: ... }, _z: ... }` or `{ _1: { _1: ..., _2: ... }, _2: ... }` (based on config)

# Directly Recursive

```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α
```

> these are built in, but usually should be compiled to JS objects. E.g. `{ tag: "nil" } | { tag: "cons", _1: ..., _2: ... }`

# Enum but in mutual block

```lean
-- Syntactically allowed in a `mutual` block, but NO recursion is happening:
mutual
  inductive Color | red | blue   -- Has no fields to reference Shape!
  inductive Shape | circle | box  -- Has no fields to reference Color!
end
```

> though they are in mutual block - the `LeanRecCtorSchema` should be `.nonMutual`. And they cannnot be in a family with many inductives


..TODO continue
