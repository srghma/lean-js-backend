Reading through `Expr.lean` carefully, most of it is airtight by construction — the type indices (`n`, `g`) rule out scope errors and opaque-name invention as type errors rather than bugs to hunt for, and the mutual size/mentions/mono functions are all straightforwardly structural. But there's one real gap I'd flag, in the push-loop recognizer at the bottom:

```lean
def Branches.pushShapeOk {fam : LeanRecFamily} {n : Nat} : Branches fam n g → Bool
  | .nil             => true
  | .cons c _ body t =>
      (match body with
       | .arr elems =>
           if c.numRecFields == 1 then
             elems.isPushShape (n + (c.recFieldIdxs.headD 0))
           else true
       | _ => false)
      && pushShapeOk t

def Branches.isPushFold {n : Nat} (fam : LeanRecFamily) (bs : Branches fam n g) : Bool :=
  (fam.allCtors.filter (fun c => c.numRecFields == 1)).length == 1
    && fam.allCtors.all (fun c => bs.hasTag c.name)
    && bs.pushShapeOk
```

**The linearity check is too weak.** `isPushFold`'s first condition only asserts that *exactly one* constructor has `numRecFields == 1` — it says nothing about the other constructors. A constructor with `numRecFields == 0` is fine (that's the base case). But a constructor with `numRecFields == 2` (or more) — a genuinely branching shape, e.g. a family mixing a list-like `cons` with a binary `node(l, x, r)` — would pass this filter untouched, since it's neither counted nor excluded.

Then in `pushShapeOk`, for that same 2-rec-field constructor, the `else true` branch fires (since `c.numRecFields == 1` is false), so the only requirement on its body is that it's *some* array literal — `isPushShape` (which checks for a single trailing `...rest` spread of exactly the folded tail) is never invoked. So a hybrid family like `A (0 rec) | B (1 rec) | C (2 rec)` with array-literal branches for all three would satisfy `isPushFold == true`, even though the value being folded isn't a linear chain and can't correctly be walked by a single-cursor `while` loop the way the docs describe (`_c0 = _c0._2` style).

I don't have `Render.lean` in front of me, so I can't confirm whether this actually produces wrong JavaScript (it's possible the renderer has its own additional guard, or that `LeanRecFamily`'s invariants elsewhere happen to preclude this shape from ever reaching here) — but as written, `isPushFold` doesn't look like a sound witness of "this family is linear." The fix would be to require every *other* constructor to have `numRecFields == 0`, e.g.:

```lean
fam.allCtors.all (fun c => c.numRecFields == 0 || c.numRecFields == 1)
  && (fam.allCtors.filter (fun c => c.numRecFields == 1)).length == 1
```

Everything else I looked at — `Expr.mentions`, `Expr.mono`, `Expr.size`/`size_pos`, `ObjProps.find?`'s shadowing order, `ExprList.isPushShape`'s spread check, `Branches.consTag`'s arity cast — is structurally consistent with what the docstrings claim. If you want, I can go through `Render.lean` (where `isPushFold` actually gets consumed) to check whether this gap is exploitable in practice or already neutralized upstream.
