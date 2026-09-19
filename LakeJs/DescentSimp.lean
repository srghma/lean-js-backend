module

public import Lean

@[expose] public section

/-!
# The simp set that runs the interpreter

`descent_eval` collects the unfoldings that turn a statement *about a term* into a
statement *about numbers*: the evaluator, the meaning of the runtime's primitives, and the
abbreviations a front end emits for calls of them.  `LakeJs.DescentTactic` populates it and
uses it; it lives in a module of its own because a simp attribute can only be used in a
module later than the one that registers it.

The set is open: a front end that emits new abbreviations tags them `@[descent_eval]` and
the descent tactics pick them up with no change.
-/

register_simp_attr descent_eval

end
