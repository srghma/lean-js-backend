import LakeJs.Js
import LakeJs.Render
import LakeJs.Optimizer
import LakeJs.JsImplOfKnownExternFunctions.Init.Prelude

open Lean Lean.Compiler.JS

-- Test 1: Fully known list [1, 2, 3]
def list123 := [JS|mkObject(`List.cons, 1, mkObject(`List.cons, 2, mkObject(`List.cons, 3, mkObject(`List.nil))))]
def eval123 := applyInline lean_array_mk #[list123]

#guard eval123 == [JS| [1, 2, 3] ]
#guard renderJs eval123 == "[1, 2, 3]"

-- Test 2: Empty list
def listNil := [JS|mkObject(`List.nil)]
def evalNil := applyInline lean_array_mk #[listNil]

#guard evalNil == [JS| [] ]
#guard renderJs evalNil == "[]"

-- Test 3: Partially known list [10, 20, ...unknownRest]
def listPartial := [JS|mkObject(`List.cons, 10, mkObject(`List.cons, 20, unknownRest))]
def evalPartial := applyInline lean_array_mk #[listPartial]

#guard renderJs evalPartial == "((curr) => {
  const out = [10, 20];
  while ((unknownRest.tag === \"List$cons\")) {
    const head = curr._1;
    const tail = curr._2;
    out.push(head);
    curr = tail;
  }
  return out;
})(unknownRest)"

-- Test 4: Unknown list (runtime argument)
def evalUnknown := applyInline lean_array_mk #[ [JS|inputList] ]

#guard renderJs evalUnknown == "((curr) => {
  const out = [];
  while ((inputList.tag === \"List$cons\")) {
    const head = curr._1;
    const tail = curr._2;
    out.push(head);
    curr = tail;
  }
  return out;
})(inputList)"
