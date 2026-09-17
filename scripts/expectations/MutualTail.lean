import SnapshotsMy.MutualTail
#eval (test1 0, test1 1, test1 2, test1 7)
#eval (test2 0, test2 1, test2 2, test2 7)
#eval (test3 0 5, test3 1 0, test3 5 0, test3 10 1)
#eval (test4 0 5 2, test4 3 0 4, test4 7 1 2)
#eval (test5 0 9, test5 4 0, test5 9 2)
-- `test1 1000000` and `test3 1000000 0` are *not* evaluated here: they are tail calls,
-- but Lean's interpreter does not eliminate them, so it overflows its stack.  The
-- emitted JavaScript is a loop and does answer, which is what the `.test.js` checks.
