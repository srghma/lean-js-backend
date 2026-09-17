import SnapshotsPBOPure.CaptureDerefRegression01
#eval (test1 (3, 4) 10, test1 (-5, 0) 2)
#eval (test2 (3, 4) 10, test3 (3, 4) |>.1 10)
#eval ((test4 (3, 4)).1 100, (test4 (3, 4)).2 100)
-- `Box2` is private, so `testEven`/`testOdd` and `test5` cannot be applied from here;
-- their expected values are worked out in the `.test.js` file from their definitions.
