import SnapshotsMy.HashContainers

#eval (test1 [], test1 ["a"], test1 ["a", "b", "a"])
#eval (test2 [], test2 [3], test2 [1, 2, 3, 4])
#eval (test3 [], test3 ["a"], test3 ["b", "c"], test3 ["a", "a", "b"])
#eval (test4 [], test4 ["a"], test4 ["a", "b", "a"])
#eval (test5 [], test5 ["a"], test5 ["a", "b"], test5 ["a", "b", "c"])
#eval (test7 [] "a", test7 ["ab", "c"] "ab", test7 ["ab", "c"] "zz")
#eval (test6 [], test6 ["a"], test6 ["a", "b", "a"], test6 ["b", "a"])
