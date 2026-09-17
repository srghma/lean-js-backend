import SnapshotsPBOPure.Fusion02

#eval test #[0, 9, 10, 1]
#eval test #[0, 1, 2, 10, 11, 100]
#eval test #[]
#eval (dropPrefix1 "123", dropPrefix1 "23", dropPrefix1 "1")
#eval toArray (fromArray #[1, 2, 3])
#eval overArray (mapU (· * 2)) #[1, 2, 3]
#eval overArray (filterU (· > 1)) #[1, 2, 3]
