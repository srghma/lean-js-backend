import SnapshotsPBOPure.Fusion01

#eval test #[0, 1, 2, 10, 11, 100]
#eval test #[]
#eval test #[5]
#eval (dropPrefix1 "123", dropPrefix1 "23", dropPrefix1 "1")
#eval toArray (fromArray #[1, 2, 3])
#eval overArray (mapF (· * 2)) #[1, 2, 3]
#eval overArray (filterF (· > 1)) #[1, 2, 3]
#eval overArray (filterMapF (fun a => if a > 1 then some (a + 10) else none)) #[1, 2, 3]
