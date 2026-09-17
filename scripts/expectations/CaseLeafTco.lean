import SnapshotsPBOPure.CaseLeafTco
#eval test1FuelCalled true #[]
#eval test1FuelCalled false #[]
#eval test1FuelCalled false #[1, 2]
#eval test1FuelCalled true #[5]
#eval test1Fuel 0 false #[7, 8]
#eval test1Fuel 1 false #[7, 8]
#eval (test1Fuel 2 false #[7, 8]).size
