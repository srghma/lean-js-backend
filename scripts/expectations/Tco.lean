import SnapshotsPBOPure.Tco01
import SnapshotsPBOPure.Tco03
import SnapshotsPBOPure.Tco05
import SnapshotsPBOPure.Tco06
#eval (test 0, test 5, test 100)
#eval (go 0, go 5, go 100, go 101, go 1000)
#eval (k 100 (by omega), k 101 (by omega), k 900 (by omega), k 1000 (by omega))
#eval (span (· > 0) #[1,2,3], span (· > 0) #[1,-2,3], span (· > 0) #[], span (· < 0) #[1])
#eval (f 0 3 4, f 1 3 4, f 5 1 1, g 0 7, g 1 7, g 4 2)
