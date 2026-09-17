import SnapshotsMy.StringWalk
#eval (test1 "banana" 'a', test1 "" 'a', test1 "héllo" 'l')
#eval ((test2 "banana" 'n').byteIdx, (test2 "héllo" 'l').byteIdx, (test2 "abc" 'z').byteIdx)
#eval (test4 "", test4 "abcd", test4 "héllo")
#eval (test3 "ab" 0, test3 "ab" 3, test3 "é" 2)
