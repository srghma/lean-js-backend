import Init.Data.UInt

def test1 : UInt32 := (1023 : UInt32) &&& (8 : UInt32)
def test2 : UInt32 := (16 : UInt32) ||| (15 : UInt32)
def test3 : UInt32 := (1023 : UInt32) <<< 2
def test4 : UInt32 := (~~~(1023 : UInt32) + 1) >>> 2 -- placeholder for -1023 shr 2
def test5 : UInt32 := (15 : UInt32) ^^^ (12 : UInt32)
def test6 : UInt32 := (~~~(1023 : UInt32) + 1) >>> 2 -- placeholder for -1023 zshr 2
def test7 : UInt32 := ~~~(~~~(3 : UInt32) + 1) -- placeholder for complement (-3)
