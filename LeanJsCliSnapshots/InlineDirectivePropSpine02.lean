def testImpl (u : Unit) : Unit := u

def test1 : Unit := testImpl ()
def test2 : Unit := testImpl ()
