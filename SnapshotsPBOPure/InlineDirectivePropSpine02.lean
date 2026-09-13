-- @js_export: f, g, test1, test2, testImpl, wat1, wat2, watUnit, watUnit1
def testImpl (u : Unit) : Unit := u

def test1 : Unit := testImpl ()
def test2 : Unit := testImpl ()
