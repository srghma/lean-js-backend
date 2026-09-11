-- @js_export: f, g, test1, test2, testImpl, wat, wat1, watUnit
def testImpl (u : Unit) : Unit := u

def test1 : Unit := testImpl ()
def test2 : Unit := testImpl ()
