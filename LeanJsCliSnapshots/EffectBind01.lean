-- all datatypes that are iso to PUniq.unit will be rendered as `null`.
def test1 : IO Unit := do
  IO.println "1"
  let value ← IO.println "2" -- since we know that `value` is JS `null` - it will be optimized away.
  IO.println "3"
  pure value -- just return `null`
