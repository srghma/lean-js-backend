This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# lean-glob

check TypedPath: for now only PosixPath allows/disallowes .. or . inside (WindowsPath - no), I am still thinking if this is ok UI.

TODO: rename patternStrict! elab for glob to glob! (this is glob that doesnt allow to write `**/*/foo`, but only `*/**/foo`)
