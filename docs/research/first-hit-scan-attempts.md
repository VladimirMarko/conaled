# First-hit scan attempt record

The chosen consumer and expected values remained fixed throughout issue #590.
The initial draft tried the identifier `prefix`, which is a Lean parser keyword,
and an unavailable Mathlib array import. Renaming it to `sumPrefix` and using
already imported core array lemmas resolved these encoding errors. They were
not failures of the scan specification or evidence for a new test language.

The finite source derivation initially attempted induction directly on a
`runUntil_spec` whose output index was a compound expression. Generalizing the
output to a variable made the induction applicable. Two sum equations also
required reassociation and commutation of natural addition. The native runner
needed the qualified name `MeasuredLoop.run` to avoid the list workload runner
in its enclosing namespace.

The array specialization initially tried rewriting a theorem indexed by
`data.size` into a goal indexed by the numeral `4`. An explicit definitional
`change` exposed the same size expression before rewriting. No new hypothesis,
weaker observation, recursion setting or heartbeat increase was needed.

There was no mathematical obstruction in this experiment. The rejected
post-read convention and changed-read client remain checked counterexamples
in `Examples/FirstHitScan.lean`; they are not failed elaboration experiments.
