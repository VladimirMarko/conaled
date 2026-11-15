# Body-realization client correction r1

Source-only author correction for local10022, 2026-11-03, within the retained
implementation/review loop. Parent-supplied starting commit:
`6971fd2a9647d077594ad66f24b5d0f29641cc5b`.

The terminal focused round r4 is retained in
`validation/body-entry-counts-r4.json` and `.log`: exit1, all71 inputs unchanged.
The actual client diagnostics were maximum recursion depth while matching the
public fifty-step count to `bodyEntries`, and the remaining literal goal
`[0, 0].length = 2`. The core bridge and other targets had compiled.

Only two proof bodies in `Examples/SuspensionBodyRealization.lean` changed:

- `ExternalHandler.not_nodup` now composes `bodyEntries_eq_count` with the
  existing public `two_attempts_without_write.1` proof. `simpa only [events]`
  expands just the local trace abbreviation when matching that count. This
  avoids asking direct definitional equality to discover the count bridge
  through the concrete execution.
- `retry_separates_occurrences_and_support` explicitly simplifies
  `List.length_cons` and `List.length_nil` after applying the existing projected
  list equality. The two-element length expectation remains2.

Statement review: no declaration type, premise, source program, capture,
observation budget, address identity or independently expected count changed.
The same public source observation still supplies body/write/hit2/0/0 at50
steps. The Nodup contradiction and the distinction between occurrence count2
and support/interpreter charge1 remain connected to the public bridge laws.
The compiled core and original handoff report were not edited.

No compiler, audit, stock hash adapter, Git mutation, cache operation or tracker
change was performed. No proof-budget increase or suppression was introduced.
The correction is uncompiled and unaccepted; root owns nine-target focused r5
and all subsequent gates.

Frozen client SHA256:
`2aed95a1b467bb196578009e16cf02c429e0f153a3da1b7b22d796661b2a4abb`.
