# Coordinator records

These files are copied preparation, authorization and dispatch records. They are
not author observations or an exported agent-session transcript.
`provenance.json` records original paths, copy time and content hashes.

- `prospective-checkpoint.md`: root's acceptance of the frozen protocol and
  private/public boundary, including the completed preparation validation gate.
- `preparation-candidate-command.json`, `preparation-candidate-result.json` and
  `preparation-candidate.log`: exact command, commit, UTC bounds, exit status and
  raw output of the committed preparation check.
- `preparation-verify.json`, `preparation-verify.log` and
  `preparation-verification-record.json`: successful record verification and its
  captured record for preparation commit
  `72607d73206b4be824c688aab738bb4f4493bb66`.
- `dispatch-initial.json`: a snapshot of root's initial dispatch record. It gives
  exact route messages, launch bounds and configuration, and records concurrent
  host activity. It does not provide author start/finish times or outcomes.

Later dispatch/closure records should use new filenames, preserving this initial
snapshot. Closed author attempts, self-reports and raw shell evidence belong in
separate author archives. Any packaging changes must follow preservation of
their original bytes. The freeze manifest remains an unchanged prospective
record even after dispatch and integration advance.
