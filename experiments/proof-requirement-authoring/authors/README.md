# Closed author attempts

`manual/` and `assisted/` preserve all files from each author's closed `attempts/`
directory. `provenance.json` records source locations, copy time, public handoff
HEADs and SHA-256 hashes for every original file. `integration.json` maps the
successful submissions to integrated modules and confirms no byte changes.

Manual submitted three checks: E passed, the first combined E/W source failed
elaboration, and the repaired combined source passed. Assisted submitted two
passing checks: E, then E/W. These are successive task development snapshots,
not independent samples. Failed sources remain evidence and are excluded from
the integrated module graph. Raw logs are explicitly tracked despite the
repository's log-file ignore pattern.

Author `outcome.md`, `session-metadata.md` and `commands.txt` are self-reports and
authored transcripts. The numbered `checks/` directories contain exact source
snapshots, commands, SHA-256 values, UTC start/finish times, exit statuses and raw
Lean diagnostics from the frozen wrapper. Manual also retained raw outer wrapper
output. No raw agent-session export was available; these records are not a
replacement presented as such. Coordinator assessment lives in `../evaluation/`.
