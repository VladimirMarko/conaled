# Frozen author handoff

This is an assigned author trial in an existing implementation/review loop.
Read `protocol.md`, `tasks/common.md` and `tasks/arm.md` before authoring. For
formal work read `guidance/example-driven-development.md` and
`guidance/worked-example.md`; for architectural judgments read
`guidance/architectural-quality.md` and `guidance/language-direction.md`; before
outcome prose read `guidance/no-ai-slop.md` and its bundled reference. Links in
these copied documents do not expand the public allowlist.

Use the pinned Nix shell through `direnv exec .`. The coordinator already
allowed direnv and built the permitted source closure. Run every Lean attempt
through `direnv exec . python3 check_attempt.py attempts/AttemptNN.lean`, with a
new name for every revision. Write only in `attempts/`. Keep exact attempted
bytes, diagnostics and an activity log. The protocol defines completion,
assistance, exposure boundaries and validation. Root coordinates replay and
independent review after the author submits; no nested workflow or subagents.
