# Native author arm

Read protocol.md and task.md before work. Your allowed project inputs are the
frozen transitive closure of `SquareKit.DependentOperation.SelectorBase` and
`Examples.DependentOperationTrialSpec`, plus the pinned Lean/Mathlib dependencies.
The public manifest lists exact files and module hashes. Do not inspect other
repository paths, Git history, other authors or coordinator work.

Start from the independent task mathematics and native helpers. You may reuse,
generalize or replace helpers, including existing indexed rule-library results
in your allowed closure. You need not write per-example preservation proofs.
Record any alternative representation and the work needed to admit it. The
shared arm's newly named boundary helpers are not in this handoff, but native
reuse is encouraged. Both arms must meet the same task outcomes.

Every Lean check, including inspection, must use a fresh attempt filename and
`direnv exec . python3 check_attempt.py attempts/AttemptNN.lean`, with the
coordinator's build-lock wrapper. Preserve incomplete attempts. Report each
checkpoint and stop reason within the fixed protocol limits. Do not launch
other agents or seek mathematical help. Report prior exposure and available
model/configuration metadata honestly; do not guess unavailable values.
