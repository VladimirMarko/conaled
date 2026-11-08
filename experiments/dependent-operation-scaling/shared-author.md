# Shared author arm

Read protocol.md and task.md before work. Your allowed project inputs are the
frozen transitive closure of `SquareKit.DependentOperation.Lowering` and
`Examples.DependentOperationTrialSpec`, plus the pinned Lean/Mathlib dependencies.
The public manifest lists exact files and module hashes. Do not inspect other
repository paths, Git history, other authors or coordinator work.

You may instantiate the local operation, compilation, substitution, execution
and quotation helpers, reuse native helpers, or justify a different
representation. The helpers do not supply the new primitive or backend laws.
Both arms must meet the same task outcomes. Record local obligations and any
remaining global bookkeeping rather than counting only source lines.

Every Lean check, including inspection, must use a fresh attempt filename and
`direnv exec . python3 check_attempt.py attempts/AttemptNN.lean`, with the
coordinator's build-lock wrapper. Preserve incomplete attempts. Report each
checkpoint and stop reason within the fixed protocol limits. Do not launch
other agents or seek mathematical help. Report prior exposure and available
model/configuration metadata honestly; do not guess unavailable values.
