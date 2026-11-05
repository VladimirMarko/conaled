# Frozen author protocol (#323)

This is an assigned trial within an existing implementation/review workflow.
The interface freeze is e376ba585603ae8f2c174d5ceaab374242942cbd. The coordinator
approved it before selecting the held-out task. A separate concrete dispatch
approval is required; receiving the coordinator's author assignment indicates
that dispatch has occurred. This file itself grants no approval.

Read tasks/common.md and tasks/arm.md. Complete calibration before the held-out
task. Work only in this handoff and its dependency/toolchain sources. Do not
read original project history, parent checkout, other arm, coordinator/private
references, or other project paths. Links in copied guidance do not expand
this allowlist. These are procedural controls on a shared machine, not an OS
sandbox. Report actual prior familiarity before work and accidental exposure
immediately. Do not spawn agents or communicate with the other author.

Every Lean attempt, including inspection modules and failed revisions, must
use a fresh file and the evidence wrapper: direnv exec . python3 check_attempt.py
attempts/AttemptNN.lean. Never overwrite attempted source or archived evidence.
Write only under attempts/. Log other commands and consulted files in
attempts/activity.md. Record available model/configuration/usage data in
attempts/session-metadata.md; unavailable serving revision, token counts and
transcripts stay unknown. The coordinator records the actual dispatch settings
separately; do not infer them from prior #320 runs.

Ask /root for environment repair or contract clarification. Clarifications
that affect the common contract go to both arms and are logged. Proof hints,
extra lemmas, changed source support or repaired submissions are separately
attributed assistance, not unaided work. Do not silently repair the frozen
interface. An interface change requires another freeze and new held-out task.

No arbitrary wall-clock, token or attempt cap. Continue to complete submission,
a concrete obstruction with attempted remedies, or external interruption or
resource failure. A scheduling convenience is not a mathematical failure.
Retain failed and unfinished attempts and explain the stopping reason.

Finish attempts/Submission.lean through the wrapper and attempts/outcome.md
mapping every task obligation to exact declarations and checks. Separate
source mathematical obligations, model-builder coherence, host encoding,
interface plumbing, documentation gaps, assistance and author effort. In
particular report root-tail raw-rule work and any new burden elsewhere.

The wrapper preserves exact bytes, hashes, commands, stdout/stderr, exit status
and times, and checks frozen inputs/import allowlists before and after runs.
It does not establish mathematical coverage, prevent all file inspection or
detect transient changes restored between checks. A successful Lean exit is
not acceptance. The coordinator will archive/replay exact submissions, review
statements and selected data, run exhaustive axiom checks, and obtain independent
Standards/Spec review. A repaired reference proof is not an author result.
One agent per arm cannot establish causal productivity or human usability.
