# Local #1039 — complete narrowed summation imports

Source: the authorized full VFA/conaled integration work, the bounded source
investigation after the c988 fresh failure, and independent retained Standards
findings ST-004/ST-005 on4adc2f006677b9ac22bbdb4a60a36526632588b2.
This remains inside the existing full Preface/Perm implementation/review loop.
Fixed base:7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd; no content exclusions.

Applications.Probability.FiniteMH currently lacks the defining import for
Finset.sum_le_sum and Finset.sum_pos: Mathlib.Algebra.Order.BigOperators.Group.Finset.
Applications.Linear.StructuredCosts currently lacks the imports defining
List.sum_replicate and global nsmul_eq_mul: Mathlib.Algebra.BigOperators.Group.List.Defs
and Mathlib.Algebra.Ring.Defs. Exact pinned source and metadata, plus independent
consumer import-closure traversals, support these source-level findings. At spec
creation they have not yet been confirmed by a focused compiler invocation.

Both files are already in the retained task diff because prior task changes
narrowed Mathlib.Tactic imports. Attribute these gaps to that narrowing, unlike
the baseline-identical natural-size example repaired by1038.

Required work:

- Preserve the actual interrupted4adc attempt: APIterminal1, no kitresult, last
  raw logged completion61, no verification/audit credit and unknown child
  quiescence. Never signal guessed or historical PIDs or infer quiescence from
  the terminal or stable files. Keep that checkout and all surviving outputs
  untouched while establishing safe isolated continuation.
- Obtain actual focused compiler evidence for the suspected gaps, then add the
  three explicit defining imports while preserving existing source bodies,
  mathematical statements, hypotheses, witnesses and proof text. Record any
  further actual failure honestly and correct it through the same review loop.
- Use the actual entire FiniteMH source (only external imports), and the small
  actual local closure for StructuredCosts: Squares, Resources.Measured,
  Optimization.Basic, Optimization.Transport, then StructuredCosts. Diagnostic
  checks do not replace any integrated gate.
- Keep compiler/dependency pins and supplied kit unchanged. All three required
  artifact families already exist. Rederive candidate-specific roots/closure;
  no cache/setup/dependency write is needed for the proposed corrections.
- Both retained independent reviewers assess the complete corrected candidate,
  reusing unchanged analysis. Full fresh/audit, non-repairing collector,
  guarded build/postguard/audit, managed audit prerequisite, four regressions,
  both final reviews and immediate candidate verification remain mandatory.
- Preserve current work in compact immediately uploaded checkpoints. No GitHub
  writes and no Sort implementation before Preface/Perm acceptance and upload.
