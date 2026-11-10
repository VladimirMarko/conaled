# Independent guarded authoring trial

This directory retains the independent author attempt for
[issue #108](https://github.com/VladimirMarko/conaled/issues/108), based on the
public repository freeze `2f89f8651843797822efbb7da038311ab3d9f04d`.

- [Report](trial/report.md): outcome, scope, validation and limitations.
- [Frozen selection and protocol](trial/selection.md): independently selected
  upstream theorem and prospective requirements, locked before construction.
- [Prospective log](trial/prospective-log.md) and [effort data](trial/effort.json):
  phases, substantive cycles, failures, interruptions and checks.
- [Attempted caller](trial/work/Attempt.lean) and
  [statement review](trial/statement-review.md): source derivation and its
  semantic applications.
- [Cycle records](trial/cycles/): pre-check source snapshots, exact commands,
  diagnostics, execution outcomes and validation interruptions.
- [Validation mapping](trial/validation-record/overlay.json): the isolated
  integration overlay and its byte-identical caller.
- [Original Phase 1 files](trial/phase1/): bytes verified against the original
  manifest before the release into proof construction.

The ignored `validation/` directory holds a separate validation checkout. Its
public import exists only in that validation candidate; this evidence directory
does not add a production import or change the frozen framework. The final
archive manifest identifies the retained evidence bytes. Independent evaluator
and Standards/Spec review results belong to the enclosing workflow after this
author archive is sealed.
