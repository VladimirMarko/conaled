# Design challenge: dynamic array policies and storage observations

The user explicitly authorized all five design challenges. Assess alternatives; do not adopt or implement architecture. Preserve useful built mathematics, book coverage with factual corrections, and usefulness to conaled. Historical checkpoints are evidence, not authority. Existing approaches are real alternatives. Competing foundations need not supply an incumbent adapter for admission.

Pinned source: e80c51d968925be3809ba3acc3259de7041b504b, read-only checkout /tmp/conaled-wave-20261111/design-challenges/source. #437/#448 and #470/#471 are published. Concurrent #472 is excluded uncommitted work, not evidence here. Inspect primary sources and exact hypotheses before external factual claims; cite local declarations precisely.

Three independent perspectives: contract/foundations (derivability and guarantees); implementation/use (actual builders, consumers, repeated obligations and migration); alternatives/generality (competing designs, capability and assumptions). Each must inspect code and consumers, distinguish defects from risks/questions, state strongest retention evidence, smallest useful alternative/correction, a discriminating test, and evidence/exposure limits. No objection quota. Investigate derivability before adding proof fields; distinguish laws defining new operations from stronger laws on unchanged operations.

Fresh agents receive only this brief and their lens. Do not read other reports or coordinate before all initial reports are saved. No target edits, issue creation, external messages, or nested agents. Read-only investigation by default. Scratch experiments use private files outside source. Heavy commands require taskset -c 0, flock /tmp/conaled-wave-20261111/build.lock, direnv and private outputs. Never change thermal settings. Ask the coordinator before significant experiment setup. Distinguish source inspection, paper argument and executed checks.

The coordinator preserves initial reports, reconciles all three, investigates disagreements and retains supported minority findings. Recommendations do not authorize adoption. Durable documentation publication receives independent Standards/Spec review.

## Decision

Which common storage/event interface supports literal and eager resize policies while preserving arbitrary copy windows and all additive prices?

Intended capability: Actual resizable-array execution with layout/refinement and amortized cost contracts.

## Current evidence and candidate approaches

Fixed-capacity buffers, vector updates, measured stores and reweighting provide pieces; dynamic resize policies remain separate obligations.

These are candidates, not requirements:

- Two local policy executors with shared copy lemmas
- Shared storage/event executor with policy-specific transitions
- More general storage hierarchy only if independently required

## Observations and clients to preserve

- Arbitrary surrounding prefix and suffix
- Ordered allocation/copy/write events
- Per-insertion grouping and arbitrary additive prices
- Raw-state vs layout assumptions and both boundary potentials
- Zero capacity and neither-policy-uniformly-cheaper examples

## Discriminating investigation

Use identical short insertion traces for both policies, arbitrary copy windows and malformed raw states; test which equalities and pricing laws survive without narrowing the executor domain.

## Evidence pointers

- `docs/research/adwh-recovered-research.md`
- `docs/research/adwh-recovered-handoff.md`

Related issues: #459, #149.

## Outputs

Write only your assigned contract.md, implementation.md or alternatives.md in this brief directory. Coordinator owns synthesis.md. Record prior involvement and absence of model diversity; fresh context does not guarantee independent assumptions.
