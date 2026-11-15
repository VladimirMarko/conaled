# Dependent author comparison protocol (#320)

Round 1 uses interface freeze `dbf56af4845f954cf6ebdcf8bc3faeed268f5ce0`,
approved by the coordinating agent before the selection recorded in
`preparation/selection.json`. The source interfaces are reviewed integration
`7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96`. Calibration precedes the held-out
J-certificate task. `tasks/common.md` fixes the shared mathematical contract;
each arm's guide gives its source notation. The prospective manifest records
exact inputs and private references. Dispatch still requires root's second
approval of that concrete snapshot.

## Question and mathematical scope

Do the candidate interfaces remove repeated semantic-annotation work while
preserving independently specified dependent judgments and selected data?
Compare a retained baseline with the candidate under the same mathematical
acceptance conditions, supported model classes, and selected observations.
The contract must exercise repeated simultaneous dependent substitution and
reuse after the admitted constructor extension. Include its identity/witness
behavior and the compatibility laws needed by callers.

The model class for reuse after extension is every full contextual
`PathTransport.Typed.Model` supplied with `Sigma.Stable` on its structural
reduct. This #317 contract includes judgmental eta through a stable
comprehension isomorphism; it does not cover beta-only models. The original
Typed source has no object-language Sigma. The matched task therefore compares
reuse of the same old argument in the exact reduct. The candidate also embeds
its derivation into the admitted Sigma source theory. Constructor formation,
dependent elimination, computation and eta are assessed separately through
checked #317 capabilities, outside the author-burden comparison. Neither author
is asked to pretend a contextual package is a Sigma term.

Keep object-language identity, judgmental equality, metatheoretic equality and
presentation comparisons distinct. Exact selected data is required wherever
the client contract asks for it. A lossy observation may be valid for its
stated contract; successful erased calculations do not discharge a stronger
selected-data contract. No higher-capability claim is evaluated without separate concrete higher
interpretation evidence. The generic task quantifies over arbitrary full models
with the stated capability; checked native specializations supply lower-truncation
evidence. This trial cannot close the higher gate. It does not select or prepare #108's theorem, resume #107,
activate #260, or require a new frontend.

## Preparation and dispatch sequence

1. Record the reviewed baseline and candidate commits, entry modules, transitive
   project import closures and source hashes. Freeze the tested interfaces
   before selecting any held-out task. Support that changes those interfaces
   requires another interface freeze before selection.
2. Identify public calibration explicitly and select at least one held-out task
   after the interface freeze. Record selection time and prior exposure. Fix
   task order and equivalent mathematical acceptance for both arms. Existing
   public transport examples are calibration rather than held out.
3. Validate private reference solutions for both arms against that contract.
   Record an unsupported arm as a capability result; changing its assumptions
   or observations does not produce a matched author comparison. Reference
   authoring, failed reference approaches and support engineering are preparation.
4. Build separate public handoffs from explicit allowlists. Include exact
   public sources, pinned environment inputs, tasks, prompt, conduct and skill
   copies, this checker, and a `public-manifest.json`. Copy dependency sources
   and caches privately, then build only the allowed project closure. Exclude
   original Git objects/history, private references, repository entrypoints that
   expose them, other-arm work, and compiled private modules. Record fresh
   public Git heads and dependency/toolchain identities separately.
5. Freeze and hash the complete handoffs, private references, task order,
   acceptance conditions, assistance, exposure policy and stopping rules. Root
   reviews this concrete boundary and approves it before dispatch. Record that
   approval and the exact prompts; a draft is insufficient.
6. Dispatch one fresh `fork_turns="none"` author per arm. Each author sees only
   their arm and works through the frozen order. The coordinator is not an
   author. No crossover, author subagents or private solutions are permitted.

The coordinator records exposed model/configuration metadata and usage data
when available. Unknown serving model, reasoning configuration, token usage or
full-session export stays explicitly unavailable. Inherited settings are not
evidence of an exact serving configuration. The fixed order, shared calibration
and one author per arm limit interpretation; later tasks have earlier-task
exposure and are not independent first-exposure observations.

## Author work and assistance

There is no arbitrary wall-clock, token or attempt cap. The owner authorized
unlimited task budget. Record measured elapsed time and available usage without
turning missing telemetry into an estimate. Work ends when the author submits
the requested artifacts and checks, reports a specific obstruction after
documenting attempted remedies, or encounters an external interruption or
resource failure. Preserve unfinished attempts and the reason for stopping.
A coordinator convenience deadline is not a mathematical failure.

Authors read only their frozen handoff and its dependency/toolchain sources.
They report actual prior familiarity and any accidental exposure immediately.
Public calibration is allowed only as disclosed in the frozen task materials.
The two handoffs share a machine: these are instruction-based exposure controls,
not operating-system isolation. Dependency/build directories remain writable
for tooling. Neither the checker nor the fresh Git history proves that an
author could not inspect other machine paths.

Authors may inspect allowed declarations, use Lean diagnostics, and write
self-contained attempt modules. Every Lean attempt, including inspection and
failed revisions, goes through the wrapper under a fresh filename. Record other
commands and consulted files in the author activity log. Ask the coordinator
for environment repair or contract clarification by the agreed channel. The
coordinator records requests, answers, time and recipients, and supplies a
clarification to both arms when it affects the shared contract. Proof hints,
extra lemmas or repaired submissions are assistance and must be recorded
separately; they cannot be counted as unaided success. A changed tested interface
requires a new round and new held-out work.

## Attempt evidence

Run `python3 check_attempt.py attempts/Attempt01.lean` from the handoff's
development shell, choosing a new name each time. Each attempt is one
self-contained Lean module. The wrapper creates a fresh archive, snapshots the
exact bytes before checking, and rejects reuse of an archive name. It records
SHA256, commands, working directory, UTC timestamps, monotonic durations, exit
status and separate raw stdout/stderr for dependency inspection and Lean.
Read-only file modes discourage accidental edits; the same machine user can
change them. The coordinator must copy closed evidence out and hash it.

The manifest has `schema: 1`, a `files` map from public relative paths to SHA256,
and `allowed_imports`, a list of permitted project module names whose sources
are in that map. The coordinator records the manifest's own hash in the private
freeze. The wrapper checks listed inputs and rejects extra public files before
and after checking. Infrastructure under `.git`, `.lake`, `.direnv`,
`__pycache__`, and mutable `attempts` is outside that source scan. The manifest
itself is snapshotted and checked for changes during the invocation.

Lean's `--deps` output determines direct compiled imports. Project imports
must be listed; dependency-package imports and toolchain imports are permitted.
The coordinator checks the transitive project source closure when building the
handoff. Frozen source hashes do not authenticate compiled dependency caches.
Before/after checks detect persistent changes, not transient edits restored
between checks. The wrapper does not collect a complete agent transcript or
prevent arbitrary Lean metaprogramming from reading files. Exposure compliance
and cache provenance remain part of the recorded experimental procedure.

Lean exit zero means only that this archived module elaborated. Empty files,
missing requested declarations and admitted proofs require separate rejection
during acceptance. The wrapper never reports mathematical acceptance.

## Acceptance and reporting

For each task and arm, preserve all attempts and record pass, partial, fail or
unavailable with exact artifact references. Replay each proposed accepted
submission byte-for-byte under the frozen environment. Check coverage against
the required declarations, review their full quantified statements and selected
projections, and run the applicable exhaustive axiom/source audit. Record the
accepted source hash and these validation results independently of author claims.
Do not edit an author's file to obtain a passing replay. A coordinator repair
has a separate source, hash, validation record and attribution.

Assess source judgments, selected data, compatibility and ordinary caller
obligations. A caller record that merely requests all old annotation alignments
does not establish that the candidate removes that work. Separate mathematical
requirements, model-builder coherence, interface/presentation burden, host
encoding, and missing documentation. Distinguish preparation, reference proofs,
support engineering, extension/model construction, author work, assistance and
coordinator repairs. Malformed Lean or an interrupted run does not establish
that the mathematical route is impossible.

Choose repair, adopt, revise or defer using those observations and preserve failed
candidates. Adoption is restricted to the tested contract and demonstrated
obligation changes. This small agent sample cannot establish causal productivity
gains, human usability or general model capability. Interface repairs need a
new frozen round and fresh held-out work. Required independent Standards and
Spec review covers the whole trial and its evidence after replay and validation.
