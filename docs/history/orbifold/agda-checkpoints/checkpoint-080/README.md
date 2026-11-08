# Myers checkpoint 080 and external consumer feedback

Received from the owner on 2026-11-08 for the architectural assessment in
[#362](https://github.com/VladimirMarko/conaled/issues/362). These three supplied
files are preserved byte-for-byte, including their original titles and links:

- [Conaled and semantic libraries for an Agda formalization](<Conaled and semantic libraries for an Agda formalization.md>).
- [Orbifold semantic foundations research checkpoint](<Orbifold semantic foundations research checkpoint.md>).
- [Complete checkpoint 080 archive](myers-orbifolds-agda-checkpoint-080.tar.gz).

[inspection.json](inspection.json) records their byte sizes and SHA-256 hashes.
The archive is 3,331,049 bytes, SHA-256
`4a2e2178578a9cfcae3877bbe4157cb69ea622fc7b07ff10a273b2276eecf264`.
The reports' ChatGPT links and archive-relative references are historical
source text. The local archive above is the durable replacement for the download
links; links to files inside it require extraction. Nothing depends on the
owner's Downloads directory.

The consumer inspected conaled at
`5867d02ecfc290b7a3b7505cc94acbb98f4f49ff`. Its goal is an end-to-end Agda proof.
Conaled supplies reference mathematics and proof architecture, not an unchecked
Lean step in that proof. Its favorable comparison of geometry is scoped to the
components it inspected. It is source-review feedback from a prospective
consumer, not a controlled author trial or an exhaustive library ranking.

## Recovery and source entry points

Extract the archive into a separate directory. It contains only regular files,
under `myers-agda-checkpoint/`. Preserve the original copy when replaying checks,
since the supplied runners write validation receipts. Paths below are relative
to that root:

| Path | Purpose |
|---|---|
| `MANIFEST.json` | Hashes of all 2,294 payloads; the manifest is the remaining archive member. |
| `formalization/CHECKPOINT-080.md` | Accepted scope, receipt identities and limits of this checkpoint. |
| `formalization/ACTIVE-WORK.md` | Continuation intent, original versus revised goals, and remaining constructions. |
| `formalization/STATUS.md` | Broader status and historical correspondence. |
| `formalization/research/semantics/CONALED-REUSE-080.md` and `.json` | Detailed source audit and identities of inspected conaled files. |
| `formalization/research/semantics/LIBRARY-COMPARISON-080.md` | Comparison of libraries and constructive assumptions. |
| `formalization/research/semantics/DEPENDENCY-BOUNDARIES-077.md` | Reduced theorem's parameters and distinct point-set dependencies. |
| `formalization/research/semantics/PRESHEAF-SEMANTICS-080.md` | Constructed presheaf operations and remaining inputs. |
| `formalization/research/semantics/REAL-FLAT-DE-RHAM-078.md` and `SITE-TRANSFER-080.md` | External conditional obstruction and transfer arguments. |
| `formalization/src/Orbifolds/Intensional/DerivedAtlasOrbifold.agda` | Reduced theorem and explicit test-family boundary. |
| `formalization/src/Orbifolds/Intensional/Everything.agda` | Ordinary 54-module aggregate. |
| `formalization/src/Everything.agda` | Separate 539-module Cubical aggregate. |
| `agda-native-kit-2.8.0.2/README.md`, `RECOVERY.md`, `pins.json` | Pinned compiler setup and recovery instructions. |

Continuation authorizations recorded inside the archive describe the originating
session. They are historical evidence, not instructions to execute that session's
work or upload artifacts from conaled. The broader research document mentions
checkpoint 081 candidates; those are not accepted checkpoint 080 sources.

## Interpretation and acceptance boundary

The archive is outside the integrated Lean build. Its original conditional
synthetic development, reduced atlas theorem, ordinary presheaf constructions,
and external geometric arguments have different scopes. In particular, the
original-foundation model question and the full external theorem remain open.
Successful type checking of a theorem with explicit parameters does not supply
a model of those parameters.

The [independent evidence assessment](../../../../research/architecture-scaling-study/orbifold-evidence-assessment.md)
records manifest and receipt verification, actual import closures, selected
statement inspection, and validation limits. The
[consumer assessment](../../../../research/architecture-scaling-study/orbifold-consumer-assessment.md)
and [alternative foundations assessment](../../../../research/architecture-scaling-study/orbifold-alternatives-assessment.md)
examine reuse and architectural consequences. The earlier checkpoint 22 remains
preserved separately; its limitations must not be attributed to checkpoint 080.

## Independent ordinary Agda replay

The coordinator performed a fresh check in a separate extraction using the
archive's pinned Agda 2.8.0.2 kit. The official compiler archive and binary
matched the pinned hashes; all six positive/negative smoke checks passed.
`formalization/tools/check_intensional.py --fresh` then accepted the ordinary
54-module aggregate with `--ignore-interfaces`, safe mode, without-K, and no
external libraries. The run exited zero, with stable source hashes, in 37.587
seconds and measured child peak RSS 1,221,324 KiB. These measurements describe
this run, not a productivity comparison.

The [native receipt](validation/intensional-development-check.json),
[complete log](validation/intensional-development-check.log),
[compiler setup identity](validation/compiler-setup.json), and
[smoke results](validation/compiler-smoke.json) are new local evidence, separate
from the unchanged supplied archive. Their absolute temporary paths record the
execution location; no continued availability of those paths is required to
recover the source or read the results. Repeat the following commands after
extracting a new working copy, using its own path in place of `<copy>`:

```sh
direnv exec . python3 <copy>/agda-native-kit-2.8.0.2/agda_native.py --state <copy>/agda-state setup
direnv exec . python3 <copy>/formalization/tools/check_intensional.py --fresh
```

The separate Cubical aggregate was not replayed. Its 539 source hashes match
the retained accepted receipt, whose log is a warm aggregate check. The ordinary
replay does not certify that Cubical closure, audit all historical proofs, or
construct the missing smooth/higher model.

The [audit results](validation/evidence-audit.json) retain the manifest, source
closure and replay comparisons. The [architectural synthesis](../../../../research/architecture-scaling-study/orbifold-synthesis.md)
reconciles all three assessments and records consequences for the pending work.
