# Dependent-conversion trial fixtures

These are preparation artifacts for the prospective [authoring
protocol](../../docs/research/dependent-conversion-authoring-protocol.md), under
[#423](https://github.com/VladimirMarko/conaled/issues/423). They provide checked
mathematical tasks and private reference solutions. The original preparation
baseline was `03cfba5e37d64c33bcec1f8484616d9e31de9397`. The subsequent
[six-author trial](results-2026-11-12/README.md) completed its author submissions
and focused replays on 2026-11-12; all twelve full trial audit contexts passed.
Independent report acceptance and publication are recorded at the exact revision
on #423. Neither these fixtures nor the bounded cohort establish
a general productivity advantage.

## Mathematical tasks

`fixtures/Terms.lean` builds open terms in the existing base-domain dependent
function grammar. Its function parameter has result index equal to the bound
base argument. A separate family variable remains in the context. Each repeated
eta expansion creates a lambda application; the comparison retains the original
function variable and its dependent result index. Weakening moves the original
base variable through added binders. The substitution sends that original
variable to its negation; lifting preserves the added free variables.

| Fixture | Checked obligation |
|---|---|
| Initial | One expansion, width 2, two nonidentity substitutions after weakening; source equality and both explicit result indices. |
| Scale: composition | Expansion lengths 1, 4, 8 at width 2 and substitution count 2. |
| Scale: context | Base widths 2, 4, 8 with the same family/function variables, expansion length 1 and substitution count 2. |
| Scale: substitution | Counts 1, 2, 4 at width 2 and expansion length 1. |
| Repair | Replace assignment to zero by assignment to another free base variable; update equality and index, and prove the old index is no longer the result. |
| Negative | Distinct free function heads with the same type are inequivalent; a surviving index mismatch also prevents dependent equality. |
| HeldOut | Width 3, two expansions and three substitutions, with an explicit surviving index. |

The recipes and repeated substitutions are syntactic: no involution equation for
base negation is silently assumed. The explicit initial result index has three
negations; the held-out index has four. The context widths count base variables,
not function/family declarations. These are open terms, not closed evaluations.

`private/DirectReference.lean` proves the tasks with eta, congruence, typed
substitution and renaming laws, without importing the converter or the service
reference. `private/ServiceReference.lean` independently uses the public
conversion decision/equivalence interface, without importing the direct
reference. Their shared task data contain no task-specific equality solution.
Direct authors may develop reusable helpers; the reference helpers were withheld
from authors throughout the trial.

`private/SeparatingModel.lean` supplies the fixture-specific finite sheaf
interpretation for the invalid head equation. It assigns different sections to
the two heads and derives a contradiction from semantic soundness. It does not
import the converter. This proves source nonderivability, rather than relying on
identical evaluations or an inconclusive checker. The index control is a
formation obligation, separate from beta-eta completeness.

## Measurements

[fixture-metrics.json](fixture-metrics.json) contains evaluated measurements of
the instantiated object syntax. Each `Dep`, `Func` and `Base` constructor counts
as one node. A variable occurrence counts once: its internal scoped variable
path and the surrounding context are not added to the term-node count. Context
base width is measured separately. Redex depth counts nested lambda-headed
applications in the instantiated left term. Substitution count is the length of
the actual applied chain; repair uses one assignment. Result-index size and
negation depth are separate observations.

These are generated term measurements, not caller-written proof sizes, active
work, elapsed author time, or token use. Subsequent author artifacts and their
separate measurements are retained in the [trial report](results-2026-11-12/README.md).
The generated source-node convention remained fixed across routes.

## Validation and source boundaries

The ten Lean files are intentionally outside the public library entrypoint.
Their imports use `Examples.ConversionTrial.*`. Copy each fixture byte-for-byte
to `Examples/ConversionTrial/<basename>.lean` in an external source mirror;
[manifest.json](manifest.json) records the mapping and source hashes. The mirror
must also contain every integrated root, SquareKit, Applications and Examples
source from the candidate, unchanged `ProofAudit.lean`, and unchanged
`scripts/project_sources.py`. Run audit-bearing commands with that mirror as
the current directory. Merely placing Examples-named artifacts on LEAN_PATH
outside the inventoried source tree does not establish audit ownership.

Select the pinned repository development shell, put a separate private output
root first on LEAN_PATH, and retain the exact candidate dependency paths. Compile
the current production ProofAudit into that output root, then compile fixtures
in manifest order. With cwd set to SOURCE_ROOT, the fixture command is:

```text
lean -R SOURCE_ROOT -o OUTPUT_ROOT/Examples/ConversionTrial/NAME.olean SOURCE_ROOT/Examples/ConversionTrial/NAME.lean
```

Record the actual command, cwd, paths and copied-source hashes. Require the
inventory to equal the complete candidate mathematical module set plus the ten
fixtures, excluding only ProofAudit infrastructure. Compare it with actual
imported origins plus the current Validate module, and require every inventoried
module to appear in the audit report. Use fresh fixture and auditor outputs;
project dependency reuse needs source/configuration/toolchain identity evidence.

An early preparation attempt privately borrowed an umbrella that referenced a
missing newer module. That failure and artifact identities were retained; its
private recovery build was deliberately interrupted. No recovery or acceptance
is claimed for that private cache, and no outputs from it are used for final
validation. No shared artifacts were repaired or deleted.

Run the existing native `scripts/lean-source-info.lean` over an explicit JSON
array of all ten source paths to enforce the accepted source policy and obtain
imports. Compilation checks complete syntax. Compile `Validate` last: it imports
both references and the separating model, emits actual metrics/import closure,
and invokes the unchanged `#audit_project_axioms` from `ProofAudit`. All ten staged
module origins occur in the source inventory, so their private proofs and
generated declarations are included among the audit roots. Staging is a file mapping,
not a new source parser or an audit exemption. The expected axiom allowance is
exactly the repository's `propext`, `Classical.choice`, and `Quot.sound`.

Preparation also checks that the native source policy rejects an axiom,
admission, source `unsafe`, and malformed late import. Separate attempted
proofs of the invalid head equation and wrong index must fail compilation.
Fresh integration staging compiled all ten modules and ran the full import-closure
and axiom audit, with all ten staged modules present among the audit roots.
All four source-policy rejection controls and both mathematical rejection
controls passed. The manifest records the audit and import-closure hashes.
These checks used fresh fixture outputs against the accepted integration
closure, without reusing outputs from the interrupted private-cache rebuild.
Earlier metrics-only previews remain development evidence; the final metrics
were emitted by the fully audited Validate module. Independent Standards and
Spec acceptance remains required.

## Preparation exposure boundary and subsequent execution

The directory is available to preparers and reviewers only. It is not a released
author bundle. `private/`, repair, held-out tasks, and negative-control solutions
must be withheld until their designated protocol phases. Public task filenames
here describe release classes; this fixture directory itself does not implement
sealing. The separately frozen execution package supplied staged author bundles.
Preparers and reviewers who have seen solutions cannot be trial authors.

The subsequent [execution package](execution/README.md) froze exact release
bundles, a reproducible cache/command policy, model configuration and matched
checkpoint/continuation rules, then assigned six fresh sessions before exposure. The prescribed three
sessions per route remain unchanged. Following the owner's 2026-11-12
clarification, 75 minutes and 24,000 reported tokens are initial sanity review
checkpoints, not hard failure ceilings. Missing live token telemetry does not
itself block execution. Record actual available usage, overshoot and observed
hibernation, throttling, contention or other interruptions separately; raw laptop
wall time must not rank the routes. The dated report records actual child configuration, author identities and
available raw usage. Exact serving revision and active preparer time remain
unknown. The original fixture preparation milestone did not include author
execution; the later bounded trial is recorded separately. No paid API purchase
was authorized.
