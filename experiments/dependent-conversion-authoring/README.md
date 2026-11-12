# Dependent-conversion trial fixtures

These are preparation artifacts for the prospective [authoring
protocol](../../docs/research/dependent-conversion-authoring-protocol.md), under
[#423](https://github.com/VladimirMarko/conaled/issues/423). They provide checked
mathematical tasks and private reference solutions. No author trial has run;
these files do not establish a productivity advantage or close the trial
obligation. The source baseline is `03cfba5e37d64c33bcec1f8484616d9e31de9397`.

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
The direct route may develop comparable reusable helpers during a future trial;
these reference helpers are withheld from authors.

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
work, elapsed author time, or token use. No author artifacts exist to measure.
The source-node convention must remain fixed across routes in a later trial.

## Validation and source boundaries

The ten Lean files are intentionally outside the public library entrypoint.
Their imports use `Examples.ConversionTrial.*`. For checking, copy each file
byte-for-byte to `Examples/ConversionTrial/<basename>.lean` in a private Lean
module root; [manifest.json](manifest.json) records the mapping and source
hashes. Compile in the manifest order with the pinned environment:

```text
direnv exec . lake env lean -R PRIVATE_ROOT -o PRIVATE_ROOT/Examples/ConversionTrial/NAME.olean PRIVATE_ROOT/Examples/ConversionTrial/NAME.lean
```

The private root must be in the Lean search path and must contain the
source-correct accepted project dependency closure. This preparation used the
checkout's private `.lake/build/lib/lean` root. It preserved package caches and
made private copies of borrowed project artifacts before checking. An initial
borrowed umbrella referenced a missing newer module; that failed attempt and
artifact identities were retained. A private closure rebuild was interrupted
because final acceptance will restage the fixtures against the accepted
integration closure. No recovery or acceptance is claimed for that private
cache, and no shared artifacts were repaired or deleted.

Run the existing native `scripts/lean-source-info.lean` over an explicit JSON
array of all ten source paths to enforce the accepted source policy and obtain
imports. Compilation checks complete syntax. Compile `Validate` last: it imports
both references and the separating model, emits actual metrics/import closure,
and invokes the unchanged `#audit_project_axioms` from `ProofAudit`. The staged
module origins fall under `Examples`, so all ten modules, including private
proofs and generated declarations, are audit roots. Staging is a file mapping,
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

## Exposure and remaining execution prerequisites

The directory is available to preparers and reviewers only. It is not a released
author bundle. `private/`, repair, held-out tasks, and negative-control solutions
must be withheld until their designated protocol phases. Public task filenames
here describe future release classes; no exposure or sealing is claimed.
Preparers and reviewers who have seen solutions cannot be trial authors.

A later step must freeze exact release bundles, a reproducible cache/command
policy, model configuration, and a matched checkpoint/continuation policy, then
randomly assign six fresh sessions before exposure. The prescribed three
sessions per route remain unchanged. Following the owner's 2026-11-12
clarification, 75 minutes and 24,000 reported tokens are initial sanity review
checkpoints, not hard failure ceilings. Missing live token telemetry does not
itself block execution. Record actual available usage, overshoot and observed
hibernation, throttling, contention or other interruptions separately; raw laptop
wall time must not rank the routes. Unknown model/configuration, author
identities, active preparer time and token telemetry remain unknown. No new
runner, release parser, author execution, or paid API spending belongs to this
milestone.
