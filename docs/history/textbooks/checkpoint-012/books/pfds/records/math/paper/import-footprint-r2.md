# Import footprint correction round 2 — local 10018

Status: all three direct-provider corrections passed the focused client pair.
The source diff is exactly three added import commands; all non-import bytes
match the correction base. Full-candidate and independent-review gates remain
open. The original first focused round remains recorded as failed.
This continues the existing prerequisite implementation/review loop, under
session/requirements/import-footprint.md version 1. It does not broaden the
import-only requirements, establish project acceptance, or change the chapter
frontier. Root owns commits, tracker/review state and the final full gates.

## Isolated scope and evidence

The clean starting point for this correction is commit
226ebaef53b9eba97bef4b3b6ca364fdea488c69 in import-correction, branch
pfds/import-footprint-r2. Its project build outputs are private; its pinned
external packages are shared through the prepared package symlink. The
separate validation-imports checkout and its running full check are untouched.

The frozen full check recorded two transitive-import failures in
active-validation/import-footprint-226ebae-resumed-r1.log:

- IMPORT-VAL-001, Applications/FRP/Demand.lean:139: the existing witness uses le_rfl, but its
  remaining goal is n<n+1 instead of n≤n.
- IMPORT-VAL-002, Applications/FRP/Finite.lean:72: field notation s.biUnion cannot find the
  finite-set union provider. The inferred finiteness evidence reduces to the
  Finite subtype class in the diagnostic; the actual missing declaration is
  Set.Finite.biUnion.

Both declarations and proof bodies are byte-for-byte identical to the parent
of226ebae. This correction changes their imports only; it does not assume that
an arithmetic proof edit or a finiteness coercion is needed.

## Demand: restore the actual simplifier and instance provider

The existing pending_registered proof performs simp_all [next] before giving
the registration witness. The pinned Mathlib.Algebra.Order.SuccPred contains
the simp theorem Order.lt_add_one_iff, rewriting x<y+1 to x≤y for an appropriate
successor/addition order. Mathlib.Order.SuccPred.Nat publicly imports that
module and supplies Nat.instSuccAddOrder. Together they explain why the
all-library import previously provided a proof context in which le_rfl was
appropriate after simplification.

Add Mathlib.Order.SuccPred.Nat directly to Applications.FRP.Demand. This is the
specific mathematical provider for the existing proof's simplification, not a
replacement proof, new simp attribute, or return to an aggregate import.
The theorem still says that a pending request requires registration at a
strictly earlier transition. Its statement and every proof token remain
unchanged.

## Finite: restore the finite union provider

The pinned Mathlib.Data.Set.Finite.Lattice defines Set.Finite.biUnion and its
dependent variant. It is the exact provider used by finiteHistory to combine
finitely many finite occurrence-index sets. Mathlib.Data.Set.Finite.Basic and
Range alone do not provide that union theorem.

Add Mathlib.Data.Set.Finite.Lattice directly to Applications.FRP.Finite. No
type annotation, coercion, field-notation rewrite or proof change is made.
The existing theorem still constructs finite occurrence histories from the
event's finite past support and finite lists at each timestamp.

## Validation plan and limits

Compare each edited file to226ebae after removing only import-command lines;
the remaining byte sequences must be identical. Record the full local import
closure and configuration hashes, freeze those inputs, and serialize the
pinned offline Nix focused command on active-validation/focused-build.lock.
Use the existing Examples.FRPDemand and Examples.FRP clients. They already
connect registration provenance, ordered/empty demand answers, the finite
history equivalence, finite list roundtrips and ordered duplicate-preserving
merge to the public results. No redundant new cases are needed for changes
that preserve every formal claim and proof body.

Focused success would establish that these imports suffice for the two known
failures and these existing clients. It would not establish the final full
project check, exhaustive axiom audit, final candidate verification, review
outcomes or a resource-performance improvement. The original running candidate
retains its own terminal status and must not be relabeled as passing because a
separate correction succeeds.

## First focused result and discovered client dependency

active-validation/import-footprint-r2-focused-r1.{log,json} ended with exit1,
not success, and all recorded inputs unchanged. It ran from
2026-11-02T21:00:11.849998Z to21:03:09.945584Z. Both
Applications.FRP.Demand and Applications.FRP.Finite compiled successfully with
their unchanged proof bodies. Examples.FRPDemand also passed.

IMPORT-VAL-003: Examples.FRP then reported an unknown exists_nat_gt in
ticks_finiteHistory. This additional failure became visible only after the two
previously blocked dependencies compiled.001 and002 are repaired in focused
evidence, still pending full-candidate and independent-review validation;
003 is the current correction.
Its proof bounds a real timestamp above by a natural number. The pinned
Mathlib.Algebra.Order.Archimedean.Defs supplies exists_nat_gt, and
Mathlib.Algebra.Order.Archimedean.Real.Basic supplies Real.instArchimedean while
importing that general API. Basic.Real.Basic explicitly documents that those
Archimedean facts are deferred to this module.

Add Mathlib.Algebra.Order.Archimedean.Real.Basic directly to Examples.FRP.
This is another missing direct dependency exposed after removing the aggregate
import, allowed by the existing version1 scope. No claim, proof token or case
expectation changes. Record the same exact non-import-byte comparison for this
third file, then repeat the two existing focused targets to verify the concrete
remaining failure. The first round remains recorded as failed even though its
two repaired modules and demand client passed individually.

## Passing correction and handoff

The corrected pair Examples.FRPDemand and Examples.FRP passed in
active-validation/import-footprint-r2-focused-r2.{log,json}, exit0,1134jobs.
The check ran2026-11-02T21:03:52.502004Z through21:04:43.533718Z; all recorded
local import-closure and configuration hashes remained unchanged. Session74577
was collected at its terminal result and the focused lock released. The prior
failed session39364 was also collected. No compiler is active from this worker.

Current correction map:

| Finding | Consumer | Added direct provider | Focused result |
| --- | --- | --- | --- |
| IMPORT-VAL-001 | Applications.FRP.Demand | Mathlib.Order.SuccPred.Nat | Module and Examples.FRPDemand passed |
| IMPORT-VAL-002 | Applications.FRP.Finite | Mathlib.Data.Set.Finite.Lattice | Module and downstream Examples.FRP passed |
| IMPORT-VAL-003 | Examples.FRP | Mathlib.Algebra.Order.Archimedean.Real.Basic | Existing example module passed |

The exact comparison record is
session/research/import-footprint-r2-source-comparison.json. It records the
unchanged non-import hashes and original/corrected full hashes for all three
files. Current corrected full SHA-256 hashes are:

- Applications/FRP/Demand.lean:
  4e92f97ac56aa684c27f3421cdf1890b64159b631fdd828c420af00d3d9c6ad6
- Applications/FRP/Finite.lean:
  f617d2f3db4fd162f43e53abd8271ebcf15bd242d79dd201a61b314afa90954c
- Examples/FRP.lean:
  a5bf0f5263b45514b4f9b88b09ef1abe2a6a1fb773a44493afd5a8198abeb22b

git diff --check passed, and the correction diff is exactly three insertions
in three files. No source statement, proof body, example, audit root, toolchain,
dependency pin, configuration, guard or proof policy changed. The original
validation-imports checkout was not edited. No broad aggregate import was
restored. No commit or tracker mutation was made by this worker.

Therefore no proof-edit prerequisite or requirements expansion is needed for
these findings: actual import repairs suffice. All three findings remain
pending full exact-candidate validation and both independent review axes.
The isolated correction sources are frozen for root's commit/integration.
No optional checks were added after this sufficient focused result.
