# Actual measured selector after coordinate acquisition

This implementation continues C03-083 in the existing whole-Chapter-3 loop.
The fixed source base is 47f12b48b93a1e223b9f743e067685f12f4da5b1. The only
authorized dependency donor is checked be8a5ab11040d61f5f2f8aef7abf02da333049fc.
The minimal project closure has 30 files: 19 already identical and 11 previously
absent exact copies, with no conflicts or overwritten source. Root remains the
sole compiler owner. This author supplies source and assessment, not a pass.

## Intended construction

The new application module is Applications.Selection.CoordinateSelection.
Its observedSelect is the existing readAll instantiated with the actual fixed
Resources.Selection.selectRun k, returning Measured (Option α) Nat. It receives
only the prior transcript, fixed rank and worker. The source list passed to the
selector is obtained from query answers. List.ofFn input is only a proved
specification of those acquired answers. The operation has no original-input
argument, input-dependent advice, or uncharged full-list access.

The Int-only selectedValue projects the actual final observation with getD 0
while preserving query decisions. A proof connects it to the same readAll
execution. The actual selectRunWith_exists and selectRun_some_iff laws prove a
some result at k : Fin n before the default is used. Correctness is on every
integer input, including duplicates; Nodup is used only for competitor lower
bounds. n=0 and invalid natural ranks remain total optional executions.

The declared work is queryWork(const c) trace + observation.2. Thus acquisition
cost c*n and the actual deterministic selector's source calls are both paid.
The checked all-rank cost<=F theorem is consumed directly. Uniform affine and
positive-size linear constants are chosen before the payload type, input,
rank, trace and observation. The asymptotic family theorem assumes actual runs
and input sizes, never an assumed growth bound.

For total correct competitors and a distinct valid-rank Int input, use existing
coordinate replay/coverage to prove c*n <= their charged query work. With
c>=1, the measured book algorithm's complete declared cost is at most one
uniform constant times that query work. An existential corollary supplies both
actual runs and equal answers, so comparison is not merely a vacuous conditional.

This model retains the existing zero tariff for frontend bookkeeping, plan
lookup, projections and proof terms. It makes no physical-runtime claim or
claim about arbitrary call models with free bulk input or randomized competitors.
The deterministic selector is not treated as free: its actual measured .2 is
an explicit addend in every combined resource theorem.

## Independently expected cases, before author source

1. Empty input: actual no-query run returns (none,2), for every natural rank;
   combined work is 2 for every acquisition tariff. There is no Fin 0 valid
   rank. This exposes why a multiplicative linear bound needs positive size.
2. Singleton [a], rank0: insertion sort costs 3, lookup costs1, cached length
   costs2 and the selector entry costs1; actual worker result is (some a,7).
   Exactly one coordinate is read, so the combined work is c+7.
3. [8,3,5], rank1: insertion sort costs9 (tail [3,5] costs5, insertion of8
   costs3, entry1); lookup costs2; selector entry1 and length4 give source
   count16. Result5, three ordered reads, tariff2 gives total22.
4. [4,4,4], rank1: sorted insertion cost7, lookup2, entry/length5 give source
   count14. Result4; all three coordinates are still read; tariff2 gives20.
5. [8,3,5], invalid rank3: public guard returns (none,5) after entry+length.
   The frontend still acquires three coordinates, so tariff2 gives total11.
6. Positive input sizes20 and21: demonstrate the actual book cutoff. At size21
   with increasing Int coordinates and rank10, result10; F21 = 483+483+
   19*21+54 = 1419, hence unit acquisition gives total <=1440. This uses the
   actual nested execution and its checked recurrence theorem, not a surrogate.
7. Arbitrary full execution: existence, exact acquired list, actual worker
   observation and combined count through the public frontend results.
8. Every valid rank: selectedValue is total and Selects on all Int inputs,
   providing a concrete inhabitant of the competitor class. The uniform
   competitor comparison explicitly preserves Nodup, rank and positive-tariff
   domains and supplies actual witnesses from totality.

The earlier repeated-plan examples remain unchanged and preserve occurrence
charging. The actual book frontend reads each coordinate once. No malformed
history is used to establish selection correctness. Any closed arithmetic
proof uses kernel reduction/decide +kernel, never native_decide or an axiom.

## Review and integration boundary

The six prior query files, 95 public inspection names, three private helpers,
and all earlier provenance are preserved. Copied dependencies retain donor
identities and provenance. New source statements will receive exhaustive
source-level quantifier/nonvacuity assessment and explicit-@ inputs under the
existing printer profile; actual printed statements remain a root gate.
No aggregate, pin, toolchain, guard, canonical control or other author's file
is changed here. All 83 obligations and full/type/audit/independent-review/
immediate-verification gates remain mandatory. C03-083 gains no acceptance
credit merely from this author handoff.
