# Permutation-minimum draft: bounded implementation-side source assessment

Prepared 2026-11-02 for FDSA-XU01. **No concrete mathematical or scope mismatch
found in the assigned root-written portions.** This is a source assessment
within the existing implementation loop, not an independent Standards or Spec
review, final approval, compilation result, proof audit or acceptance decision.
No elaborated types were inspected.

## Scope and inspected identities

The following stable root-written files were read from
`conaled-permutation-minimum`:

| File | Inspected scope | SHA-256 |
|---|---|---|
| `Examples/PermutationMinimum.lean` | Entire file, 4,891 bytes | `b1cef98f9814eb53668cc29896bad750d2b687c4bc162c7ad500e1df82a09442` |
| `docs/research/fdsa-permutation-minimum.md` | Entire file, 7,608 bytes | `9b0ac9218e6a82f40e61faf97447af33adcccfafb60498a4f33acbfce91f5a31` |
| `docs/research/fdsa-reconstruction-map.md` | Only the new section headed “Shared fixed-subset minimum probability (draft)” through EOF | Whole-file identity: `98cb1df9badd9ce31b6dc252e7741cd9362e7ef1785b4989b4c2011e5facdfd7` |

The reviewed reconstruction-map addition is 883 bytes, SHA-256
`49d3298c5d65e570bc3626e02b8070fb718442a459150876e13cad50a4965412`.
The whole-file hash identifies its containing snapshot; it does not extend
this assessment to earlier sections.

The governing frozen requirements were
`reviews/permutation-minimum-requirements.md`, SHA-256
`59e2ff6ff66dd39b6151a42b501bcc22e86eb593a9b854b532f97bc45fdd7686`.
The retained independent arithmetic was
`research/finite-ranking-calculations.json`, SHA-256
`36f853f68d0f0713581aea33e7c91187a003f99bb7386ff5ba509e52964c1949`.
Both hashes matched the supplied identities. The starting-state record and
repository guidance had already been read for this same implementation loop.

**Exclusions:** I authored `Examples/PermutationMinimumBoundary.lean`, so it
was not reread or treated as independent evidence in this pass. Its import
in the main file and the root documentation's descriptions were inspected;
those descriptions were compared with the frozen mathematics and arithmetic,
not used to approve the authored implementation. The concurrently completed
core proof was not read. Neither its implementation nor the whole import
closure is assessed here.

## Public API connections

Architecture directly confirmed the agreed, not elaborated, interfaces:

- `minimumEvent priority S a` includes membership and every non-strict
  priority comparison, using `priority (π a)` with a single permutation π.
- `uniformOn_minimumEvent priority hinj S a ha` returns the ENNReal reciprocal
  of `S.card`, with finite I, linearly ordered P, injective priority and the
  sample-space measurable/singleton hypotheses.
- `minimumEvent_inter priority S T a haS haT` identifies the intersection
  with the event on `S ∪ T`. Both membership premises are explicit; the
  union operation additionally has its ordinary `DecidableEq I` instance.

The main file's argument orders and hypotheses match those contracts.
Its concrete Fin3 type supplies decidable equality and finiteness. The only
measurable instances declared there are local to the permutation sample
space. `law` is the ordinary `uniformOn Set.univ`, with its probability
instance obtained from existing infrastructure, not a new experiment.

## Connected mathematics

| Frozen case | Actual source connection | Assessment |
|---|---|---|
| Overlap marginals | `first_minimum_mass` and `second_minimum_mass` each invoke `uniformOn_minimumEvent` for candidate 1 in their fixed two-member subset. | Each mass is one-half under the same `law`. |
| Joint event | `overlap_event` invokes `minimumEvent_inter` with both membership proofs, then proves the union is `Finset.univ`. `overlap_mass` uses `full_minimum_mass 1`, which invokes the generic probability theorem. | The event intersection is inside one measure application, so both observations share the same sampled permutation. Joint mass is one-third. |
| Failure of independence | `marginal_product` computes one-quarter from the two proved marginals; `overlap_mass_ne_product` compares it with the actual joint mass. | No multiplication rule is used to infer the joint probability. |
| Full universe and singleton | `full_minimum_mass` and `singleton_minimum_mass` instantiate the generic theorem for every `a : Fin 3`. | The expected masses one-third and one follow through the public result. |
| Infinite, gappy priority target | `spaced_minimum_mass` supplies the proved injectivity of `spacedPriority` to the same generic theorem, for candidate 2 in `secondSubset`. | Its mass is one-half, without a finite-target or monotonicity premise. |

The saved overlap calculation gives the same half/half/third/quarter values.
Directly, six global rankings have three samples in either marginal and two
in the intersection. The exhaustive JSON reports 50,363 permutation/subset
pairs for universe sizes zero through six. That stored arithmetic was read,
not rerun or promoted to Lean validation. Its additional preceding-count
fields remain outside the frozen unit.

### Integer-priority statement review

`spacedPriority` assigns indices 0, 1 and 2 the Int values -7, 100 and 4.
These are pairwise distinct; in sorted numeric order their gaps are 11 and 96.
The target type Int is infinite. The injectivity proof splits the nine finite
index pairs, and the failure of monotonicity uses the concrete comparison
`1 ≤ 2` together with `100 > 4`. Those are the intended mathematical claims,
not assumptions of injectivity or a claim that the assigned values are ranks.

As a small independent mathematical check, among key-to-label permutation
tuples `(π 0, π 1, π 2)`, the tuples `(0,1,2)`, `(1,2,0)` and `(2,1,0)`
make candidate 2 first in `{1,2}` with these priorities; the other three do
not. Thus the expected mass is three-sixths. The Lean claim obtains this
through the general theorem rather than encoding those favorable cases.
No expected raw numeric priority or monotonicity inference is made.

## Documentation and source limits

The research note accurately describes the membership conjunct, fixed
subsets, finite global permutation law, distinctness, and explicit sample
measurability. Its right-composition explanation exchanges key indices,
consistent with the agreed proof route. Its statement that no global index
inhabitance is required concerns the generic interface; the member premise
still supplies nonemptiness when a probability claim is instantiated.

The boundary descriptions agree with the frozen counterexamples: empty
events, a normalized permutation law on empty indices, outsider mass zero
versus raw comparison mass one-half, and tied-member mass one. This is a
check of the root-written prose, not independent review of my boundary code.

The main header, research note and reconstruction-map addition consistently
leave conditional/adaptive history laws, full relative-order restriction,
the expected preceding count and first-position bridge, treap construction
and charging, and actual sorting/treap work outside this unit's claims.
Occurrence pivots and duplicate inputs retain their own obligations. The
inverse-orientation description is a source-position convention; no theorem
identifies inverse π with sorting arbitrary nonmonotone numeric priorities.
All artifacts explicitly retain uncompiled and unaccepted status and make
no chapter-completion or algorithm-complexity claim.

## Remaining checks and disposition

There is no concrete correction request from this bounded source pass.
The later frozen-candidate checks must still elaborate the core interfaces
and example calls, local instance synthesis, finite case proofs and ENNReal
arithmetic; inspect actual elaborated public types; and validate the complete
import closure, including the excluded boundary module. This report provides
none of those results and closes no independent-review finding.

Only this requested report was written. No reviewed source, boundary file,
core, requirement, tracker, Git state, compiler output, cache or gate was
changed. The file digests above were ordinary read-only SHA-256 calculations,
not execution of a project hash helper or verification command.
