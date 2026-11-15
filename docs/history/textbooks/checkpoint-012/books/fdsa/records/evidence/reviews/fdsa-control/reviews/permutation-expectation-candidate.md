# FDSA-XU04: immutable preceding-count expectation draft

Recorded 2026-11-02. **Uncompiled and unaccepted.** Chapter 1 remains the
active chapter and no chapter is accepted. This is a source handoff within
the existing book implementation loop, not either final review axis.

## Identity and scope

- Base: `a0597381f02eddd074ee96cabaa974f2062285f8`.
- Candidate: `11923e9ffd17246b6f22c5594002a1ba0434e43c`.
- Worktree: `conaled-permutation-expectation`.
- Branch: `work/fdsa-permutation-expectation`.
- Commit: `feat(probability): formalize preceding-count expectations (#174)`.
- Six tracked files, 1,001 inserted lines; clean index and working tree after
  the commit. Only the unchanged dependency packages are shared. No compiler
  or project-output writer was started in this checkout.
- Frozen requirements: `permutation-expectation-requirements.md`, SHA-256
  `926fddbeb2d20b45842416b90ba96c78dbeaa84064d5d135cf3bb5b2d620624a`.
- Starting state and coordinated API: `permutation-expectation-start.md`.
  Checkpoint 0021 preserves these requirements, source/API preflights,
  independent expectations and clean pre-code branch. Its receipt is in
  `../checkpoints.json`.

The predecessor chain contains the unvalidated Chapter 1 repair and the
minimum, whole-order and conditional-tail drafts. No inherited acceptance
or gate pass is claimed. Any corrections to those dependencies must be
reconciled explicitly before this unit can be accepted.

| Candidate file | Bytes | SHA-256 |
|---|---:|---|
| Applications/Probability/PermutationExpectation.lean | 12,849 | `a322a016ea767d0a1f294cac5f709c20bc7e41d0e1e4f05d2aa2eb9ebc1c1cf9` |
| Examples/PermutationExpectation.lean | 8,255 | `5f89da2fb3dc77e886532708962eccdf7fc93cbdbaaaf0ef5fe486f231f7a037` |
| Examples/PermutationExpectationBoundary.lean | 14,682 | `e5547ba32b5f786c221a5f2259282452c17e05b86eacc9808d5d490a5f62b333` |
| SquareApplications.lean | 8,431 | `2a537090f1bb7c625897e5206c20ac4753afc6d722733950a667645082c9a71e` |
| docs/research/fdsa-permutation-expectation.md | 9,278 | `9a835956f4f914f9a76e50975458b01d90597e09ceebf606ed9349bbb18ecabe` |
| docs/research/fdsa-reconstruction-map.md | 20,131 | `bf1f4f5dd009da181a1cfbcf94dc52ebbbdde3a564b24cf000b6c477f049d0d1` |

## Claims and actual-observation connections

The sole new observation `beforeCount` is ordinary Set.ncard of the actual
strict-before set. Its LT-only definition and empty-subset law retain the
standard infinite-set natural-cardinality convention. Under finite indices
and a preorder, the complement bound uses only the impossibility of strict
self-comparison. It has no injectivity or probability premise.

The probability laws retain a fixed subset, the original uniform global
permutation and an injective priority into a linear order. The target need
not be finite or measurable, and the public index type needs no enumeration,
decidable equality, key order or inhabitance. A private pointwise lemma
connects the actual count to the finite outsider-indicator sum. Another
identifies each outsider's strict-before event with the earlier minimum
event on the inserted subset; its converse uses injectivity to eliminate
ties. The minimum probability, finite linearity and complement cardinality
give the ENNReal formula, including empty S and empty I.

The real law explicitly establishes Integrable.of_finite, consumes it in
ofReal_integral_eq_lintegral_ofReal, proves the displayed ENNReal ratio is
finite, and transports to the real formula. It does not interpret a
totalized nonintegrable integral as an expectation. Natural subtraction
occurs before scalar casting and the successor denominator is nonzero.

The rank bridge uses the composed equivalence π.trans rank and an actual
nonempty finite-image minimum. It identifies the counted set with the
preimage of an initial segment and uses Fin.card_Iio. Rank supplies local
finiteness; the public bridge does not ask for extra finite or measurable
instances. The one-based mean uses this value equality, finite integrability
and normalization, then proves the cardinal bound needed for the natural
subtraction cast and real algebra. The nonempty-domain premise is retained.

The main cases connect Fin3/S={0,1} to ENNReal and real count means 1/3,
actual first-position mean 4/3 and deterministic count bound 1. A nonidentity
rank swapping 0 and 2 uses the generic rank bridge to give actual count and
minimum rank 1, position 2. Fin4/S={0,3} uses the public laws for means 2/3
and 5/3. These are fixed-subset mean specializations, not new distribution
theorems.

The Int-valued priority 100+10*j has count mean 1/3 through the general
infinite-target theorem. Its raw numeric observation is the actual minimum
of the selected image. Finset.min'_image and the rank bridge establish the
pointwise affine relation before finite integral laws give its mean 310/3,
different from the ordinal 4/3. The raw minimum was not defined as the
desired affine expression.

Boundary cases retain empty Fin3 subset count/mean 3 and sentinel 4, Empty
index normalization and mean 0, fixed singleton count/position means 1 and
2, and full-subset count/position 0 and 1. Tied Fin2 priorities with proper
subset {0} have actual mean 0 instead of the unjustified formula's 1/2;
the deterministic bound still applies. The sample-dependent singleton
{π.symm 0} has cardinality 1 but actual count and mean 0, connected through
the pointwise rank bridge and compared with fixed-singleton mean 1.

The conditional boundary uses the same Fin3 sample, actual full inverse
order and first-key-0 event. XU03 gives original head mass 1/3 and both
tail masses 1/2. XU02 support and a finite support table reduce that actual
order on the event to [0,1,2] or [0,2,1]. Mapping back through π recovers
key 1's assigned rank; the new rank theorem identifies its actual count.
An on-event indicator equality passes to conditional a.e. equality, and
explicit finite integrability plus conditional normalization give mean
3/2. Its original mean is 1. The same actual singleton-order observation
has the same HasLaw under both measures through XU02 and XU03 map laws.
No independent sample or generic conditional-mean framework appears.

## Statement assessment and validation evidence

The core and boundary authors stopped at the exact hashes above after
bounded source/API assessments. Root read both completed modules, its main
examples, the frozen requirements and source-use documentation. No
mathematical or scope mismatch was identified in these author assessments.
Root removed a redundant trailing reflexivity tactic after a cast-normalizing
tactic before the immutable capture; this was a source-shape correction,
not a compiled result or a change to any expected value.

The pinned-shell `git diff --cached --check` passed before commit. A bounded
marker search of the three new Lean files found no admissions, source-axiom
declarations, unsafe/partial definitions, native_decide or skipKernelTC
markers. This does not replace the complete source guard or axiom audit.

The separate read-only assessment is complete at
`../research/permutation-expectation-draft-preflight.md`, 14,935 bytes,
SHA-256 `a9e73a2714f0e89ccb48354c3beda5e82404e883d0cdb9af3eadce2924b09ad4`.
It inspected all three Lean modules, the full new document and the new map
section/import at the exact unchanged hashes above. No XU04-SP finding was
opened. Root read the complete report. Its bounded statement/proof-route/API
assessment supplies neither final Standards/Spec approval nor compilation
or acceptance credit.

No compiler, focused build, project hash helper, whole-candidate check,
exhaustive audit or matching candidate success record exists for this unit.
Elaboration risks include the generated additive indicator lemma, cardinal
coercions, rank/minimum definitional reduction, finite support decision,
instance search, casts and integral normalization. Source inspection does
not establish kernel validation of these proof terms.

## Limits and resumption

No chapter is accepted by this shared work. C10-117 remains open, including
the canonical root/minimum correspondence, conditional depth, Jensen,
algorithm work, adaptive histories and correlated weighted charging. A
relative-order HasLaw alone does not supply global placement; E[d] does not
factor E[dZ]. Quicksort and selection algorithm/cost correspondences remain
separate obligations.

Keep the old Chapter 1 gate unchanged and collect its outcome first. Resume
validation of the repaired Chapter 1 candidate in the idle isolated cache,
reconcile any new correction candidate, and obtain the retained independent
final reviews plus immediate candidate verification before acceptance.
Then reconcile the shared dependencies and compile this unit's actual core
and connected examples in the pinned environment. Preserve any correction
as a new immutable candidate. The full guarded check, exhaustive audit,
independent Standards and Spec axes, and immediate matching verification
remain mandatory; no acceptance checklist is closed by this handoff.
