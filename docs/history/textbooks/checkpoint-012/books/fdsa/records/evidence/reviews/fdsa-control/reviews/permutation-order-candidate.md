# Permutation-order draft: candidate and source statement assessment

Recorded 2026-11-02. **Uncompiled source draft; no acceptance claimed.**

## Immutable identity

- Ticket: FDSA-XU02, in the existing book implementation workflow.
- Starting/review base: `ff3dd88082c6283df40bcd86a4363841a0360b12`.
- Candidate: `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`.
- Branch: `work/fdsa-permutation-order`.
- Checkout: `conaled-permutation-order`; clean after commit.
- Requirements: `permutation-order-requirements.md`, SHA-256
  `f473f593bf4a7ef75dcf2f3163440db6fe187b3b9983f87254d2ddfa8191982d`.
- Commit: `feat(probability): formalize restricted permutation orders (#174)`.
- Change: six files, 793 insertions. The minimum-law source is unchanged.

The start and coordinated API are in `permutation-order-start.md`. The base
is an unvalidated minimum-law draft, itself based on the unvalidated
Chapter 1 repair. No accepted dependency is assumed. Project outputs remain
separate; only the pinned dependency packages are shared. No compiler or
mutation of the active old Chapter 1 checkout occurred.

## Exact source files

| File | SHA-256 |
|---|---|
| `Applications/Probability/PermutationOrder.lean` | `b427902814c19d269c850c97cb43728034d03df2539c5e357ce7ce715191298f` |
| `Examples/PermutationOrder.lean` | `251c0ee0ce7b96711ea57e1ff7496a784fe33137596e8f13b244fa9e44fd57e5` |
| `Examples/PermutationOrderBoundary.lean` | `35c9768d94fd12e553905244a69ffa375e01e469098856b311ac17ad88533fea` |
| `SquareApplications.lean` | `bfa905b56c3cfb7ed63b0c80b7680a0e93486cf32987739ef4d61ca94262dc21` |
| `docs/research/fdsa-permutation-order.md` | `39fd16835dccd39c9d34ebfcebbdbdd33f44ec1dad49fdfe582a8ac4801faea3` |
| `docs/research/fdsa-reconstruction-map.md` | `aa5ae498a2b23a5dee8dcbc0eac1eb5d8735cec4d97ebcdca7877d48ff9f52ce` |

The core is 319 lines/15,172 bytes; the main example 146 lines/6,445 bytes;
the boundary example 144 lines/5,434 bytes. The main example imports the
boundary module, which reuses the earlier public integer-priority example.
The root imports the main example, so all new Lean files join its closure.

## Source statement review

Root read the three new Lean files in full and the prose. The core author
also checked its pinned APIs, argument orders and proof route; the boundary
author reviewed its cases. No elaborated type was inspected. The following
records source meaning and intended connections, not formal validation.

### Actual observation and value assumptions

`restrictedOrder positions S π` is the inverse map followed by the ordinary
stable membership filter. π maps a key to its label, so `π.symm` maps the
ordered labels to keys. The definition needs only DecidableEq I.
`orders positions S` is the finite set of permutations of the filtered
base list, not a new ranking datatype or separate random draw.

The general membership law retains both `π a ∈ positions` and `a ∈ S`.
Completeness removes only the first condition and establishes exact finset
support. Nodup of positions establishes distinctness; both premises yield
the length and permutation contracts. Their separate necessity is retained
in the invalid-enumeration examples.

The mapped-sublist law has no completeness/Nodup premise. Mapping the
filtered keys back by π gives a sublist of the original labels, fixing the
pointwise order correspondence. The second-filter/intersection law also
has no distribution hypothesis; T⊆S gives the nested specialization. These
are observations of one unchanged π, with no conditioning or resampling.

### Whole-fiber probability and existing mapped meaning

The source-event theorem quantifies over every fixed S and every output xs.
Supported lists have reciprocal ENNReal factorial S.card mass, and all
other lists have mass zero. Completeness yields a local Fintype from the
actual positions list. No public finite enumeration, nonempty index type,
index order, index measurable space or output measurable space is imposed.
Its explicit sample measurable-singleton hypotheses make the finite fibers
measurable.

The proof extends the positionwise correspondence of two supported Nodup
lists to σ using the existing finite-injection extension theorem. Equal
support proves that σ preserves S. Right composition by σ.symm gives the
whole-list equivariance equation. Injectivity of `List.map σ` identifies the
fiber preimage; count/cardinality invariance under the sample bijection
gives equal masses. The actual fibers cover the sample space, and their
finite sum normalizes to one. Existing list permutation cardinality gives
factorial S.card. None of these premises assumes the desired probability.

The Measure.map corollary adds only the existing measurable structure and
measurable singletons on List I. A finite I makes List I countable, not
finite in general. Singleton extensionality, finite-source measurability,
the fiber law and the finite target measure give equality of the supplied
measures. No bespoke probability carrier or action framework is introduced.

Source inspection confirmed the argument order of `List.Sublist.map`, the
length/index binders of `List.ext_getElem`, and the definitional inverse
composition used in the equivariance helper. The bound transport is proof
irrelevant, but its actual elaboration remains pending.

### Connected observations

The Fin 4 main example proves completeness and Nodup for `[0,1,2,3]` and
uses the public value/support/order laws on subset `{0,2,3}`. Its target
cardinality six is obtained through `orders_card`.

The probability of `[0,2,3]` uses the generic supported-fiber branch.
The probability of `[0,3,2]` uses `Measure.map_apply`, the actual public
mapped-law equality, the target's singleton formula and cardinality. Both
have independently expected mass 1/6, despite sharing their first key.
The repeated list `[0,0,2]` receives zero through the off-support branch.

The nested observation filters the actual output to `{0,3}` under the same
π. It uses the public subset-composition law, then the generic probability
law to obtain mass 1/2 for `[3,0]`. Singleton and full-universe examples
obtain one and 1/24 through the same public fiber theorem.

The boundary file instantiates the new probability theorem for empty S and
for Empty indices. Its target is `{[]}` and the mass is one; no nonempty-I
premise or reciprocal zero is inserted. The concrete cycle distinguishes
the inverse output `[0,1]` from the wrong direct output `[1,0]` on `{0,1}`.
The numeric-order example reuses `spacedPriority`, proves strict increasing
order for enumeration `[0,2,1]`, and failure for ordinary label enumeration.

Incomplete positions `[0]` retain Nodup but produce an unsupported empty
output under the swap. Repeated positions `[0,0,1]` retain completeness but
produce unsupported `[1,1,0]`. These are pointwise counterexamples to the
support claim with either missing premise, not unproved global probability
counterexamples.

## Bounded contributor assessment and preserved correction

Report: `../research/permutation-order-draft-preflight.md`, SHA-256
`302611bfb28cb30b5cc580185aa7475233d89587187cd53a92696e40f4bb19e8`.
It assesses root's main example, source note and only the new map subsection.
It excludes the assessor's own boundary file and the core implementation.
It provides no independent final-axis or elaboration evidence.

**XU02-SP01** identified the phrase “non-increasing numeric order” in the
initial doc: `[-7,100,4]` is not descending. Root corrected it to “a different
numeric order that is not strictly increasing”. The assessor reread the
correction and recorded the updated hash above. The report retains the
initial hash and disposition. No code changed for this clarification, and
there is no remaining source-level correction request from that pass.

## Validation boundary and next work

The six intended paths were the only nonignored changes before staging.
`git diff --cached --check` passed. An ordinary marker search in the three
new Lean files found no admission, new-axiom, unsafe/partial or native-evaluation
bypass token. Neither check is the project's guarded build or exhaustive
proof audit.

No focused compilation, candidate check, axiom audit, independent final
Standards/Spec approval or candidate verification has run. Remaining ordinary
elaboration risks include dependent Fin transport, composition/filter
simplification, finite fiber sums, singleton preimages, countability, local
instances and ENNReal/factorial arithmetic. No compiler failure or success
is asserted by this source review.

Conditional histories, adaptive subsets, disjoint joint laws, expected
positions, algorithm and treap semantics, and actual source costs remain
queued. The draft closes no chapter obligation. Collect the unchanged old
Chapter 1 gate first, finish repaired-chapter validation and retained reviews,
then reconcile shared drafts with the accepted base and capture the matching
candidate. Full guarded validation, both independent axes and immediate final
verification remain necessary before acceptance and its uploaded checkpoint.


## Recovered validation continuation — 4 November 2026

Original frozen candidate4bb13e44 and requirements remain preserved. The minimal
validation source now continues through fbc9a32 to
bdac9703aab4b383fa775568d36bf685af329389. The source core and boundary examples
have individual compiler passes; the complete triple and all53 explicit types
remain pending. This addendum grants no independent or candidate acceptance.

Existing XU02-ELAB-001–008 remain in the four provenance correction records.
Actual attempt4 at e4965499954e2afe6bb6be0b8a4a61167a0ff2ce closed with exit1;
its21245-byte complete log has SHA256
10d22668f7040a1802fbac453a6c8880fe1482b663751055f780cdcf934e2df0.
Both closed recorder/native records are secured. The original partial diagnostic
snapshot is retained with its actual status, separately from that terminal result.

XU02-ELAB-009–014 concern the main example: equivalent explicit Sublist notation,
two current ite rewrite names, five positive memberships proved through the
existing mem_orders/List.Perm interface, one actual multiplicity contradiction,
explicit singleton-preimage reflexivity, and a finite-cardinality numeral cast.
Read chapter02-xu02-elaboration-correction4-20261104 for the full observed errors,
source diff, immutable successor and root source assessment. All18 public main
claims and the private helper preserve their mathematical contract; every exact
probability, same-environment nested observation and boundary remains. The
successor is uncompiled. Full scope reviews, complete validation/audit and
immediate verification remain mandatory in the established shared-unit order.
