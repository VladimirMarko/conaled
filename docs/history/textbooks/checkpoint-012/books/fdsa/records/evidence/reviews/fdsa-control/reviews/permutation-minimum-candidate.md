# Permutation-minimum draft: immutable candidate and source statement review

Recorded 2026-11-02. **Uncompiled source draft; no acceptance claimed.**

## Identity and scope

- Ticket: FDSA-XU01, within the existing book implementation workflow.
- Starting/review base: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Candidate: `ff3dd88082c6283df40bcd86a4363841a0360b12`.
- Branch: `work/fdsa-permutation-minimum`.
- Development checkout: `conaled-permutation-minimum`; clean after commit.
- Frozen requirements: `permutation-minimum-requirements.md`, SHA-256
  `59e2ff6ff66dd39b6151a42b501bcc22e86eb593a9b854b532f97bc45fdd7686`.
- Commit: `feat(probability): prove uniform subset minima (#174)`.
- Change: six files, 590 insertions. Only the assigned new core/examples,
  source-use documentation, reconstruction-map addition and public import
  changed. No dependency, toolchain, checker or existing probability API changed.

The starting state and file ownership are in `permutation-minimum-start.md`.
The parent is the unvalidated Chapter 1 repair, not an accepted dependency.
All later integrations must preserve both that chapter's gates and this
unit's gates. The old Chapter 1 validation checkout was not changed.

## Source identities

| File | SHA-256 |
|---|---|
| `Applications/Probability/PermutationMinimum.lean` | `648a2d799ea9905a27992ad4e8653ad21a0457c5301e8c0a026d08d9cd067bbb` |
| `Examples/PermutationMinimum.lean` | `b1cef98f9814eb53668cc29896bad750d2b687c4bc162c7ad500e1df82a09442` |
| `Examples/PermutationMinimumBoundary.lean` | `d169fc8ccac457d71978bd1a209ab610338dd601fe816e40f9f0666164cca34d` |
| `SquareApplications.lean` | `577dc9b46b727b6c951a3fbff19ff545b94cdbe47d85507ca5348bbb0a489bd0` |
| `docs/research/fdsa-permutation-minimum.md` | `9b0ac9218e6a82f40e61faf97447af33adcccfafb60498a4f33acbfce91f5a31` |
| `docs/research/fdsa-reconstruction-map.md` | `98cb1df9badd9ce31b6dc252e7741cd9362e7ef1785b4989b4c2011e5facdfd7` |

The core is 197 lines/8,244 bytes; the main example is 126 lines/4,891 bytes;
the boundary example is 113 lines/4,173 bytes. The main example imports the
boundary example, and the public root imports the main example.

## Intended statements and actual source review

Root read every new Lean file in full and the documentation. The core author
performed a bounded pinned-API and mathematical source pass. The separate
boundary author reviewed that file's statements; root reviewed them as well.
No elaborated types were inspected because no compiler was run. These are
implementation-side source assessments, not the independent final axes.

### Event and elementary laws

The ordinary set `minimumEvent priority S a` contains π precisely when
`a ∈ S` and every b in S satisfies `priority (π a) ≤ priority (π b)`.
It uses only `LE P`. The candidate membership conjunct is not silently
dropped when interpreting the event. π sends key indices to labels, and
every observed subset uses the same π.

`minimumEvent_empty` and `minimumEvent_of_not_mem` give empty events without
probability, finiteness or injectivity assumptions. `minimumEvent_singleton`
uses only `Preorder P`. `minimumEvent_inter` needs the ordinary decidable
equality for finset union, plus membership in both subsets; it gives equality
of the intersection and union-minimum events under only `LE P`. These two
membership premises are necessary for that exact event equality in general.

### Uniform probability theorem

`uniformOn_minimumEvent priority hinj S a ha` has finite I, linearly ordered P,
injective priority, and explicit measurable-space/measurable-singleton
instances on `Equiv.Perm I`. Its conclusion is the ENNReal reciprocal of
S.card under the actual supplied uniform law on all permutations.
The member proof already entails nonemptiness. No public Fintype, index
order/measurable structure, inhabited index type, finite/measurable target,
or monotonicity of priority appears.

The private event-preimage proof uses `π * Equiv.swap a b`, whose action is
right composition. The transposition preserves S and exchanging two indices
exchanges their minimum events. The finite-bijection measure helper uses
`uniformOn_univ`, measurable finite counts and bijective preimage cardinality.
It does not introduce a new law or assume the desired equal event masses.

Finite minimum existence gives the event cover; antisymmetry, injectivity of
priority and injectivity of π give disjointness. Summing the equal event
masses over this disjoint cover gives total one. The ENNReal normalization
lemma then yields the reciprocal. The proof does not require factorial
counting, a public selector or independent draws for different subsets.
The hypotheses are satisfiable in every nonempty concrete subset example.

### Connected examples and boundaries

The root-written Fin 3 example invokes the generic theorem for both
two-member marginals, the full universe and singleton subsets. Its
`overlap_event` uses the public intersection law and proves that the union
is the full universe. `overlap_mass` then uses the generic full-universe
mass. Both marginal observations are under the same `law`; their product
is compared with the joint mass, never used to infer it. The independent
targets are 1/2, 1/2, 1/3 and 1/4 respectively.

The Int specialization assigns -7,100,4. It proves injectivity by finite
cases, proves failure of monotonicity from indices 1 and 2, and supplies
injectivity to the same public probability theorem. No numeric-priority
mean or finite-target assumption is introduced.

The boundary file uses the identity permutation to witness the nonempty
sample space for Empty indices; it does not assume an inhabitant of Empty.
Empty subsets have empty events and mass zero, with no reciprocal formula
at cardinality zero. The Fin 2 outsider's membership-aware event has mass
zero. Its raw comparison is proved equal to the full-set minimum event and
receives mass one-half through the generic theorem, contradicting the
singleton reciprocal one if membership were dropped.

Constant tied priorities are proved noninjective. Every full-set member
then has a universal non-strict minimum event and mass one, not one-half.
The generic theorem is not applied to this invalid injectivity instance.
All concrete permutation measurable spaces are declared locally, not as
new globally selected permutation instances.

## Bounded contributor assessment

The separate source contributor assessed only root's main example,
research note and reconstruction-map addition after their contents became
stable. Report: `../research/permutation-minimum-draft-preflight.md`, SHA-256
`2dc6359cde242541e2b8e32a910f22c232c05a747c070a72cc74e20878427dd2`.
It found no concrete mathematical or scope mismatch. It explicitly excluded
its author's boundary code and the core proof, checked no elaborated types
or import closure, and supplies no independent final-review credit.

## Validation evidence and limits

- The six intended paths were the only nonignored changes before staging.
- `git diff --cached --check` passed before commit.
- An ordinary marker search in the three new Lean files found no admission,
  new-axiom, unsafe/partial or native-evaluation bypass token. This is not
  the project's source-policy check or exhaustive proof audit.
- Source comparisons with pinned Mathlib APIs were performed. No Lean
  elaboration, focused build, full candidate check, proof audit or final
  candidate verification has run for this unit.
- No independent Standards or Spec final approval has been requested or
  recorded. The immutable candidate must be validated before those gates.

The ordinary remaining elaboration risks include the private uniform/count
rewrite, finite-permutation and local measurable instance synthesis, finite
sum normalization, concrete finset simplification and ENNReal arithmetic.
These are pending checks, not reported compiler failures or proof successes.

## Scope retained and next steps

Expected preceding counts and one-based positions, full relative-order
pushforwards, adaptive/conditional sampling, source list orientation,
quicksort recursion, treap construction/root/ancestor/charging arguments and
actual algorithm cost bridges remain queued. The documentation makes these
boundaries explicit. This unit closes no chapter or complexity claim.

First collect the unchanged old Chapter 1 gate result and validate/accept
the repaired chapter through its retained review loop. Then reconcile this
draft with the accepted base, capture the appropriate immutable candidate,
run focused checks and the full applicable guarded candidate build/audit,
complete both independent final axes and immediately verify the final
candidate identity before acceptance. Save and upload that acceptance
checkpoint. The current draft checkpoint is only recovery evidence.
