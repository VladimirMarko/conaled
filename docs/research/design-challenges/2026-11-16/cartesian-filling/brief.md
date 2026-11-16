# Neutral design challenge: Cartesian all-box filling and selected recomputation

Decision: whether the concrete constructions in `proposal.md` meet #600's
selected-witness comparison contract, which corrections are required, and
which bounded target fragment is useful to implement or publish.

Read `proposal.md` and the actual source; its research author
has not implemented or kernel-checked any new result. Do not treat the
proposal's suggested route as the desired verdict. Do not read other lenses'
reports until all initial reports are saved. Do not modify production, create
issues, or start another design-challenge workflow. Isolated finite calculations
or scratch Lean experiments are permitted; no integrated or cold builds.

## Fixed inputs

Repository `VladimirMarko/conaled`, committed base
`4c81050dd2844c39bcfc551426f1e1cdbe3bcac1`. Inspect that revision with git show
or a separate read-only checkout; concurrent #599 edits are not evidence for
this proposal. The accepted #574 report is
`docs/research/second-cubical-witness-preservation.md` and its linked challenge.
The issue is https://github.com/VladimirMarko/conaled/issues/600, created
2026-11-16T09:55:51Z, body read 2026-11-16; its acceptance text follows.
No #600 source modifications are proposed yet. The scratch proposal may be
revised only after initial reports; hash it in your report for identification.

#600 acceptance:

- Select actual target families and Cartesian cofibrations (including required
  diagonal equalities), concrete Kan formulation, and precise size assumptions.
  Distinguish endpoint-Kan from diagonal-Kan.
- Construct chosen fillers for every box in the promised fragment, including
  boxes without source lifts. Verify boundary, naturality and source=target.
- Compare inherited source outputs with target recomputation on the exact
  selected composite/inverse records, dependent package and public square from
  #574. Prefer a specified native comparison when sufficient; prove orientation,
  endpoints, substitution and composition. Retaining a chosen square may require
  a higher relative witness; mere existence of a homotopy is insufficient.
- State residual code classification and arbitrary target ua; either construct
  the bounded additional comparison or name a concrete successor.
- Design challenge before adoption; preserve Bool separation, Fin3 order,
  dependent proof fields. Formal results require EDD, independent review,
  full build/audit; research results require reviewed hypotheses and a concrete
  construction or separating obstruction.
- No all-foundation bridge, kernel change, general smooth/cohesive model,
  runtime evaluator or production #489 interface.

The user authorized orchestration of #599 and #600. #599 independently owns
formal restriction and faithful recovery of selected source bodies. Completing
#599 does not discharge #600's independently recomputed target operations.

## Candidate constructions

1. Presented discrete target families, including actual Fin3/Phase admittedLine
   and its proof-bearing package, have unique all-target-box fillers. This
   claims full record equality for discrete endpoint equivalence fibers and
   full package equality through a specialized Pi inverse.
2. Cubical nerve N(G), G finite small sets and bijections, with vertexwise
   all-box filler and tuple decoder. This includes nonconstant code paths and
   native ua for decoded vertex local systems. It does not classify every
   Cartesian fibrant family.
3. Q from source universe cubes with finite discrete vertex codes to N(G),
   using source transport along canonical De Morgan vertex paths. The proposal
   gives a relative dimension homotopy and a triangle-square argument needed
   for exact functoriality. All vertices of the exact swapComposition qualify.
4. Claimed comparison Q(exact selected square)=native recomputed nerve square.
   This is whole target-cube equality after Q. Q is not shown to recover the
   source interior. A relative three-path in RU is not constructed. Determine
   whether this satisfies the required comparison or exposes a required missing
   construction; do not silently weaken the square contract.

## Concrete checks

Verify the full filler formula for r varying across vertices, φ a diagonal,
and substitution that duplicates variables or selects endpoints. At a generic
cube φ may be false while all its vertices satisfy φ, so vertex membership
cannot be mistaken for global membership. Explain why the proposed nerve cube
is still an actual presheaf element and why its restrictions match every tube
cube, including such cases.

For the source triangle law use a square with corners v,a,w,v and coordinate
conditional(s, canonical(v,a)(t), canonical(v,w)(t)); its left side is constant
v, right side canonical(a,w), bottom canonical(v,a), top canonical(v,w).
Check actual orientation and whether the existing source dependent transport
laws provide the needed comparison rather than asserting categorical path
composition without a construction. Endpoint fibers are discrete; interiors
of the exact source square are not assumed strictly constant.

For source square retention, distinguish the full source code-valued body,
its image as a functor V_2→G, native equality of target bodies, and any proposed
relative three-path in the restricted source universe. Identify exactly what
can be recovered or which observations could be identified by Q. No claim of
source-body injectivity may follow merely from nerve boundary determination.

## Three independent lenses

Contract and foundations: prove or refute all-box filling, Q coherence, and
whole selected-square comparison at the exact stated hypotheses. Examine
whether source-category paths or source decoder choices are hidden assumptions.

Implementation and use: inspect actual source definitions, package proof fields,
selected composite/inverse records and swapComposition. Identify a minimal
implementation that serves them and genuine missing adapters/proofs; distinguish
paper derivations from existing Lean evidence and avoid adding final theorem
fields to an interface.

Alternatives and generality: compare presented-discrete-only, nerve/local-system,
and a stronger native relative-square or classifier bridge. Test whether Q
changes the retained observation contract and whether another bounded route
preserves it with less machinery. The constant-code Boolean obstruction is a
negative control, not rejection of non-discrete classifiers.

Each report must cite evidence, separate defects from unproved obligations,
state strongest evidence for the candidate, propose the smallest useful fix
or alternative, and name a discriminating test when unresolved. Report context
exposure, proof/experiment limits, and hashes of inspected scratch inputs.
