# Issue 314 candidate handoff

Candidate: `3484ce523bf23524f715a3a2029c290a2d43c4c0` on `research/dependent-structure-314`.
Checkout: `/tmp/conaled-314-320/314`.
Exact incorporated integration base: `9b0a0fe143c6f97f399632d4bb34a179db012181`.
Review the candidate against this base and the complete `specs/314.json`.
No push; #107 remains paused and #108 untouched. Shared tracker and root reports belong to the coordinator.

## Delivered evidence

The report `docs/research/dependent-structure-audit.md` inventories every field of `StructuralModel` and contextual `Model`, every constructor of the eight mutually defined source judgments, semantic-code dependencies and relevant client groups. It classifies data, supplied laws, derived laws, signature assignments, independent properties and unresolved comparisons. Its decision matrix treats local repair, factoring and replacement as distinct routes.

`Comprehension` derives pairing naturality, uniqueness, pullback mediation and both triangles/uniqueness, equality-induced family comparisons and their composition/inverse laws, lift identity/composition and the section-over-map equivalence. `DisplayCategory` supplies Mathlib context/display categories, full faithful comprehension, display pullbacks and cartesian lifting with arbitrary ambient arrows. `RepresentedFamilies` independently specifies natural representability without projection/variable/pairing fields, then reconstructs those operations and laws. `Representability` constructs it from the old records and recovers exact selected data. `TypeFamilyRepresentation` provides a direct varying Type-family instance without primitive signature assignments.

`FamilySquares` proves equivalence with actual dependent functions, with identity/composition preservation. `GroupoidComprehensionBoundary` constructs an actual Grothendieck shear over the base that fails chosen-horizontal-lift preservation. `UniformOperations` proves the variable-syntax/natural-operation equivalence and rejects closed universal selection and equivariant choice on inhabited carriers. It is a small alternative author-representation comparison, not dependent initiality.

`EmptySubstitution` constructs a generated empty substitution recursively for every context derivation. `DependentStructureBoundary` retains the old Bool countermodel by reuse and adds a full contextual-J Unit-context/Bool-endomorphism model. It separates nonexistence in inaccessible ambient components from nonuniqueness at a reachable object.

## Statement review and checked uses

- All pullback and pairing results quantify over arbitrary ambient substitutions and sections; no desired pullback or fullness property is assumed. The groupoid specialization applies public `displayPullback` and `lift_comp` to the existing binary-action model.
- Lift comparisons transport the actual comprehension domains using substitution equalities. Their coherence is proved by equality induction and category laws; no general pseudo-model comparison is inferred.
- Independent representability starts from a natural hom-set equivalence. Projection/variable are its value on identity and pairing its inverse. Beta, eta and pairing naturality are consequences. The bridge recovers projection and the selected term, not merely truth or isomorphism classes.
- The Type-family example uses `Fin(n+1)`; increment then double sends base 3 to 8 and retains index 2. The proof calls `equivalence_comp`, and the inverse equivalence recovers the dependent fiber function. Reversed composition would give 7.
- The shear is a functor of the actual total groupoid for a constant C2 family over C2. Its over-base equation is checked; the chosen nonzero horizontal arrow acquires a nonzero fiber arrow. Thus all squares cannot be identified with strictly cleavage-preserving transformations.
- Both nonterminal models satisfy the unmodified full contextual-J record. Unit motives are the complete admitted families in those instances, so the J hypotheses are satisfiable. Generated empty existence is constructive recursion on the actual `CtxDeriv`.
- Uniformity ranges over all small carriers and functions. Evaluation on `Fin n` recovers the variable, and the Bool-negation automorphism refutes invariant selection on inhabited carriers. No dependent-parametricity theorem is assumed.

The report retains the failed literal untransported lift identity and false strict-cleavage comparison as mathematical boundaries. Focused development logs also retain ordinary namespace/noncomputability and Grothendieck equality-normalization errors; those were source elaboration issues, not integrity incidents.

## Explicit limitations and successors

The all-commuting-squares comprehension category is constructed. A general equivalence with pseudonatural transformations of groupoid families is **not** proved; #318 must discharge that comparison if its selected construction uses that category. The checked shear refutes the stricter chosen-cleavage identification.

Generated empty-substitution **existence** is proved. Ambient and full reachable-subcategory terminal uniqueness are refuted by the loop model. Uniqueness restricted to source-generated arrows, and terminality of a source quotient, remain unproved; the ambient true loop is not claimed to be source generated. #315 must prove the projection invariant or give a generated counterexample if it advertises that stronger judgment category.

No equivalence of full contextual-J model categories, dependent syntax initiality, higher dependent interpretation, LF exponentials or weak-model strictification is claimed. #315 owns judgment representation/comparison construction, #317 constructor admission, #316/#321 higher semantics, #318 optional construction hypotheses, #319 internal-setting stress case and #320 frozen author evaluation. These limitations do not erase the reconstructed structural properties.

## Validation

- PASS `direnv exec . lake build Examples.DependentComprehension`, log `reviews/314-focused-accepted.log`; all new modules are in its import closure.
- PASS `git diff --cached --check` before commit.
- PASS `direnv exec . flock /tmp/conaled-314-320/build.lock ./check.sh --candidate HEAD`, log `reviews/314-candidate.log`: all 1014 integrated modules checked, exhaustive audit passed, permitted axiom union `[propext, Classical.choice, Quot.sound]`. Total 43.56s. The preguard rebuilt 41 modules with missing traces from the private seed cache; coordinator confirmed these were expected cold artifacts. Postguard hashed 3039 artifacts with 0 inconsistent modules.
- PASS immediate `direnv exec . ./check.sh --verify-candidate HEAD`, log `reviews/314-verify.log`. Candidate receipt `.lake/verification.json` matches the exact commit above, Lean 4.35.0 and pinned dependencies, incremental mode.
- Clean checkout after acceptance. Independent Standards/Spec review is pending with the coordinator; this handoff does not claim approval.

Primary citations rechecked against Awodey 1406.3219 (representability and Proposition 20), Bezem–Coquand–Dybjer–Escardó 2012.08370 (uniform families and Theorem 1), Kaposi–Kovács–Kraus 1907.07562 (injectivity and §8.2 limitation), Clairambault–Dybjer 1112.3456 (pseudo maps/extensional biequivalence) and Lumsdaine–Warren 1411.1736 (LF, Theorem 3.4.1 and type-equality limitation). The frozen external memo and historical assessments are unchanged.
