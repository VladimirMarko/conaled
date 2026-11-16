# Foundations follow-up: all sieves are finite formula cofibrations

I confirm the generality lens's correction. My initial assessment accepted the candidate's claim that Ω imposes a stronger filling requirement. That claim is false for the stated finite Cartesian cube category and #600's convention of compatible local formula subobjects. Preserve the initial assessment as the review record, but replace its domain conclusion with the result below.

## Factorization proof

The inspected syntax is `CartesianDimensions.lean:9–49`: an arrow f:m→n is an n-tuple of constants 0,1 and m input variables, with substitution as composition. Let v₁,…,vₖ be its distinct occurring variables, in first-occurrence order. Here k≤n, regardless of how large m is. Define p:m→k by selecting these variables, and i:k→n by replacing each occurrence of vⱼ in f by variable j, retaining the constants. Then f=i∘p.

Define s:k→m by placing variable j in the coordinate vⱼ and 0 in every unused coordinate. Then p∘s=idₖ and i=f∘s. Thus, for every sieve S on n, f∈S iff i∈S: one direction uses closure under p and the other closure under s. This works for arrows from every domain dimension, not only dimensions bounded by n.

For each normalized pattern i, form Eᵢ as follows. For every constant output coordinate a, require xₐ=that constant. For every pair a,b filled by the same pattern variable, require xₐ=x_b. This is a finite conjunction. An arbitrary h:l→n satisfies Eᵢ precisely when it factors through i. Indeed, choose one representative output position for each variable block and use h's term at that position to define q:l→k. The equations give h=i∘q. Conversely, every such composite satisfies the equations. This is equality of terms at every stage l, so Eᵢ defines the entire principal sieve, not merely its vertices.

There are finitely many normalized patterns: each has n entries from the finite alphabet {0,1,var 1,…,var n}, with the additional canonical first-occurrence restriction. Given S, take the finite disjunction of Eᵢ for exactly the patterns i belonging to S. Classical logic selects this finite subset. The sieve equivalence above proves that the disjunction denotes S at every stage. No bound on the domain dimensions of arrows in S was assumed.

## Edge cases

- If k=0, p:m→0 still has a section s:0→m consisting of zeros. The pattern i:0→n is a vertex, and Eᵢ fixes every output coordinate. Its principal sieve consists exactly of that constant tuple at every domain dimension.
- If n=0, there is one normalized pattern id₀. Every map m→0 is split epic, so the only sieves on 0 are empty and total. Empty and singleton disjunctions give false and true respectively.
- A conjunction forcing one coordinate to both 0 and 1 denotes the empty sieve, because the two endpoint constructors are distinct at every stage. More generally, an equality component touching both endpoint labels is inconsistent. Such a conjunction is discarded; consistent components give the patterns described above.
- A conjunction can constrain variables to endpoints, so a factor q may send a pattern variable to either endpoint. This is allowed and is necessary for principal-sieve closure under endpoint substitutions.

## General contexts and exact domain consequence

For a subpresheaf φ⊆Γ and a represented element x:y(n)→Γ, its pullback x*φ is a sieve on n and therefore has the finite formula just constructed. These local subobjects are compatible under substitution because they are pullbacks of φ. Conversely, compatible local subobjects determine a subpresheaf. This is exactly #600's “General contexts carry compatible local such subobjects” convention (`cartesian-filling-recomputation.md:47–57`). It does not assert one globally finite list of generators for an arbitrary Γ, a different convention that #600 does not impose.

Consequently the extensional cofibration class used in #600 equals Ω here, classically. Every family equipped with the specified uniform diagonal composition for those extensional formula cofibrations is already an input to the proposed Ω classifier. There is no additional filling hypothesis and no need to construct extra fillers for new subobjects. Finite-formula syntax indexed composition would need invariance under equal denotations before making this identification; that is an encoding condition, not a mathematical restriction of the extensional domain.

The restriction to chosen uniform diagonal composition remains. No statement follows for arbitrary presheaves lacking such composition, nor for other cube categories containing extra interval operations. The classifier still enlarges the admitted *family* domain beyond vertex local systems, as its arbitrary-family input and Z/2 consumer establish.

## Validation and exposure

This follow-up was requested after all initial reports were saved. I read `challenge-generality.md`, then independently reconstructed the factorization, principal-sieve equality, edge cases, and passage to contexts against the inspected local syntax and accepted #600 convention. I found no counterexample. This is a paper proof; no Lean check or build was run. The root's check of ABCFHL Proposition 1 concerns interval-quantifier closure and is independent of this finite-sieve argument. The initial report remains unchanged.
