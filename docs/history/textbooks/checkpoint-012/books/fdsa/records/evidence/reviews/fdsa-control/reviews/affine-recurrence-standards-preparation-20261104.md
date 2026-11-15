# XR01 independent Standards source preparation — 2026-11-04

## Current disposition

**Blocked — source preparation only.** The complete original five-path XR01 change and the complete frozen requirements have been independently assessed at `d64b4c89fb9f21d1a6a2a603c1dc04f47233d9e2`, relative to `c28ba71863d2a35ee1c3a089caa90464e4cca692`. I found **no new mathematical or architectural Standards defect in XR01**. The original draft inherits the already-recorded documentation finding **XP01-DOC-001**, which must retain its reviewed Chapter 1 qualifier on eventual incorporation. That carry-forward does not reopen or modify the later resolved XP01 review.

This is not a compiler pass, actual-type pass, full-candidate pass, proof audit, final two-axis approval, or acceptance. No XR compiler or statement-inspection command has run in this review. The exact Foundation continuation remains higher priority when its actual terminal evidence is supplied. Existing Foundation, Chapter 2 and XP01 reports remain byte-identical; their accepted/pending states and statement counts are unchanged. This shared preparation does not activate Chapter 3 or alter the established integration route.

## Fixed scope and evidence

The exact candidate has the stated base as its sole parent. Its complete delta is the following five paths; no later narrow diff substitutes for this scope.

| Path | Status | Lines | SHA-256 |
| --- | --- | ---: | --- |
| `Applications/Resources/AffineRecurrence.lean` | Added | 113 | `0f867ba6fa96cbeaaaeeba6c4a24cc71b38fdbf798b684d484234eabb283d17d` |
| `Examples/AffineRecurrence.lean` | Added | 142 | `eb9239f5810887ba988420c3fe8538eab21285c1e6173eb5467133baa63868d5` |
| `SquareApplications.lean` | Modified | 256 | `c7abc390617e80c42c2b604528748fcebe794f869d8abeae88a07a69864ea3ef` |
| `docs/research/fdsa-affine-recurrence.md` | Added | 233 | `a07b086bc846c0898b2713a7b055b9cb451d0471c655eeaab9cc1077f32b87bf` |
| `docs/research/fdsa-reconstruction-map.md` | Modified | 500 | `4e8acd033864e106e6881d8d5bb3d73993f9c6c65bee14d072553eadf392789b` |

All 1,244 source/documentation lines (61,960 bytes) were read completely. The root was read in full. The reconstruction map was read in three contiguous bounded ranges, 1–160, 161–330 and 331–500. The new core, clients and dedicated note were each read in full. The diff on existing files is exactly one public-root import and the 23-line shared-affine section in the map; the three added files are reviewed as complete additions. The public root already imports `Examples.AffineRecurrence` at the fixed draft. The note's remaining public-root integration work therefore concerns incorporation into the eventual accepted candidate and its validation, rather than a missing import in this original source.

The full frozen requirements, `reviews/affine-recurrence-requirements.md`, are 96 lines / 5,540 bytes, SHA-256 `5873700a349c359d15873829f1399a20225fa80eaa980e7ad9f1e4c8f774dd02`. The complete 80-line handoff and 464-line preflight were also read. Their identities, exact read boundaries and hashes are preserved in `provenance/affine-recurrence-standards-preparation-20261104/read-ledger.json`. Author, root and Spec narratives are evidence aids; none replaces this source assessment or an actual expanded-type reading.

The candidate's AGENTS, code-review and example-driven instructions were fully read. Previously completed applicable architecture, domain, implementation/review-loop, language-direction, glossary, ADR and worked-example readings were retained only after exact byte-identity comparisons with the already-reviewed XP01 candidate `12cb14fc98b8617b3b625620da8e60936daba340`. Their boundaries and fingerprints are recorded in the ledger. The user's local-ticket/no-GitHub instruction and explicit Nix waiver remain in force; exact pins, proof restrictions and all actual acceptance gates are unchanged.

## Statement and proof assessment

### Quantifiers, assumptions and finite prefix

The sole public core theorem, `Resources.AffineRecurrence.exists_affine_bound_of_two_branch`, quantifies over an already total `f : Nat → R`, two ordinary natural child functions, a natural recurrence cutoff, and scalar parameters `rho K C D`. The scalar assumptions are exactly a commutative ring, linear order, strict ordered-ring structure and Archimedean property. The conclusion chooses `A` and `B` once, before **every** natural input, with `0 ≤ A`, `0 ≤ B` and `f n ≤ A * n + B`.

The hypotheses are the eventual child-sum upper bound and eventual one-sided recurrence upper bound, together with `rho < 1`. The statement adds no monotonicity of `f` or of the child functions, no nonnegativity of `f`, `C`, `D`, `rho` or `K`, and no final affine estimate as a premise. No field, inverse, floor, topology, norm, completeness or real-specific carrier is required. Some parameter choices can make the size premise unsatisfiable, but the concrete clients exhibit meaningful satisfiable cases; the theorem does not claim arbitrary parameter choices are realizable.

Let `delta = 1 - rho > 0`. The first Archimedean witness gives a natural `M` with `2*K ≤ M*delta`. The proof sets `N = max n0 (max 1 M)`, obtaining `2*K ≤ delta*N`. It then uses the existing nonempty finite supremum of `f` over the inclusive prefix `0..N` and takes its maximum with zero as `B`. This includes zero, every original base case and every case added by enlarging the proof cutoff. The finite prefix cannot be silently discarded or moved into an input-dependent existential.

A second Archimedean witness chooses a natural-cast slope `A ≥ 0` such that `2*(max 0 C + max 0 D + B) ≤ A*delta`. Thus both witnesses are constructed using finite order operations and natural multiples. There is no division by `delta`, so the integer client tests the claimed generality without a field. A local finite maximum is not a new global order structure or framework.

### Strict child descent and absorption

For `n > N`, the proof obtains `n ≥ 1`, positive natural cast, and `2*K ≤ delta*n`. The child-sum premise then yields

`2*((left n : R) + (right n : R)) ≤ (1+rho)*(n:R) < 2*(n:R)`.

Both child casts are nonnegative because the child maps are natural-valued. Each is therefore strictly smaller than `n` after reflecting the cast inequality back to naturals, before either strong-induction hypothesis is invoked. The proof does not assume child descent and does not infer termination of a separately defined algorithm from a later proof cutoff.

The two induction hypotheses and the recurrence give `f n ≤ A*(left+right) + 2*B + C*n + D`. Since `n ≥ 1`, the source proves `C*n + D + B ≤ (max 0 C + max 0 D + B)*n`; its explicit signs justify multiplying each inequality. Scaling the slope witness yields `2*(C*n + D + B) ≤ A*(1-rho)*n`. Combining this with the scaled child inequality cancels the contracting margin and gives the intended `f n ≤ A*n+B`. The finite-prefix branch uses `A*n ≥ 0` and the same `B`. These algebraic steps need ordered-ring operations, not a field.

I checked the inequality directions, the two independent child calls, the second copy of `B`, and the use of the eventual hypotheses only above `n0`. No source-level circular premise, omitted zero case or sign assumption was found. Actual tactic elaboration, inferred instance arguments and expanded theorem types remain unverified until a real qualified compiler/type run.

### Pinned APIs

The candidate retains Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, plus the unchanged eight additional dependency pins. All ten repository configuration/checker files match the prior qualified XP01 profile byte-for-byte. That source/configuration equality supplies no XR execution or object-authenticity credit.

I independently read the exact pinned definitions and relevant contexts for `Archimedean.arch`, `exists_nat_gt`, nonempty `Finset.sup'`/`le_sup'`, `Nat.cast_le`, `Nat.cast_lt`, `Nat.one_le_cast`, natural cast nonnegativity, `nsmul_eq_mul`, both multiplication monotonicity directions, and the generated additive form `le_add_of_nonneg_left`. The strict ordered-ring hierarchy supplies the ordered-ring, nontriviality and characteristic-zero capabilities used by these casts. I also read the rational and integer Archimedean instances and the official installed Lean source contexts for `Nat.div_lt_self` and `Nat.div_mul_le_self`. Every inspected Mathlib source file matched its immutable pinned blob. The ledger distinguishes complete files from bounded API excerpts.

The core imports only the Archimedean definitions and finite/order/tactic dependencies. The broader `Archimedean.Basic` import, including rational support, is confined to the client module. Existing `Applications/Resources/Growth.lean` is unchanged and was fully read; this scalar one-sided theorem neither imports it nor silently turns signed upper bounds into norm-based asymptotics.

## Connected example and boundary assessment

| Client group | Independent assessment |
| --- | --- |
| Actual quarter recurrence | `quarter` has base `n ≤ 1 ↦ 1`; otherwise it computes `2*quarter(n/4)+n+1`. Definition-level termination uses the actual division child and proves `n/4<n`. Separate base and recursive equations remain public. |
| Quarter observations | The six expected values were independently calculated: `Q(0)=1`, `Q(1)=1`, `Q(2)=5`, `Q(4)=7`, `Q(8)=19`, `Q(16)=31`. Proofs use the branch equations, not an unrelated scalar definition. |
| Quarter generic connection | The rational cast is passed to the generic theorem with two children `n/4`, cutoff 1, `rho=1/2`, `K=0`, `C=1`, `D=1`. The actual floor-division inequality gives the child-sum premise; the actual recurrence equation supplies the step premise. |
| Signed integer client | `signed n = -(n:Int)-1` has base -1, independently proved nonpositivity and an explicit recurrence through two zero children with signed toll coefficient -1 and offset 1. Its generic application is over integers, not a field or a nonnegative surrogate. |
| One-sided versus absolute value | `negative_square_upper` is over the ordered commutative ring without an unnecessary Archimedean premise. The integer example at 2 has upper bound zero but absolute value four. It establishes the stated boundary; it is not falsely advertised as the pending noncontracting recurrence theorem or a proof of every possible Big-O failure. |
| Parameter family | For each natural parameter `p`, the constant integer-valued function has an affine bound through the same public generic theorem. Separate natural and integer counterstatements refute choosing one pair for all `p,n`; at `n=0` choose a parameter exceeding the proposed intercept. The placement `∀p, ∃A B, ∀n` is not interchanged with `∃A B, ∀p n`. |

These clients use actual public laws and independently meaningful observations. There is no throwaway wrapper that assumes the desired result, no default payload, no timing model substituted for an order inequality, and no synthetic recurrence record introduced merely to feed this theorem.

## Complete explicit declaration surface

The source contains **21 explicit public named declarations**: one core theorem and twenty client declarations (two definitions and eighteen theorems). There are no new instances, private named declarations or anonymous `example` commands in these two modules. Local `have` proofs remain part of the fully read theorem proof. Generated recursion equations, termination auxiliaries and other elaborator-generated declarations are not counted as absent; they remain within the eventual exhaustive audit.

The exact 21 fully qualified names, source locations and authored headers are recorded in `source-preparation.json`. This source inventory is not actual expanded type output. All 21 actual type inspections remain pending, and no existing Foundation, Chapter 2 or XP01 statement count is changed.

## Documentation and frozen-scope boundaries

The dedicated note and the new map section accurately describe the generic scalar result as an uncompiled shared draft. They distinguish a signed one-sided upper bound from an absolute-value/norm bound, an eventual proof cutoff from definition-level termination, and fixed parameters from a bound uniform across an external family. Source identities/citations are retained. This Standards review checks their mathematical and architectural claims against the frozen scope; it does not replace the independent Spec source-correspondence axis.

The original book-specific natural-ceiling laws and negative-offset boundary, sharper displayed constants (including potentially negative intercepts), selector-to-scalar correspondence, grouping bounds, source algorithm connections and genuine noncontracting halving counterexample remain Chapter 3 obligations. The current generic theorem may choose a looser nonnegative intercept; it does not claim to prove the pending sharper source statements. The optional internal quantitative helper from the preflight is not an unfulfilled frozen requirement. No later chapter is accepted by the existence of this shared unit.

### Existing finding carried by the original branch

**XP01-DOC-001 — inherited in d64; carry the existing fix on incorporation.** At `docs/research/fdsa-reconstruction-map.md` lines 466–471, the unqualified sentence saying that `Resources.erasureSquare` is the only existing public-interface adjustment is unchanged from the original XP01 parent. That is too broad once `Potential.budget` and `budget_append` are generalized. The later independently reviewed XP01 successor scopes the sentence to Chapter 1. This XR preparation records that exact existing issue and the required carry-forward, without changing its stable ID, silently declaring the historical draft corrected, or modifying the resolved XP01 review.

There are no additional concrete XR source findings. Pending compiler/type/full-check evidence is tracked as pending evidence, not disguised as a zero-finding final approval.

## Remaining gates and method limits

The next actual validation must bind to the incorporated immutable candidate and retain the complete original XR scope. It must establish qualified focused compilation, then secure and independently assess every actual expanded public type. Acceptance still requires the applicable whole-candidate output-integrity check and proof audit, complete independent Standards and Spec outcomes, and immediate verification of the exact approved candidate before a local fast-forward. Normal-versus-fresh rules and all proof restrictions remain unchanged; no unnecessary fresh run is prescribed by this source preparation.

The central outputs are retired/unusable and were not consumed, fingerprinted or modified. No process was polled, no compiler was launched and no cache/source/ref changed. Existing F/C2/XP reports were hash-checked before and after the only writes, which are this new XR report and its own provenance. The Foundation run remains root-owned; no terminal or type evidence is inferred from its age or historical session identifier.

One read-only metadata command initially requested the nonexistent root `lakefile.lean` and failed; the corrected discovery read the actual `lakefile.toml` and confirmed all ten configuration identities. This bookkeeping lookup was not a compiler or validation command. The exact source/type/configuration boundaries and this qualification are preserved in the preparation receipt.
