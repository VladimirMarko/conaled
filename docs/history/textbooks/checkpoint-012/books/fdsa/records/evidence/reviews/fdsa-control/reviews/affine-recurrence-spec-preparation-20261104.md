# XR01 affine recurrence — independent Spec source preparation

## Current disposition

**Overall: Blocked.** This is the independent nonauthor Spec preparation for the entire original XR01 scope at immutable candidate `d64b4c89fb9f21d1a6a2a603c1dc04f47233d9e2`, against fixed base `c28ba71863d2a35ee1c3a089caa90464e4cca692`. The complete frozen mathematical scope and all five changed files have been read. There are **zero new concrete Spec source findings**. This source assessment supplies no compiler, actual expanded-type, full candidate-check, axiom-audit, final review, immediate-verification, integration or chapter-acceptance credit.

Reviewer: `/root/chapter02_spec`, which authored none of the reviewed source. This continues the existing whole-book review process and does not start a replacement acceptance loop. The parent authorized the read-only assessment before checkpoint 0102 and released writes only for this dedicated source-preparation report and its own provenance after that checkpoint was verified and exposed. The reviewer did not run a compiler, poll a build, inspect live generated outputs, mutate source or Git references, or change a cache, ticket, pin, global control file, or earlier review.

The preserved Chapter 1 acceptance remains at `07e480f6ec9958d4975bb90151005b84f2907614`. The exact Foundation candidate `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` remains subject to its own pending terminal and type evidence. The original XR snapshot predates the accepted Chapter 1 incorporation and the later XP01 corrections; neither is silently substituted into this review. The parent's recorded F → combined-four → XU02 → XU03 → Chapter 2 route and later chapter order remain unchanged.

## Exact scope and read boundary

The scope is the complete base-to-candidate change, including the whole contents of each changed file, not merely the newly added lines. The Git diff has exactly these five paths and 512 insertions; the candidate's sole parent is the fixed base.

| Immutable path | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Applications/Resources/AffineRecurrence.lean` | 113 | 5,839 | `0f867ba6fa96cbeaaaeeba6c4a24cc71b38fdbf798b684d484234eabb283d17d` |
| `Examples/AffineRecurrence.lean` | 142 | 5,165 | `eb9239f5810887ba988420c3fe8538eab21285c1e6173eb5467133baa63868d5` |
| `SquareApplications.lean` | 256 | 8,431 | `c7abc390617e80c42c2b604528748fcebe794f869d8abeae88a07a69864ea3ef` |
| `docs/research/fdsa-affine-recurrence.md` | 233 | 9,975 | `a07b086bc846c0898b2713a7b055b9cb451d0471c655eeaab9cc1077f32b87bf` |
| `docs/research/fdsa-reconstruction-map.md` | 500 | 32,550 | `4e8acd033864e106e6881d8d5bb3d73993f9c6c65bee14d072553eadf392789b` |

The complete 96-line frozen requirements have SHA-256 `5873700a349c359d15873829f1399a20225fa80eaa980e7ad9f1e4c8f774dd02`. The complete 80-line handoff has SHA-256 `4c205b012b58219b0022427e32a12717dd46bd25a38ae68f53c62d16b8baeab4`. The complete 464-line preflight has SHA-256 `dc20f947d2ff84ece47299a2403c9166d28f8c6103697e3b4b6b28842979b273`. The preflight was read in contiguous bounded ranges 1–160, 161–320 and 321–464; the map in ranges 1–160, 161–320 and 321–500. No truncated output is credited as read.

The applicable `AGENTS.md`, implementation, shared review-loop, code-review and example-driven rules, architecture/domain instructions, glossary and relevant ADR/language-direction guidance retain their independently read XP01 identities at this snapshot. The exact reuse comparison is in the companion receipt; this is reuse of already completed instruction reads, not a claim that a changed instruction was skipped. README normal-versus-fresh acceptance rules remain applicable. A source change alone does not invent a new fresh-baseline requirement, and a focused build is not a complete candidate check or audit.

The machine-readable read and semantic receipt is `../provenance/affine-recurrence-spec-preparation-20261104/source-assessment.json`. It preserves Git blob identities, read ranges, source declarations, primary-source boundaries, API read ranges, requirement-to-result accounting, and the unchanged earlier report identities.

## Primary source and correspondence

The supplied book PDF is the July 27, 2026 edition, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. I independently read its extracted text lines 1837–2027, covering printed pages 41–43 and the following scalar-to-selector composition proof on page 44. I also visually inspected complete printed pages 41, 42 and 43, rendered from zero-based PDF indices 46, 47 and 48. The three images are regenerable primary-source viewing artifacts, not task source, and are retained outside the checkpoint payload at `/workspace/scratch/b4a17a285e23/research-source/xr01-page-renders/`. Their exact bytes/hashes, page indices and completed visual-read credit remain recorded in this report's dedicated provenance. The original PDF/extracted text are likewise external primary-source viewing inputs. The text input has SHA-256 `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333`; literal newline indexing was used, so form-feed page boundaries do not shift the recorded line ranges.

Theorem 3.9 fixes the recurrence and coefficients before choosing constants that cover every natural input. Its real-valued equality recurrence has positive coefficients `a,c`, `a+c<1`, and a nonnegative linear toll coefficient; the offsets, constant toll and function values are not required to be nonnegative. The text's preliminary coefficient prose names `a,b` where the child coefficients are `a,c`; the numbered theorem is unambiguous. The displayed strict slope condition is stronger than the subsequent maximum choice guarantees. The frozen ledger correctly retains the sufficient non-strict version and the original sharper witness obligations separately.

XR01 is a justified abstraction of that induction argument, not a completed formalization of the displayed rounded source theorem. It uses arbitrary natural child maps, an upper recurrence, and a strict contraction bound on the child-size sum. The signed ordered-ring formulation and division-free witnesses are documented explicitly. The actual rounded source adapter, original prescribed constants, natural-valued corollary, source scalar recurrence and uniform selector connection remain future Chapter 3 work. In particular, the quarter example does not stand in for median-of-medians cost correspondence.

The preflight and public note retain Manuel Eberl's `Selection.thy` identity at Isabelle `f86f290225eebcc52c1ae7dba2e098f405f51c21`, theory SHA-256 `c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8`, and its BSD-3-Clause attribution. I retain that attributed earlier inspection and the supplied preflight's statement account. I did not freshly read or rebuild the complete original theory in this continuation, and do not claim that its revision generated the earlier PDF. No Isabelle/AFP proof is a Lean dependency. The complete supplied book statement and the ordinary arithmetic argument suffice for this bounded source assessment; no new general external-proof gate is introduced.

## The generic theorem

The sole new core public result is `Resources.AffineRecurrence.exists_affine_bound_of_two_branch`. At the source level its assumptions are precisely a `CommRing`, `LinearOrder`, `IsStrictOrderedRing` and `Archimedean` scalar carrier; a total `f : Nat → R`; two total natural child maps; a natural recurrence cutoff; fixed coefficients; `rho < 1`; the eventual affine child-size sum bound; and the eventual affine upper recurrence. Its conclusion chooses nonnegative `A,B` before all natural `n`. No final upper bound, function monotonicity, child-map monotonicity, field structure, or nonnegativity of `f,K,C,D` is assumed. These are source statements: the full elaborated type has not yet been printed or assessed.

The proof correctly chooses two Archimedean natural multiples. The first gives `2*K ≤ (1-rho)*N` for `N = max n0 (max 1 M)`. The nonempty finite range `0..N` includes zero and covers the entire enlarged prefix, including sizes above the original cutoff at which induction is deliberately not yet used. Its finite supremum, enlarged by zero, supplies the intercept `B ≥ 0`. The second multiple yields a natural-cast slope `A ≥ 0` with `A*(1-rho) ≥ 2*(max 0 C + max 0 D + B)`.

Above `N`, the two size inequalities give `2*(left n + right n) ≤ (1+rho)*n < 2*n`. Both child casts are nonnegative, so each child is strictly smaller than `n`; the cast inequalities are reflected back to `Nat` before either strong-induction hypothesis is applied. This is the required decrease argument from the contracted sum, rather than an extra assumed decrease premise. It does not purport to define `f` or establish termination of an unrelated recursive program.

The proof explicitly uses `n ≥ 1`, nonnegative positive parts of the toll coefficients, and `B ≥ 0` to establish `2*(C*n+D+B) ≤ A*(1-rho)*n`. Combining this with the two child induction bounds and the size bound gives the desired affine bound. In detail, the two child intercepts contribute `2*B`; after doubling the recurrence, the absorption inequality removes the extra `2*B` alongside the toll. The signs and multiplication directions are correct. No lower bound on `rho`, sign of `K`, or sign of the function values is silently needed. Some choices of coefficients can make the size premise impossible; the generic implication does not assert otherwise, and the retained rational and integer clients demonstrate satisfiable instances.

The use of the standard finite supremum avoids a complete-lattice supremum or a separate recurrence framework. The core has only five direct Mathlib imports for Archimedean/order/finite-range arithmetic and `linarith`; it imports no real-analysis or asymptotic module. `Applications/Resources/Growth.lean` is byte-identical to the original base and its interface is not widened. The source contains no admission, added axiom, unsafe or partial definition, kernel-bypassing proof command, custom ceiling/logarithm, or exported recurrence executor. Those source observations do not replace the required exhaustive audit.

## Connected cases and frozen requirement accounting

| Frozen obligation | Independently assessed source connection |
| --- | --- |
| One pair of constants for every input, including the enlarged finite prefix and zero | Core witnesses precede `∀ n`; the prefix range is `N+1`, is witnessed nonempty by zero, and the small-input branch applies to every `n ≤ N`. |
| Strict child decrease above the proof cutoff | Obtained from the contracted sum and nonnegative natural casts before strong induction; no decrease or final bound is assumed as a premise. |
| Nontrivial defined natural recurrence | `quarter` has the actual equations `Q n=1` for `n≤1`, otherwise `2*Q(n/4)+n+1`, with its own `termination_by n` and division decrease proof at that branch cutoff. |
| Independently known values | Public branch equations support `Q 0=1`, `Q 1=1`, `Q 2=5`, `Q 4=7`, `Q 8=19`, `Q 16=31`. The recursive dependencies and arithmetic agree with direct calculation. |
| Actual rational application | `quarter_affine_bound` applies the core to the rational cast of the defined `quarter`, with both child maps `n/4`, cutoff 1 and coefficients `1/2,0,1,1`. `Nat.div_mul_le_self` proves the size bound for all remainders, and the actual large-branch equation supplies the upper recurrence. |
| Signed nonfield application | `signed n=-(n:Int)-1` has base `-1` and actual recurrence with zero children and toll `1-n`. The generic integer application has `rho=0,K=0,C=-1,D=1`; `signed_nonpositive` independently records the expected bound. The actual application exercises the integer instance and signed premises. |
| One-sided order versus norm | `negative_square_upper` proves `-(n:R)^2≤0`; the concrete integer instance has absolute value 4 at input 2. No signed Big-O theorem is exported or claimed. The concrete absolute-value observation illustrates the stated distinction; it is not misrepresented as a complete asymptotic counterexample theorem. |
| Parameter quantifier order | `parameterwise_affine_bound p` applies the same recurrence coefficients separately to the integer-valued constant function `p`. The natural and integer nonuniformity results use `n=0` and a parameter exceeding the proposed intercept, so there is no interchange of `∀ p` and `∃ A B`. |
| Full Chapter 3 exclusions | The exact ceiling/negative-offset laws, displayed child thresholds, sharper possibly-negative-intercept constants C03-041/042, real/source/natural adapters, actual median-of-medians recurrence and selector-cost connection, generalized grouping and genuine noncontracting halving counterexample remain explicit obligations. |
| Ordinary domain modules and public-root connection | The result and clients live in resource/example modules. `SquareApplications` adds exactly `import Examples.AffineRecurrence`; that module imports the core. The unchanged `ProofAudit` imports the public root and describes inclusion of private/generated declarations. Actual checker coverage remains unexecuted. |

The integer client and parameter family are mathematical functions with actual satisfiable recurrence premises. The quarter client is an explicitly defined scalar function, not a measured algorithm or a timing claim about Lean's evaluator. Its definition-level decrease is logically separate from the later proof's enlarged cutoff. The later exact tree, balancing and Braun arguments in the preflight remain their direct chapter-specific induction obligations; the generic theorem's strict sum contraction is sufficient, not claimed necessary for all linear algorithms.

## Pinned API and source-surface assessment

The API checks used immutable Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The declarations and surrounding class assumptions of `Archimedean.arch`, `exists_nat_gt`, `nsmul_eq_mul`, `Finset.sup'`, `Finset.le_sup'`, `Finset.mem_range`, `Nat.cast_le`, `Nat.cast_lt`, `Nat.one_le_cast` and `Nat.cast_nonneg` were read. The rational and integer Archimedean instances in the pinned `Basic` file were also read. The exact official-kit Lean 4.35.0 source for `Nat.div_lt_self` requires `0<n` and `1<k`; the quarter branch supplies these for `k=4`. Its `Nat.div_mul_le_self` declaration has precisely the natural product inequality used by the rational cast client. These are source/API checks, with no claim of successful elaboration, instance synthesis or tactic execution.

The authored surface has **21 public named declarations: 19 theorems and two definitions**. The core contributes one theorem; the example module contributes 18 theorems and the two definitions `quarter` and `signed`. There are no authored private declarations, anonymous examples, or named/local instances in these two files. This is an explicit source inventory, not a count of generated declarations or kernel-safe audit roots. Termination/equation auxiliaries and every other generated declaration remain included in the mandatory whole-project audit.

All 21 source names and their line locations are in the companion receipt. Complete actual expanded-type inspection is still pending for the entire surface, including the two definitions and the examples; merely checking the core theorem or printing selected header names would not discharge that obligation. No actual XR type output has been credited. The later exact integrated candidate must retain matching source, dependency, configuration, qualified-runtime and terminal identities for any evidence used there.

## Findings and inherited history

**New XR01 Spec source findings: none.** The source argument, contracts, connected cases, documentation and full frozen scope agree at this preparation boundary. This does not assert a compiler pass or final approval.

**Inherited XP01-DOC-001 is retained, not duplicated as a new XR finding.** The exact original XR map still contains the unqualified historical sentence at lines 466–471 that the only existing public-interface adjustment is `Resources.erasureSquare`. The original XP01 draft already generalized `budget` and `budget_append`; that inherited issue was independently identified and then corrected by the explicit Chapter 1 qualifier in the later XP01 successor. The correction is not present at this immutable XR snapshot. The parent must preserve the already recorded dependency correction during eventual integration, without claiming that it was applied here. No new finding identifier or replacement loop is created.

The requirements' November 2 references to a still-pending Chapter 1 gate are dated historical context. They do not override the subsequently recorded Chapter 1 acceptance. Conversely, the current acceptance of Chapter 1 does not validate this earlier XR branch or its other unaccepted dependencies. The new XR note and new map section accurately identify this unit as an uncompiled draft and preserve later chapter boundaries.

## Remaining gates and preserved records

The parent must reconcile the exact source into the permitted integration route, retain all prior dependency corrections, obtain the applicable focused compiler evidence, qualify and independently assess the complete actual public types, secure the full immutable candidate check and exhaustive permitted-axiom audit, complete both independent final axes for the entire original scope plus any successor deltas, and run immediate `./check.sh --verify-candidate HEAD` through the qualified environment before acceptance. The exact pins, narrow disclosed native launcher adapter, proof restrictions and normal-versus-fresh README rules remain in force; the Nix waiver changes none of those gates. No result is inferred from a checkpoint, source reading, selected import or another unit's evidence.

The earlier Spec reports were read only for retained identity and remained byte-identical:

| Preserved report | SHA-256 |
| --- | --- |
| `shared-foundations-spec-continuation-20261104.md` | `450409a89197f229e88e12ff477f7c3e6b60c067fde0eef297a431163a7249d6` |
| `chapter02-spec-source-preparation-20261104.md` | `64de8e1782cf83ad2f47602171aa8dcfc70b9eb7c2b707dd1d43d3649fba6007` |
| `potential-spec-development-20261104.md` | `9bba3ac4ffa5a5dab1e8a32e3a990851f55846a16dd4a16a72605fd00e21a615` |

No Chapter 2, XP01, Foundation-145 or possible Foundation-110 type count or reuse disposition changes here. Foundation terminal review retains priority when actual evidence is supplied. No live or historical execution session was polled by this reviewer.

## Checkpoint 0103 packaging relocation

The parent requested that the three existing page renders be moved outside `fdsa-control` before checkpoint capture. They were moved without rerendering to `research-source/xr01-page-renders/`, with all three original sizes and SHA-256 identities preserved (461,101 bytes total). Only the render locations and this report/receipt/boundary packaging metadata change; every mathematical/source assessment, read boundary, finding and pending gate remains unchanged. The receipt records a recovery render recipe and identifies its historical-command limitation: the original executed render command text was not retained in the old receipt, so the saved recipe is reconstructed from the PDF pages and preserved 1010-by-1307 RGB images, using scale 1.65, and has not been executed or asserted byte-identical. F, C2 and XP reports remain unchanged.
