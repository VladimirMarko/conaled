# Coordinator statement acceptance

Both closed submissions satisfy the frozen calibration and held-out contract.
This assessment applies to the exact SHA256 sources in `author-archive.json` and
`replay.json`. It follows source and elaborated-type inspection, not the authors'
own coverage claims. `AuthorTypes.lean` and `author-types01.txt` retain every
submitted declaration's type and transitive axiom query. The integrated
exhaustive audit remains the acceptance audit, including generated auxiliaries.

| Frozen requirement | Baseline coverage | Candidate coverage | Result |
|---|---|---|---|
| Calibration comparison and operand typings | `calibration`, `calibrationLeft`, `calibrationRight` invoke the existing command reconstruction API | `calibration : TypedEquality` packages substituted/fresh operand derivations and equation | Both pass |
| Arbitrary finite tail and dependent p:Q | `certificateCommand` quantifies n, T, Q, p and their source derivations with arbitrary code indices | `certificateCommand` quantifies n, T, Q, p and source hx, hT, hp under Ω | Both pass |
| Selected J recipe and branch alignment | `Motive.reflexivity` forms identity motive, substitutes p along rootTail, forms reflexivity and converts by symmetric identity substitution; `certificate` is the generic J derivation | Explicit identity motive and reflexive pulled-back branch; `branchTyping` converts by symmetric `identitySub`; `certificate` retains `selected` | Both pass |
| Two arbitrary dependent substitutions | `valueTwice`, `certificateTwice` apply `TmDeriv.sub` twice to arbitrary hσ, hτ | Same two source substitutions through `Tm.substitute` | Both pass |
| Family and selected-term comparison | `valueTypeComparison`, `certificateTypeComparison`, `valueComparison`, `certificateComparison` use the source composition rules with explicit semantic indices | Same names use source family and term composition rules | Both pass |
| Certificate conversion | `certificateAligned` retains raw term, converts dependent family and derives annotation cast via source soundness | `certificateAligned` retains selected term and converts its source family | Both pass |
| Actual dependent weakenings | `firstWeakening` constructs L.k, `witnessVariable` is k, `secondFamily` is identity on k in the weakened family, `secondWeakening` constructs Δ.h | `firstWeakening`, `witnessVariable`, `secondFamily`, `secondWeakening` construct the corresponding source judgments | Both pass |
| Generic argument applied to weakenings | `dependentWeakeningCertificate`, `dependentWeakeningComparison` invoke generic declarations with constructed substitutions | Same names; `dependentWeakeningAligned` also instantiates conversion | Both pass |
| Selected value and certificate validity | `valueValidity`, `certificateValidity` use the checked interpreter returning a semantic section, equated to the exact nested substitution code | Same names interpret actual source judgments under hΩ; original validity is retained separately | Both pass |
| Dependent type alignment validity | `certificateTypeValidity` interprets the actual source family comparison; hQ, hp, hσ, hτ are included explicitly | `certificateTypeValidity` interprets the source equation with hp, hσ, hτ and satisfied Ω | Both pass |
| Stable extension, exact selected data | `extensionSelected`, `extensionValue`, `extensionType` use unchanged full-model reduct with explicit Stable parameter | `extensionSelected`, `extensionValue`, `extensionType` include validity/equations and exact embedded evaluation recovery; `extensionSelectedTwice`, `extensionValueTwice` retain repeated substitutions | Both pass |
| Actual extension reuse | `extendedCertificate` reuses the source derivation unchanged; `extendedValidity` interprets it in the underlying full model | `extendedCertificate` embeds with `Sigma.retain`; `extendedAssumptions` derives embedded Ω validity; `extendedValidity`, `extendedTwiceValidity`, `extensionAlignedValidity` use the Sigma interpreter | Both pass |

No declaration assumes the desired composition equation, the selected output,
UIP or equality reflection. The baseline's code indices are quantified
parameters constrained by source derivations; they are not evidence of native
models only. The candidate interpretation uses arbitrary full `Typed.Model`,
ρ and validity of original Ω. Its `eval_old` equations are paired with source
validity and cannot replace that obligation. `Stable` is intentionally unused
by baseline old-language interpretation: the selected extension has that exact
full-model reduct. The candidate uses `Stable.toCapability` to admit Sigma.
Neither arm authored a new Sigma term, and neither claims a higher model.

Object-language `Id_Q(p,p)` is the certificate family. Source judgmental
equations compare substitution forms. Host equality compares source recipe
expressions or interpreted values. None is silently identified with another.
The generic task permits zero-length and all finite tails; the retained
inhabited application has three dependent binders. The two added families
explicitly depend on p and then the first generic witness k.

`Examples/DependentAuthorTrialReplay.lean` independently probes the baseline
motive, reflexive branch, semantic motive and exact reference branch annotation.
Its explicit `selectedTyping` type checks the actual generic J raw expression
and selected code. The candidate's selected expression and branch match the
frozen reference at arbitrary source inputs. These probes are coordinator
acceptance work; they add no result to the measured source.

`Examples/DependentAuthorTrialCases.lean` retains the prospective inhabited
native inputs, reference interpretations and constructor cases. Its post-trial
`author_*` declarations consume each accepted submission at the three-binder
tail and actual dependent weakenings. Candidate cases prove original and
extended certificate validity, the selected J section itself, and its exact
value after both substitutions and extension. The baseline cases consume its
checked interpreter and interpreted source comparison. The native model has
varying finite fibers. Constructor cases retain nonconstant Sigma reindexing,
noncommuting substitutions, selected dependent elimination and beta; the frozen
#317 capability supplies judgmental eta and stable comprehension. These are
constructor/model-builder evidence, not credited as author-built Sigma terms.

Focused author/case build passed in `author-cases01.txt`; recipe probes passed
in `author-recipe02.txt`. The preceding evaluator attempt failed only because
Lean field notation did not expand a local notation without parentheses;
`author-recipe01.txt` retains that failure. This is coordinator probe development,
not a measured author failure or a repaired submission. All exact author bytes
are unchanged. Their module status is documented by the importing experimental
cases module rather than inserting headers into measured sources.
