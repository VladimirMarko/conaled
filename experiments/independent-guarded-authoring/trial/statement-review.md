# Statement review of the independent inv-inv caller

This is the author's statement review before archival and outside evaluation.
It does not replace the later independent evaluator or Standards/Spec reviews.
The reviewed caller is `work/Attempt.lean`, SHA-256
`4dc308b0b8cf2e69b322796c264092e1025bfb2f9fdf21ddc6a33a7b3e66133a`.

## Source correspondence

The upstream theorem quantifies over an arbitrary type, endpoints and path,
and inhabits the identity between double inversion and that path. The caller's
`involutionTyped` quantifies over arbitrary expression variables V, assumption
list Ω, context Γ, family A, endpoints x/y and path p. Its premises are exactly
`Tm Γ A x`, `Tm Γ A y`, and `Tm Γ (Id A x y) p`. Formation information is
recoverable from these conventional typing judgments. It does not assume
involution, reflexivity of p, a model-code equality, or a semantic result.
Its conclusion is a generated term of
`Id (Id A x y) (doubled Γ A x y p) p`, retaining the expression
`involution Γ A x y p` as certificate.

Agda's ambient type and level parameters are represented by external schema
parameters, as declared before construction. The caller does not encode
Agda's universe hierarchy or its function types. Upstream pattern matching on
identity uses the available J principle; no additional elimination rule was
introduced. `reverse` is a generated J term with endpoints exchanged, and
`reverseRefl` checks the upstream reflexive computation. The semantic
`reverseRecipe_eval` independently identifies its interpretation with actual
categorical inverse. Thus the double operation is tied to upstream `inv`, not
merely an arbitrary operation whose square happens to be identity.

The selected theorem is smaller than #106's associativity trial: it has one
path and no extra dependent argument tail. It uses the frozen guarded theory's
nil-tail based-J instance. Success does not measure elimination with a
nonempty dependent tail, nor isolate a productivity effect of the repair.

## Source helpers and their checked uses

| Claim group | Statement and intended use |
| --- | --- |
| `basedTyped`, `basedBeta`, `basedSub` | Import already derived generic contextual J typing, root computation and reindexing into the named guarded theory through its existing import combinators. Explicit contexts bind all parameters; these add no source rules. |
| `motiveTyped`, `motiveRoot`, `branchTyped`, `genericTyped`, `reverseTyped`, `reverseRefl` | Type and compute the generated inverse with exchanged endpoints. The branch uses a path-level reflexivity in the correct family. The general source theorem and C4 single-inverse checks consume these definitions. |
| `reverse_subst`, `reverseSub`, `reverseCongr` | Distinguish raw expression substitution from typed source substitution and equality congruence. The former supports arbitrary-expression semantic evaluation; the latter normalize the involution's J branch and reindexed conclusion. |
| `doubledTyped`, `doubledSub`, `doubledCongr`, `doubledRefl` | The second inverse returns to the original endpoint order. Reindexing changes context and all five supplied arguments; no path argument is dropped. |
| `doubleTyped`, `involutionMotiveTyped`, `doubleRoot`, `involutionRoot`, `involutionBranch`, `involutionGenericTyped` | The motive is an identity at the path level, including the arbitrary path variable. Its root is the identity of reflexivity with itself. Conversion uses derived equalities, not an assumed source conclusion. |
| `pathProofAt`, `doubleAt`, `involutionAt`, `involutionTyped` | Substitution at the supplied endpoint recovers exactly p and double inversion of p. These establish the intended arbitrary-path conclusion rather than only a reflexive case. |
| `involutionReindexed`, `involutionRefl` | Reindexing retains the substituted original certificate, with normalized endpoints. The reflexive case compares the selected source certificate to the selected second reflexivity. No equality with a freshly constructed certificate after arbitrary reindexing is claimed. |

## Semantic claims and applications

`inverseSection` has objects equal to the categorical inverses of the supplied
path-section objects. Its naturality proof uses the supplied section's
naturality. It quantifies over arbitrary groupoid context G, arbitrary family
`A : G ⥤ Grpd`, and arbitrary endpoint/path sections. A is not assumed constant,
discrete or faithful. `paths`, `carrier`, `first`, `second`, `witness`, `motive`,
`branch` and `selected` expose the actual ordinary-model interpretation of the
source inverse. Their evaluation lemmas and `selected_inverse` identify the
selected J section, including its reflexive boundary. `selected_at` then
identifies its application to the caller's arbitrary p.

`environment` interprets all five schematic source inputs. `inputs_valid`
proves each of the three source typing hypotheses for those actual inputs;
there is no unsatisfied semantic premise. `double_eval` identifies the
source double operation, and `conclusion_eval` identifies its path-level
identity type. `certificate_evaluates` applies the frozen guarded soundness
interface `source.evaluates` to the actual `source` derivation. Its existential
witness is constrained by equality to evaluation of `certificateRecipe`.
A separately supplied identity witness cannot replace it.

`double_inverse_from_source` extracts the ordinary arrow equation from the
section obtained by that same soundness application. Its proof does not appeal
to the target's double-inverse theorem. Ordinary groupoid identity fibers are
discrete, allowing this extraction; the claim does not infer faithfulness for
models with nontrivial higher identities. Its model parameters C/B remain
explicit even though the final arrow equation no longer mentions them.

For each C4 label n and each supplied primitive model B, `certified` retains
both the actual source-certificate evaluation and the observed double-inverse
label. The faithful and ineffective examples specialize this universal result
at arbitrary n. The nonzero examples check 1 to 3 under single inversion and
1 to 1 under double inversion in both models. `ineffective_distinct` proves
that observing the source double inversions at labels 1 and 0 gives different
arrows despite the frozen ineffective primitive action. The latter action
property is inherited from the public ineffective model; the new inequality
consumes `observed_eq`, which in turn consumes the source-derived result.
These inputs witness satisfiability and rule out interpreting all source paths
as reflexivity. They do not provide a new construction of the frozen models.

The single-inverse negative-label normalization uses categorical inverse
uniqueness and the group inverse cancellation law. This identifies the
meaning of the new source operation. It is not a target-only proof of the
selected double-inverse theorem. The general double-inverse and C4 consumers
remain connected to the source proof through soundness.

## Scope and acceptance limits

The checked targeted caller has no authored `sorry`, `admit`, or new axiom.
Failed elaborations and recovery-sorry diagnostics are retained as failed
attempts, outside the validation import closure. No frozen API, production
resource limit, dependency revision or selected statement was changed.
Targeted checks alone do not constitute full acceptance; the isolated overlay's
full fresh build and exhaustive proof audit are recorded separately. Final
independent mathematical evaluation and code reviews occur only after archive.
