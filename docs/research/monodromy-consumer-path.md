# The retained monodromy consumer: admission and construction obligations

Assessment for [#428](https://github.com/VladimirMarko/conaled/issues/428),
inspected at `a95a5ef`. This is a source and declaration audit, with a proposed
acceptance procedure. It adds no Lean theorem and does not rerun the retained
Agda check. The existing source receipt and the new properness replay certify
different closures; neither certifies an Agda-to-conaled interpretation.

The first work to prioritize is the source-declaration inspection alongside
small-family classification and circle construction. Glue then depends on the
classifier; the complete interpretation depends on all these constructions
and the exact source conversion rules. A successful native integer-action
example remains useful, but cannot discharge that interpretation obligation.

## Frozen source and declaration trace

The source is [Monodromy.agda](../../experiments/dependent-higher-identity/Monodromy.agda),
SHA-256 `bbca6eabc7d35040fd5bb1fcc84f49c12ddfcfb90ffc2edb6d922a8c6e622aa3`.
Its generic argument is [FrozenMemo.agda](../../experiments/dependent-higher-identity/FrozenMemo.agda),
SHA-256 `48ac4bcb111b63339678cdbb9cc3fa26afe77f8a3476715ebd76e9dfad73c00f`.
Keep Agda 2.8.0.2 and Cubical commit
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. The
[experiment receipt and reproduction instructions](../../experiments/dependent-higher-identity/README.md)
record safe checking, explicit library selection, hashes and the whole-module
import graph. That graph includes unused declarations. It is not a minimal
proof-dependency graph or an exported checked derivation.

The following trace follows the actual source bodies, including the pinned
upstream [inductive circle adapter][circle], [conversion definitions][conversion]
and [integer successor path][integer]. It identifies required declarations,
not an assertion that every transitive primitive dependency has been extracted.
That extraction and its correspondence evidence belong to #115/#422.

| Declaration | Actual requirement and downstream use |
|---|---|
| `FrozenMemo.Memo (A) (B)` | Universe-polymorphic types and dependent families; inductive identity, its transport/J and reflexive computation; dependent pairs. The generic proof does not assume univalence. |
| `Memo.v`, `η`, `W`, `w` | Two transports, their composition comparison, and the selected pair of value and comparison witness. `η refl refl u = refl` uses identity elimination. |
| `Memo.K`, `apd-η`, `higherType`, `higherWitness` | Transport of the selected comparison in a family indexed by an identity proof. Retaining only the endpoint value loses the type and witness of this obligation. |
| `Γ`, `Δ`, `Θ`, `σ`, `τ`, `σ∘τ`, `w-twice`, `apd-twice` | Dependent records, projections, substitutions and their composition. Both twice-substituted comparisons are source `refl`; interpretation must validate the promised conversion as well as their result types. |
| Upstream `sucPathℤ` | `ua (sucℤ , isoToIsEquiv (iso sucℤ predℤ sucPred predSuc))`. This uses a path between types from a specified equivalence, with successor orientation. A native `Equiv` alone does not supply this source operation. |
| Upstream `S1.loopPath`, `loop`, `S¹-rec`, `Cover` | Circle point/path constructors; `loop = pathToEq loopPath`; `S¹-rec b l = S1.rec b (eqToPath l)`; `Cover = S¹-rec ℤ (pathToEq sucPathℤ)`. The cover crosses Path and inductive identity in both directions. |
| Upstream `pathToEq`, `eqToPath` | `pathToEq` uses Path J into inductive equality; `eqToPath refl` is the constant path. Admission must cover the actual indexed identity and primitive conversion used here. Importing all `PathIsoEq` theorems is not justified merely by importing its module. |
| `circle-loop`, `step` | Abstract source definitions; `step n = refl` checks transport in `Cover` along the selected inductive loop against `sucℤ n`. A merely propositionally similar target computation does not automatically validate this source conversion. |
| `input`, `erased-input`, `two-steps` | Same second loop composite, different first loop. `two-steps` composes `η`, `ap`, and `step`; it does not simply evaluate a numeral. |
| `transport-three`, `transport-two` | Source proofs observe the first component of `second-w` as `pos 3` and `pos 2`. They depend on the preceding transport argument. |
| `value-and-witness-twice`, `transported-witness-twice` | Preserve the whole selected pair and its transported comparison under the two substitutions, by the generic theorems. They must accompany the integer observations. |

The circle adapter also defines `S¹-elim` and its loop equation. Those are
relevant to #421's general dependent-circle contract. The direct `Cover` body
uses `S¹-rec`; the stronger eliminator should not be mislabeled a direct call
from `Monodromy.agda`. Likewise `HigherWitness.agda`'s K(ℤ,2) construction is a
separate consumer, not a prerequisite silently imported into this task.

## Connection status at the inspected revision

“Constructed” below means a named existing artifact in its own setting.
“Assumed” means evidence a caller must presently supply. “Missing” means the
connection needed for this particular source has not been constructed here.
Existing Lean declarations are inspected source evidence with their original
acceptance history; this documentation change makes no fresh build claim.

| Connection | Status and exact artifact | Remaining owner |
|---|---|---|
| Agda source typing and selected source observations | Constructed in the retained source and its `validation.json`; trusted Agda primitives remain part of its foundation | #422 preserves these hashes and judgments |
| Completed Agda declarations → explicit admitted target judgments | Missing. Surface files and `imports.dot` are available; no checked declaration export or translation of this argument is supplied | #115 inspects bodies/types/options/levels/opacity and dependencies; #422 proves admission |
| De Morgan dimensions and substitutions | Constructed local `Expr`, `Expr.Conv`, `Cube.Hom`, `Cube.connection` in [Dimensions.lean](../../SquareKit/Internal/Cubical/Dimensions.lean); source correspondence still missing | #422, with #421's source rule inventory |
| External lawful dependent families | Constructed `FamilyData`, `LawfulFamily`, `LawfulFamily.reindex` and `reindex_comp` in [FamilyData.lean](../../SquareKit/Internal/Cubical/FamilyData.lean). Supplying a particular lawful family remains a caller obligation | #419 constructs classification; #421 supplies the circle family |
| Internal small-family codes, decoding, substitution and integer closure | Missing at the required scope. External `LawfulFamily` is not an internal classifier. Finite codes cannot classify this integer cover | #419 |
| Glue, universe filling, `ua` and successor transport | Missing at the required scope. Listing an equivalence or filler as a field would leave it assumed | #420 after #419 |
| Circle construction and dependent elimination in the selected model | Missing for this source contract; accepting an external family is only a conditional intermediate | #421, independently of completed universe/Glue |
| Restricted cubical transport | Constructed `Filling.transp`, `transp_on_face`, `transp_reindex`, `transp_computation` in [RestrictedTransport.lean](../../SquareKit/Internal/Cubical/RestrictedTransport.lean), assuming lawful filling and the specified constancy data | #422 must connect the actual source `transp`/`hcomp` uses; #420 constructs required universe filling |
| Marked identity → source indexed inductive identity/conversion | Missing correspondence. `normalizedIdentity`, `normalizedIdentity_reindex` in [NormalizedIdentity.lean](../../SquareKit/Internal/Cubical/NormalizedIdentity.lean) do not establish `pathToEq` conversion | #422; inspect early with #115 |
| Interpretation of `FrozenMemo`, records, two substitutions and `step` | Missing as one connected derivation for this model, even though generic semantic operations exist | #422 |
| Interpreted pair, transported witness and 3-versus-2 observation | Missing target acceptance artifact; source results exist | #422 |
| Target evaluation and cost | Not supplied by semantic conversion preservation; excluded from this checkpoint unless separately contracted | #235 names a consumer before extending scope |

The reference mathematical construction is [CCHM v1, Definition 18 and §8.3][cchm],
as analyzed in the [universe construction assessment](cubical-universe-glue-milestone.md).
That model theorem has its own size and rule assumptions. It does not certify
Agda's split primitives or indexed matching. The primary source bodies above
are the basis of this task's additional admission obligations; a generic
citation to univalence cannot replace them.

## End-to-end acceptance and rejecting checks

This is a proposed executable-check plan for #422, not an implemented script.

1. In a fresh checkout, hash both frozen files and the pinned dependencies, then
   use the experiment's documented `check.py` command with a new work directory.
   Retain the source receipt, including failed diagnostics. Do not replace its
   source/toolchain pin with checkpoint 096-10's unrelated closure.
2. #115 exports or inspects completed declarations for the table, retaining
   levels, bodies, opacity, builtins, typing options, relevant primitive rules
   and unresolved metadata. #422 builds a declaration-to-judgment manifest and
   proves its correspondence. A hand-written admission may suffice at this
   bounded scope if each actual source derivation and rule is accounted for;
   an unverified dump is not itself a proof certificate.
3. Instantiate #419–#421 constructions at the declared universe levels. Build
   interpretations of `Cover`, `circle-loop`, and `step`, with term and dimension
   substitution and the exact promised conversion equations. Audit the claims
   before relying on source `refl` to translate as reflexivity.
4. Interpret `FrozenMemo` and its chosen arguments, obtaining the selected pair
   and transported comparison. Check both repeated-substitution theorems and
   both integer observations from these interpreted terms, without separate
   target proofs substituted for their source derivations. Run the applicable
   README build/proof audit on those new Lean declarations.
5. Require controls: erasing the first selected loop changes 3 to 2; reversing
   the successor equivalence fails the `step` orientation; replacing the
   universe by finite codes fails integer admission; absent lawful filling
   fails model admission; dropping the transported witness fails the stated
   output type. A malformed source rule should be rejected, not accepted with
   an assumed compatibility field. Record whether each rejection is a typing
   failure, theorem/countermodel or runtime diagnostic.

For a Cartesian route, the [judgment comparison](cubical-judgment-compatibility.md)
shows that a coordinate-preserving dimension-expression translation cannot
represent `i ∧ j`. The separate `contract-cube` example tests that obstruction;
it is not a new premise of this monodromy proof. A Cartesian rederivation using
Kan operations remains eligible, but must name changed source rules and prove
its correspondence rather than claim literal unchanged admission.

The native comparison should apply the integer successor equivalence directly
and compose its actions, checking the same numerical outputs. Charge only its
actual obligations and report its missing source-derived witnesses. It supplies
a cost-of-adoption baseline, not evidence of importing the proof. No additional
native implementation or measured comparison was produced in this assessment.

## Priority and independent-consumer handoff

Run #115's selected declaration inspection early, alongside #419 and #421.
In particular, resolve whether the selected indexed identity conversion has an
admitted target rule before describing #420 as the only missing prerequisite.
#420 depends on #419; #422's final acceptance depends on #420 and #421 plus
source admission. Preparation of #422 can proceed now. #428 is not a blocker
on independent construction, and #115 need not become a general importer.

For the independent consumer, start at the [experiment README](../../experiments/dependent-higher-identity/README.md),
this connection table and the construction tickets. The supported entry point
today is reproducible Agda checking, not a public Lean importer. Once #422's
interface is reviewed, hand over pinned source, model package, admitted-rule
manifest, example invocation, reproducible checks and a list of required caller
inputs. The consumer supplies supported source declarations and their explicit
requirements; the library must supply constructed model capabilities and
compatibility proofs it advertises. Success means reproducing the interpreted
pair, dependent witness and observations through that entry point without
private repairs. Record any assistance. Trial execution and productivity
conclusions remain separate; do not consume #108's protected fresh theorem.

This bounded consumer uses no smooth or cohesive premises. It cannot close
#100/#102 or the technical smooth interpretation #433. #107 is resumed; #433
waits only for named technical dependencies, not a favorable #108/#434 author
assessment. The [properness verification](myers-properness-096-10-verification.md)
additionally rules out treating #435's external properness as unrestricted
internal properness without a new comparison theorem. That verified conditional
obstruction constrains a future bridge; it neither refutes this circle model
nor supplies it. #426's modal/higher diagram and #435's finite-action consumer
can proceed independently.

[circle]: https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/Data/Equality/S1.agda
[conversion]: https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/Data/Equality/Conversion.agda
[integer]: https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/Data/Int/Properties.agda#L566
[cchm]: https://arxiv.org/html/1611.02108v1
