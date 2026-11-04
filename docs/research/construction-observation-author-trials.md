# Construction and observation author trials

Two independent AI authors completed matched direct and shared proofs for an
indexed vector client and an exact parser observation extension. Both retained
the native contracts, including every vector coordinate and selected parser
witnesses. The focused Lean checks passed. Integrated candidate validation,
proof audit, and independent Standards/Spec review remain acceptance gates
owned by the coordinating implementation workflow.

This is the bounded author-effectiveness experiment for
[#279](https://github.com/VladimirMarko/conaled/issues/279), within
[#235](https://github.com/VladimirMarko/conaled/issues/235), coordinated with
#117's methodology and #36. It tests existing Lean interfaces, not alternative
surface syntax or #286's extraction of proof requirements.

## Frozen tasks and evidence

The [protocol](../../experiments/construction-observation-authoring/protocol.md)
fixes tasks, mathematical reference results, route restrictions and the
15-minute cap. The [setup record](../../experiments/construction-observation-authoring/setup/record.md)
records public interface revision `5e5b03987d1f7ab23ea720561147e56319a85f51`
and protocol commit `21eaedeed1c78f58437b05a0197b12bcc386c9bb`.
Fresh agents received no conversation fork, designed neither selected interface,
and could read public source/docs/examples but not each other's work or private
solutions. Both inherited the same configuration without overrides. Their
[dispatch A](../../experiments/construction-observation-authoring/setup/dispatch-a.md)
and [dispatch B](../../experiments/construction-observation-authoring/setup/dispatch-b.md)
prompts are retained verbatim.

| Author | Route order | Final source | Raw report |
|---|---|---|---|
| A | A-direct, A-shared, B-direct, B-shared | [Author A](../../Examples/ConstructionObservationAuthorA.lean) | [Report and attempts](../../experiments/construction-observation-authoring/author-a/report.md) |
| B | B-shared, B-direct, A-shared, A-direct | [Author B](../../Examples/ConstructionObservationAuthorB.lean) | [Report and attempts](../../experiments/construction-observation-authoring/author-b/report.md) |

Each author retained seven pre-compilation source snapshots and full compiler
logs, including failures. Both final attempt 07 logs report exit 0 with
`direnv exec . lake env lean Examples/ConstructionObservationAuthor{A,B}.lean`,
without output-file arguments. Lean was 4.35.0, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Final examples are imported by
`SquareApplications.lean`; failed attempts remain isolated experiment evidence.

The exposed identity was Codex based on GPT-6. Exact serving model revision,
effective reasoning and sampling configuration, tokens and pricing were
unavailable. Author A recorded 17:19:22–17:25:03 UTC on 2026-11-04. Author B
uses the conservative first timestamp 17:19:34 through 17:24:46 UTC, rather
than resetting the budget when its start file was written. Reporting is included
in those intervals. There were no later proof hints, nested agents or external
calls. Setup used separate copied caches; concurrent project work caused
uncontrolled host contention. Times are not causal speed comparisons.

## Preserved mathematics and theorem connections

Task A composes existing constructors as `cons a (double (cons b t))`. Its
length changes from n to n+2; it does not add a primitive or establish arbitrary
constructor-extension support. Both authors prove every coordinate equals
`Fin.cases a (Fin.cases (2*b) (fun k => 2*v k))` for arbitrary n, a, b and v.
Their direct proofs use native lifted equations, induction and coordinate cases.
Their shared proofs visibly invoke public `correct` with the same assumptions
and conclusion. Both use `substituted` to expand the vector leaf into complete
cons syntax. Empty-tail and [7,22,26] cases remain, as does index 1 = 22 for the
established `double (cons 7 (cons 11 nil))` client through public `correct`.

Task B keeps exact `parse` agreement at every word for arbitrary witness language
P. The observer has type `Decision (P []) × Decision (P ['a'])`; the two fibres
remain distinct. Direct proofs derive pair equality from the old relation and
use native `Quotient.lift`. Shared proofs discharge factorization through
`fun p w => p.parse w`, then invoke `compatible_of_factor`, `extend_iff`,
`descend` and `descend_mk`. Both routes prove extension/recovery and quotient
representative computation without assuming the desired compatibility.

The concrete nullable-star parser is `star (union epsilon (atom 'a'))`. Both
authors retain the exact empty-list decision and the singleton nonempty parse
with an atom witness. `WitnessTrie.lookup_unfold` connects the nonempty result
to native exact lookup at depth 1. Replacing only the old relation with Boolean
recognition breaks compatibility: public ambiguous epsilon alternatives agree
in recognition but select opposite Sum tags. First-component projection refutes
pair equality. This negative case does not weaken the successful exact task.

Statement review checked unrestricted coordinate/word quantifiers, indices,
pointwise equality, dependent result types, discharged premises and concrete
inhabitants. The vector target is independently specified by its coordinates;
the parser pair uses actual decisions rather than success bits. No new axioms
or admissions occur in successful sources. Failed elaborations' recovery
warnings are preserved and do not count as successful proofs.

## Author obligations and failures

Both clients import `Examples.IndexedCompositional`,
`Examples.ObservationExtension`, and `Applications.Languages.WitnessTrie`.
Local wrappers name the frame, exact setoid, pair observer, quotient functions
and concrete input/witness values. Author B also names the expected vector.
Neither required dependent casts, universe lifts, a new primitive signature,
or a library compatibility instance.

| Layer | Evidence from these trials |
|---|---|
| Mathematics | Induction on length, finite-coordinate cases, function/product extensionality and quotient well-definedness suffice. Boolean incompatibility is a genuine witness-information loss. |
| Interface concepts | Direct vectors expose lifted successor states; shared vectors consume all-term correctness. Shared parser proofs add meaning factorization and a commuting square; direct pair/quotient proofs are already short. Both substitution routes reuse the same public theorem. |
| Lean encoding | Both authors encountered ambiguous `Language` after imports. Qualifying `LanguageWitnesses.Language` resolved it. Author B assumed vector notation and `fin_cases` were available; core `Fin.cases` sufficed. |
| Author/tool use | Both attempted an ambient `python3` edit outside the shell, then corrected it with `direnv exec .`. Author B also corrected terminal reporting in its attempt harness; saved diagnostics were retained. |
| Documentation | Public examples already qualify witness `Language`. Source comments and theorem statements sufficed for both clients; these trials demonstrated no missing documentation prerequisite. |

Author A had two failed Lean attempts from the same unqualified name and one
unchanged successful recheck after its failed edit. Author B had three failed
Lean attempts: two from that name and one from notation/tactic assumptions.
These counts describe retained attempts, not independent measurements of an
interface. Earlier routes and public examples informed later ones; reversing
order does not remove exposure effects.

## Acceptance assessment and limits

The frozen matched tasks, independent authors, native contracts, prompts,
metadata limitations, attempts, failures, assistance records and focused
successful checks satisfy the experimental evidence portion of #279.
Full formal acceptance still requires the coordinator's candidate build/audit
and independent review. No bounded interface correction was justified by the
observed failures, so no interface revision or affected-task rerun is claimed.
The public library remains unchanged.

These two AI trials establish completion for the recorded tasks and conditions.
They do not establish human usability, a general model capability, a speed
advantage for either route, or usability for arbitrary constructor/observer
extensions. Continued architectural reassessment remains with #235/#36; a future
consumer exposing a contract mismatch should supply a scoped retrofit and
recovery requirements, freeze the changed interface, and rerun affected tasks.
