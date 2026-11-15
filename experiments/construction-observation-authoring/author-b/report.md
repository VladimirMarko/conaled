# Author B trial report

Completed both tasks and all four routes, in order B-shared, B-direct,
A-shared, A-direct. Final source is `Examples/ConstructionObservationAuthorB.lean`.
The final complete file checked with exit 0 in attempt 07. No admissions,
new axioms, library changes, import-root changes, or commits were made.
The coordinator owns the integrated build and exhaustive proof audit; this
trial performed the requested direct Lean validation without output files.

## Timing, environment, and assistance

The earliest recorded timestamp is 2026-11-04T17:19:34Z, from the initial
public-document read command. Use that as the conservative trial start.
`start.txt` was written at 17:19:45Z after initial reading; it is not a later
budget reset. The final compiler completed at 17:23:14Z. `end.txt` records
completion of reporting. The budget was 15 minutes or completion.

Frozen checkout HEAD: `21eaedeed1c78f58437b05a0197b12bcc386c9bb`.
Protocol interface revision: `5e5b039`. Compiler output:
`Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.
The assigned checkout used its prepared cache and `direnv exec .` flake shell.

The exposed developer identity says Codex based on GPT-6. No exact serving
model revision, effective reasoning setting, sampling configuration, token
counts, or pricing was exposed. Configuration was inherited without overrides.
No nested agents or external calls were used. Assistance consisted only of
the coordinator's initial assignment, route order, isolation constraints,
and notice that public dependencies were already built. There were no proof
hints or subsequent interventions. No other author files, private solutions,
or coordination records were read.

The example-driven-development skill supplied statement-review criteria;
no-ai-slop supplied prose guidance. This was an assigned trial within the
coordinator's existing implementation loop, so no new review loop was started.

## Attempts and diagnostics

Each numbered `.lean` is a source snapshot taken before compiling. Its matching
`.log` retains the full compiler output, exact command, UTC start/end, and exit
status. `check-attempt.sh` generated these records.

| Attempt | Route | Result |
| --- | --- | --- |
| 01 | B-shared core | Failed: ambiguous `Language`, followed by cascading unknown declarations. |
| 02 | B-shared core | Same source/failure; intended edit did not run because bare `python3` was unavailable. |
| 03 | B-shared and parser instances/counterexample | Passed after qualifying `LanguageWitnesses.Language`. |
| 04 | B-direct | Passed, retaining the checked shared route. |
| 05 | A-shared | Failed: unavailable vector notation and `fin_cases` tactic. |
| 06 | A-shared | Passed after expressing the three coordinates through `Fin.cases`. |
| 07 | A-direct and complete file | Passed. |

The bare-Python failure was a shell-use mistake by the author, not a Lean or
mathematical failure. Subsequent editing commands used `direnv exec . python3`.
The initial harness used a brace group with `exit`, so attempts 01/02 did not
print the saved log back to the terminal. Their complete logs were saved and
read before fixes. A subshell fixed terminal reporting for later attempts.
A read-only glob search for `Applications/Languages/Trie*.lean` found no files;
repository search located `WitnessTrie.lean`.

## Task B and statement review

`old P` quantifies over all words, with exact `Decision (P w)` equality.
`pairObservation` has the product of the two distinct result types
`Decision (P [])` and `Decision (P ['a'])`. It does not erase to a Boolean or
compare witnesses across different words.

The shared proof factors through `fun p w => p.parse w`. Function
extensionality proves its compatibility from the old contract; the semantic
pair projection commutes by reduction. It then uses the requested
`compatible_of_factor`, `extend_iff`, `descend`, and `descend_mk` results.
No compatibility premise is assumed.

The direct proof uses the old hypothesis at the two words and `Prod.ext`.
Extension/recovery is the two directions of the conjunction, and native
`Quotient.lift` consumes the derived compatibility. Its representative law is
reduction. This route does not use shared extension/descent/factor helpers.

Both quotient routes are instantiated with `star (union epsilon (atom 'a'))`.
The empty decision is `yes` with the native empty parse list. The nonempty
decision is `yes` with a singleton parsed word carrying `Sum.inr` atom evidence.
The nonempty observation is also connected to the bounded trie using
`WitnessTrie.lookup_unfold` at depth 1, with its length premise proved by
`decide`. Thus actual decisions, rather than only success bits, are retained.

The existing ambiguous epsilon alternatives agree under public `recognition`
by `old_agreement`. Their first components differ by `selected_different`.
Projecting a hypothetical pair equality with `Prod.fst` contradicts this.
The failed law is precisely `Compatible recognition pairObservation`, meaning
recognition agreement would have to imply equality of the selected pair.
The successful exact contract is unchanged. These are usable instances;
neither route relies on an impossible old relation or a circular hypothesis.

## Task A and statement review

`frame` is a compound client of the existing cons/double signature, not support
for adding an arbitrary primitive. Its length is exactly n+2. `expected`
is independently the vector with head a, next coordinate 2*b, and remaining
coordinates 2*v. The universal theorems quantify over n, a, b, v and every
`Fin (n+2)` coordinate without restricting n to positive lengths.

The shared proof explicitly rewrites by the public all-term `correct` theorem,
then checks the head, second coordinate and tail by `Fin.cases`. The direct
proof develops leaf, cons, and double observer equations. Leaf and double
use induction on length; double's recursive step follows the native lifted
transition. The final direct client proof uses only those equations and
coordinate cases. It does not use `correct`, `read_morphism`, `fold_morphism`,
or the observation bridge.

Both routes use public `substituted` to replace the leaf by its complete
`expand` syntax under `Term.bind`, preserving every expected coordinate.
Each retains the empty-tail case, the nonempty vector [7,22,26], and its
expanded version. The established double(cons 7(cons 11 nil)) result at index
1 is recovered through public `correct`, independently of the direct route.
The empty length uses `Fin.elim0`; no missing coordinates or head-only
agreement are hidden by the statements.

## Imports, obligations, and interpretation

Explicit imports are `Examples.ObservationExtension`,
`Applications.Languages.WitnessTrie`, and `Examples.IndexedCompositional`.
The first supplies the shared interface and the requested ambiguous parsers;
the second supplies exact trie lookup; the third supplies the vector interface.
No additional tactic imports were added.

Local wrappers are the old setoid, pair observer, two quotient functions,
nullable parser/witness, compound frame, and independent expected vector.
No equality transports or casts were needed. The parser shared route requires
learning factorization through a dependent function, `Compatible`, and quotient
representative computation. The direct route requires setoid relations,
product extensionality, and the `Quotient.lift` well-definedness obligation.
The vector shared route consumes all-term correctness and evaluates its
meaning. The direct route requires understanding `rule.lift` transitions and
induction at the shrinking vector index. Both substitution routes consume the
same public preservation result.

The namespace ambiguity is Lean name resolution exposed by these imports,
with an author omission of qualification. The failed notation/tactic attempt
was an author assumption about available imports; core case analysis sufficed.
There was no mathematical obstruction and no demonstrated expressiveness
limitation. Public source comments and theorem statements were sufficient for
these clients. This record does not establish human usability, causal speed
advantages, or general model capability. Earlier routes and public examples
informed later routes as permitted by the counterbalanced protocol.
