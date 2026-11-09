# Policy-directed realization choice

Issue #436, implementation baseline `ab51385a10d1936b55e48f18d791b3cfe2af91e1`.
The [PetaBricks assessment](petabricks-architecture.md) supplies motivation.
This record distinguishes implemented contracts from pending runtime evidence.

The direct library route now supplies finite admission before ranking,
context-checked offline evidence, and selection inside existing composites.
`Optimization.Choice.select` reuses `Thinning.argmin`; `Prepared.select`
is its definitionally equivalent resource-profile specialization. Existing
Prepared operations, contracts and first-occurrence tie behavior remain usable.
`select_map` reuses `argmin_map` and retains the entire selected witness.
`selected_contract` and `choose_contract` accept an arbitrary candidate
predicate. The checked allowed-output example admits distinct results 10 and
12; no equality between realizations is assumed by the common construction.

Evidence collection is explicit. `Epoch.record` adds a successful observation
without mutating the old epoch. `complete` also checks imported epochs: exact
context, positive equal repetition counts, unique candidate IDs, and one
successful observation at each candidate/repetition pair. Missing, duplicate,
failed or stale observations cause the whole policy to use its fixed score.
Current admission is checked again, and an empty admitted catalog returns
`none`. A complete epoch ranks by total recorded duration over equal numbers
of repetitions. Clock accuracy and future speed are not proved by this law.

`Applications/Parallel/PolicyChoice.lean` selects a local recipe in a known
finite `ScanSearch` context. It checks the size and optional circuit-depth
limit of the completed context. Correctness follows from `ScanPlan.correct`,
which already constructs product and composition proofs using `Scanner`.
The common-list input adapter has a checked flattening law; shaped callers
continue to use `Scanner.run` directly. Recipe/context identity and model
constraints are included in evidence validity. Empirical policy selection uses
the declared unpruned catalog: circuit dominance does not imply runtime
ranking dominance.

`Applications/Sequences/LCA/PolicyChoice.lean` uses the actual direct interval
scan and sparse-table realizations. Selection precedes preparation; dependent
state stays with that strategy for the whole service. `chooseTree` places
backend choice inside `TreeReduction`, checking the composite profile,
including conversion and retained decoder storage. Existing prepared
reduction, query-list and resource laws supply whole-tree correctness and
modeled query bounds. Policy updates affect subsequent sessions, not existing
state. The shared-block strategy remains available through the old interface;
this experiment does not need its enormous symbolic winning-size examples.

The checked clients in `Examples/PolicyChoiceClients.lean` demonstrate an
explicit synthetic update changing each client's selection, the nested scan
counterexample where a locally tied plan fails the enclosing depth limit,
a noncommutative monoid specialization, and the tree caller. Synthetic records
are labeled and are not performance observations.

Statement review: selection membership and admission retain the original
candidate/request; ranking is absent from the semantic-law assumptions.
The scan result is quantified over every monoid and every input of the
requested size. The model-depth conclusion describes the complete enclosing
recipe. Prepared query correctness holds for every query from the chosen
valid state, and reduction bounds include its translation. These laws establish
neither arbitrary algorithm interleaving nor a physical deadline. Finite
catalog/context traversals and total selected operations provide progress.

A bounded scan interpreter could name and resolve multiple sites, but the
current caller already supplies `Frame`/`plug`, scanner composition, and exact
selected-witness transport. Prepared service additionally needs a staged,
dependent representation. Adding a common AST would impose those encodings
on both authors without removing a demonstrated obligation. The interpreter
route is assessed here and has not been implemented or author-timed. Existing
compiler targets can consume a selected certified operation; their soundness
laws do not automatically establish tuner correctness.

Focused development checks have passed for `Examples.PolicyChoiceClients` and
its dependency closure using the Nix shell, restricted to CPUs 0 and 1.
Full candidate build/audit, independent review, runtime driver tests and
controlled empirical evidence remain pending at this milestone. No performance
claim is made. The public entrypoint imports the new examples and their modules.
