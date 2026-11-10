# Policy-directed realization choice

Issue #436, implementation baseline `ab51385a10d1936b55e48f18d791b3cfe2af91e1`.
The [PetaBricks assessment](petabricks-architecture.md) supplies motivation.
This record distinguishes implemented contracts, measured runtime evidence and pending acceptance.

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
context on both the epoch and each observation, positive equal repetition
counts, unique candidate IDs, and one successful observation at each
candidate/repetition pair. Missing, duplicate,
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

Focused development checks have passed for `Examples.PolicyChoiceDriver` and
its dependency closure using the Nix shell, restricted to CPUs 0 and 1. The nine
runtime tests pass, including the regression that rejects an observation whose
context differs from the current request. Controlled empirical evidence is recorded below. Full candidate build/audit
and final review reconciliation remain pending. The public entrypoint imports the examples and
their modules.

## Executable caller and evidence files

Build and exercise the runtime interface through the development shell:

```sh
direnv exec . lake build Examples.PolicyChoiceDriver
direnv exec . python3 scripts/test-choice-driver.py
```

`scripts/choice-driver.lean` exposes a bounded JSONL session. `select` returns
its exact context and candidate IDs; `record` applies the shared immutable
update; `run` executes the selected realization; `explore` explicitly executes
an admitted named realization. Those modes read no clock. A syntactically
malformed request returns an error; a well-formed but incomplete or stale
epoch falls back to the fixed policy. Selection does not execute unchosen
alternatives. The returned epoch must be sent back to use the observations.

The runtime tests exercise complete and incomplete saved epochs, failed and
duplicate observations, changed implementation/target/workload/site/protocol,
model constraints, empty admission, ties, parsing failures and continued
service. Synthetic observations change both clients' selections. Clock-free
smoke runs execute both tree strategies on 17/65-node star, chain and branching
fixtures and scan recipes with 16/64/256 elements. Every driver execution
compares the complete output with the independent specification; tests also
check concrete expected prefix and LCA outputs. No benchmark result follows
from those checks.

`sample` is explicit bounded exploration. It requires a declared target and
`CONALED_CHOICE_IMPLEMENTATION`. The actual empirical harness computes a source
hash including Lean sources, toolchain/dependency configuration and the runner,
sets that identity, and checks it again after measurement. The driver also
records its Lean version. Workload keys contain every fixture-generation
parameter. Scan scopes retain the enclosing frames and constraints; tree
scopes retain the composite resource requirements. Candidate lists retain
order, and imported evidence is checked against the current admitted list.
Context equality is a consistency check on declared metadata, not proof that
a physical host or a reported clock behaved as claimed.

To reproduce the controlled measurement protocol, run:

```sh
direnv exec . python3 scripts/benchmark-choice.py /tmp/choice-results --repetitions 5
```

The driver target is **Lean's `--run` evaluator**, using the actual library
realizations. The initial assessment proposed a compiled CPU executable;
this bounded implementation instead uses the repository's existing driver
pattern and names that target explicitly. The results will not establish
performance of a standalone native executable or hardware scan circuit.
The persistent process receives one untimed warmup per candidate and rotated
exploration order. A fresh prepared state is constructed for each tree sample.
The harness saves complete epochs, reloads them, and compares fixed and
trained selections in alternating order. It reports a policy that loses as
well as one that wins; performance improvement is not assumed.

## Timing boundaries and overhead

The phase timer receives a thunk and invokes it after reading the start clock.
This matters in an eager language: passing an already computed value to an
IO timer would measure only its return. Timers are disabled in runtime tests.

`sample.elapsedNs` is the sum of input/output conversion, preparation and
query/kernel phase durations. Scan input loading and output flattening are
conversion; tree conversion constructs the Euler maps, preparation builds the
chosen backend, and queries include encoding and decoding. Every candidate
has the same positive repetition count before totals are compared. Fixed
policies use catalog order for scan and modeled total preparation/query cost
for prepared service. Neither model score is mixed with measured nanoseconds.

`featureNs` covers constructing the job, fixture/context and current admission
list. `selectionNs` includes evidence validation, ranking and selection.
`validationNs` measures full output checking separately. `endToEndNs` starts
before job construction and ends after execution and validation. It includes
selection, feature extraction, timer/dispatch overhead and fixture generation.
`otherNs` is the residual after the named phases; it combines fixture/query
list generation, coordination and instrumentation overhead. A separate
`instrumentationProbeNs` reports six empty timed phases and is never subtracted
from candidate timings. It is a diagnostic, not an exact correction for noise.

The end-to-end clock excludes JSON parsing/rendering, pipe IO, and process
startup. `requestWallNs` in the Python harness includes request serialization,
server parsing/rendering, pipe transport and the driver call. The report records
process startup plus its initial handshake separately. Evidence serialization,
file write and reload have their own duration; `trainingTotalWallNs` includes
initial selection, warmups, all exploration, update requests and persistence.
Both internal end-to-end and request-wall comparison totals are retained.
The final report-file write is not part of those comparisons. Resource
requirements constrain the selected realization's declared model profile;
they do not certify the physical driver or selection overhead against a deadline.

## Author assessment and remaining work

Adding a scan realization means supplying its recipe or `Scanner` law and the
appropriate shape/context admission. The plan's existing correctness proof is
reused after selection. Adding a prepared realization means supplying its
representation, operations, validity, laws and optional resource bounds; the
choice and tree-reduction proofs then reuse those laws. Existing direct APIs
remain available. A fixed policy is a score function. An observation-informed
policy uses the same choice interface with a validated epoch; it does not
require another client semantic proof. These are demonstrated code paths,
not a measured productivity comparison or a claim about human author effort.

The bounded interpreter/compiler route was assessed and was not implemented.
Current scan callers already have `Frame`/`plug` and scanner composition;
prepared callers have a separate preparation/query lifecycle with dependent
state. A shared new AST would add encoding obligations without a demonstrated
consumer benefit in this milestone. Stable choices can later be specialized
before an existing compiler's primitive interpretation. This report records
no invented interpreter authoring or compiler-performance measurements.

Approximation needs checked error-budget composition beyond the generic
contract predicate. Parallel scheduling needs dependency/effect legality.
Additional layouts need conversion and storage contracts. Stateful replacement
needs a source-linked state correspondence and transfer operation. Unrestricted
recursive switching needs a shared progress argument. Current finite nested
composition and immutable sessions do not supply those capabilities.

Controlled empirical results are recorded below. Full committed-candidate
build/audit, final Standards/Spec review and originator review remain pending.
The coordinator retains their scheduling and review record. No #108 trial
material was used in this work.

## Measured execution on 2026-11-10

The preserved [raw report](../../experiments/policy-choice-measurements/2026-11-10/report.json) records seven workloads at source commit `6a64bf059ad25bb0590dc4498f383be15a597e03` and source hash `d42c35116d14b9eed26dc5660de5b9f15cd49921be4caaff75239a998b614112`. The nine runtime tests passed before measurement. The run used Lean 4.35.0 `--run` on the recorded Linux x86-64 host, pinned to CPUs 0 and 1. Competing orchestration builds were excluded using the shared build lock; ordinary desktop activity was not disabled. Each candidate received one warmup and five measured training repetitions in rotated order. Five subsequent comparisons per policy used alternating order. Full output checks succeeded throughout; each saved epoch was reloaded and accepted.

Times below are arithmetic means in milliseconds for the five comparison calls. End-to-end includes the named driver phases; request wall time additionally includes transport and serialization. Training is the entire training/persistence interval for that workload. These are observations from one run, without confidence intervals or a general speedup claim.

| Workload | Fixed → trained choice | Fixed / trained end-to-end ms | Fixed / trained request wall ms | Training ms |
|---|---|---:|---:|---:|
| scan nested | same recipe | 0.234 / 0.313 | 0.289 / 0.466 | 7.766 |
| scan powers 2^6 | changed recipe | 4.815 / 4.785 | 4.893 / 4.972 | 109.577 |
| scan powers 2^8 | changed recipe | 53.132 / 52.535 | 53.279 / 52.811 | 1201.576 |
| star tree, 17 nodes / 1 queries | direct → direct | 5.762 / 5.862 | 5.848 / 6.053 | 137.141 |
| star tree, 17 nodes / 1024 queries | sparse → sparse | 42.029 / 42.072 | 42.294 / 42.440 | 732.271 |
| chain tree, 65 nodes / 32 queries | sparse → direct | 25.629 / 24.857 | 25.763 / 25.115 | 539.660 |
| branching tree, 65 nodes / 1024 queries | sparse → sparse | 212.547 / 212.416 | 212.864 / 212.827 | 3443.444 |

Training changed both power-scan choices and selected direct interval scanning instead of sparse preparation for the 65-node/32-query chain. The nested scan and both star workloads were slower with trained evidence in this run. For the 64-element scan, the small internal end-to-end reduction did not survive request-wall accounting. Cases choosing the same realization still differ because evidence validation and measurement noise remain. The five comparison calls did not repay training costs for any workload; this run does not establish amortized benefit.

Feature construction and repeated admission/selection work dominate several small kernels. For the 256-element scan, fixed-policy feature and selection means were 17.024 ms and 34.157 ms, versus 53.132 ms total end-to-end. The trained means were 17.010 ms and 34.325 ms. The measured selector therefore needs workload-aware amortization or cheaper repeated admission before it can be presented as a low-overhead runtime facility. That is an engineering follow-up, not a failure of policy-independent semantic preservation.

Startup and initial handshake took 1228.229 ms, separately from all workload totals. Raw responses retain conversion, preparation, kernel/query, validation, feature, selection, residual and instrumentation-probe durations. The empty-phase probe is diagnostic and was not subtracted. The full report also retains persistence and training costs, successful outputs, and each complete epoch. No native-code, hardware-parallel, optimality or human-productivity claim follows from these measurements.

The measurements close the empirical-evidence gap in the earlier checkpoint. Exact-candidate build/audit, independent Standards/Spec reconciliation and the assigned originator review remain acceptance obligations.
