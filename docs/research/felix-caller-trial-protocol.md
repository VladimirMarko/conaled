# Matched categorical caller trial (#25)

This protocol fixes the experiment before independent authors start. The three
contracts below are shared by both routes. Completion evaluates the evidence;
it does not require a favorable Lean result. Production interfaces stay at their
pinned revisions during the trial.

## Baselines and author access

Lean: `3c064b11a5812e38c317601473e6897f65ce2a32`, including completed #8 and #24.
This advances #25's original baseline; conclusions concern this revision.
Use its `lean-toolchain`, `lake-manifest.json`, `flake.nix` and `flake.lock`.
Felix: `6f36d28097db7ea5f5df3263db3e8be08f74e490`. Use that checkout's flake
and lock, Agda library declaration and source. The environment manifest records
compiler versions and lock hashes before author starts. See
[environment.json](../../experiments/felix-caller-comparison/environment.json) and
[launch.json](../../experiments/felix-caller-comparison/launch.json). Both manifests
and the linked exact prompts must be committed and reviewed before launch.

Assign one fresh-context agent to each route with the same model configuration
and tool capabilities. Authors receive this complete protocol, the route's
checkout/environment paths and the same neutral reporting instructions. They
receive no coordinator solution code or conversation history. Record agent IDs,
start/end times and prompt text. This is one attempt per route, not a population
estimate of human or agent productivity.

Authors may read all public source, examples and documentation at their route's
pin, including the pinned dependencies, and use local search and compiler tools.
Existing examples may be adapted with attribution and costs recorded. They may
not read the other author's trial or obtain task-specific external assistance.
The coordinator may repair environment access, logging or missing pinned files;
each intervention is logged. Mathematical or API coaching ends the independent
attempt, and any subsequent work is labeled post-trial repair.

## Common mathematical contract

Use natural-number matrices with finite dimensions. Write `V n = Fin n → Nat`.
The raw source has objects natural dimensions, arrows `n → m` represented by
`m`-by-`n` matrices, matrix identity/composition, zero-dimensional terminal
object and product dimension `n + m`. Interpret a matrix by its action on
coordinate vectors using finite sums. Semantic equivalence is pointwise equality
of this action; entry equality need not be recovered.

The intermediate category also has dimension objects and arrows arbitrary
functions `V n → V m`, with equality pointwise. Its chosen product has dimension
`n + m`. The final category has types and functions with ordinary pair products.
The dimension-to-type interpretation sends `n` to `V n`; its product comparison
splits and joins coordinates. Show both inverse laws and the applicable product
preservation laws. Product preservation must use this comparison, not replace
coordinate vectors by pairs to make preservation definitional. Function
extensionality may be used in Lean; Agda may retain pointwise setoid equality.
Record this encoding difference rather than postulating Agda extensionality.

1. **Interpretation and transported laws.** Define the raw matrix operations and
   the matrix-to-coordinate interpretation. Supply local operation preservation
   and obtain category and cartesian laws under induced semantic equivalence
   through library law transport. Establish the dimension-to-type map with its
   non-strict product comparison. Distinguish local arithmetic/coordinate facts
   from general laws inherited from the library.
2. **Composition.** Reuse those two packages to form the matrix-to-type composite,
   its product comparison and preservation results. Demonstrate its action on
   arbitrary matrices/vectors and its product observations. Charge setup from
   task 1 once; identify any new proofs or repackaging task 2 actually requires.
3. **General comma caller.** Use matrix source and type/function source with
   their interpretations into the common type/function category. For every
   dimension, the comma object's connector is coordinatewise doubling,
   `x ↦ 2*x`. Construct squares for two-dimensional shear
   `L(x,y) = (x+y,y)` and swap `R(x,y) = (y,x)` with their matrix implementations.
   Prove commutation for all inputs. Compose `R` after `L` through public comma
   operations and obtain its semantic statement through public projections.
   Check `(1,2) ↦ (2,3)` and reverse composition `(1,2) ↦ (3,1)` so order matters.
   Exercise comma products and their projections for arbitrary dimension-indexed
   objects under the corresponding preservation assumptions. Keep the two source
   families distinct and the doubling connector nonidentity. A function-only
   specialization or identity connector does not satisfy this task.

Equivalent finite-index encodings are allowed if their conversion is disclosed
and the full contract is retained. If a required library capability is absent,
record the precise obstruction and smallest reproducer. Helpers implementing
missing generic infrastructure count as new caller work; they do not retroactively
become baseline capabilities. Do not weaken a contract to obtain a passing file.

## Budget, stopping and evidence

Each route receives at most 60 compiler-feedback rounds and 180 minutes of
active elapsed time across all three tasks. A round is an actual checker
invocation over a frozen trial-source snapshot. Nested calls in scripts or editor
tooling count individually; one multi-file build of one unchanged snapshot is one
round. Record each snapshot hash, command, start/end timestamps and exit status.
Active elapsed time starts when the author receives the task and is wall time
minus explicitly logged, non-overlapping dependency-provisioning or coordinator
build-lock waiting intervals during which the author does no other task work.
Ordinary reading, thinking, source editing and checker execution count.
At the first budget boundary freeze source immediately. An already-running check
may finish and its result is retained, but no further author edits or feedback
rounds follow. Coordinator reproduction and required audits of that frozen source
are recorded separately and cannot provide more author repair opportunities.
Read/search commands are unrestricted within the time cap. This is a prospective
effort cap, not a quality score.

Proceed in task order, retaining partial attempts. Stop when all contracts check,
either budget is exhausted, or a concrete unsupported capability prevents further
independent progress. Record which tasks were reached. Task dependencies make
failure to reach a later task censored evidence, not proof that it is unsupported.
The coordinator must not extend a route's budget after seeing its outcome.

Keep an append-only command/feedback log, source snapshots at the first compiler
attempt for each task, final source, and diagnostics. Record all helpers and their
provenance, discovered API requirements, failed approaches and repairs. Report
first-attempt and final checked status separately. No admissions, new axioms or
unchecked placeholders count as a completed proof. Preserve failures and exclude
post-trial repairs from independent-attempt measurements.

## Evaluation and validation

For each task compare mathematical scope, assumptions/equality, caller concepts,
local proof obligations, inherited proofs, composition work and representation
locality. Identify which declarations change if the coordinate encoding changes;
support that assessment with actual dependencies. Inventory one-time setup and
incremental caller work separately, including all adapted helpers. Lines may be
reported as descriptive evidence, never as a weighted elegance score.

Check successful artifacts under their pinned compilers. Lean additions require
statement review and the repository's applicable build/proof audit; distinguish
experiment modules from integrated production modules. Agda checks must ignore
old interfaces for the final reproduction and retain the explicit flags. Preserve
compiler/library identities, exact commands, source hashes and outcomes. Independent
Standards and Spec review assess the final evidence and all conclusions. A frozen
protocol does not itself establish any comparison result.

Conclude per task: supported on the examined dimensions, concrete gap, or
insufficient evidence. Create scoped follow-ups for demonstrated gaps, checking
existing owners first. This sample does not establish library-wide elegance or
capability parity. The full-section author experiment under #235 and Agda-like
surface comparison under #117 are separate work.
