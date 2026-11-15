# Independent review of staged resource models

Reviewer: `reuse_survey`, 2026-11-02.
Scope: bounded cross-cutting preparation only, outside the integrated library.
This is not a chapter Standards/Spec gate, integrated proof audit, or chapter
acceptance. Read `../source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` for the full
source obligations that remain beyond these drafts.

Each draft is reviewed only after its owner completes the focused Lean check
and freezes the source. Successful focused validation is reused at the exact
source hash; this review does not rerun an unchanged expensive check.

The initial model reviews below are retained as history. The later
**Checked resource-interface follow-up** section records the current frozen
source hashes and discharges the initially proposed, uncompiled resource
adapters. Both current drafts have no unresolved findings within this scope.

## Unary comparison — initial model review, no unresolved findings

File: `../staging/unary-costs/UnaryComparisonCosts.lean`.
Initial reviewed source SHA-256:
`71f6b20983629b7020be14e836755ad1d201f96b1fb6051669dfba7da6025429`.
Owner: `environment`. Owner reported final one-thread pinned Lean 4.35.0 check
exit 0, with the exact command and input identities in `VALIDATION.md`. The
reviewer inspected that record, successful output and the source; the file
hash matched this initial snapshot. The four reported principal theorems
depended only on `propext`.

### Mathematical statement and model review

- `unaryLE` is an explicit terminating lockstep less-than-or-equal recursion.
  `unaryLERun` follows the same branches and recursive call, incrementing the
  observation once per pair-pattern call, including the terminal call.
- `unaryLERun_erases` connects the actual instrumented recursion to the
  unmeasured one. `unaryLE_eq_decide` independently identifies its Boolean
  result with mathematical `n ≤ m`. Neither theorem merely assumes the
  desired answer or substitutes an unrelated cost recurrence.
- `unaryLERun_steps` proves `min n m + 1` for every pair, with correct zero and
  successor cases. The stated count does not include arithmetic bookkeeping,
  allocator work, primitive execution costs, or proof checking.
- `no_difference_only_bound` quantifies over every `bound : Nat → Nat` and
  uses `(n-m)+(m-n)`, the absolute difference for natural operands. The equal
  witness `n=m=bound 0` has count `bound 0+1` and difference zero, contradicting
  the proposed finite bound. It therefore refutes arbitrary finite
  difference-only bounds, not merely the formula proportional to a difference.
- `equal_inputs_beyond_threshold` supplies real equal-input witnesses above
  each supplied threshold and budget. No impossible invariant or bounded
  domain makes the counterexample vacuous.
- The zero-left, zero-right, equal, strictly-less and strictly-greater examples
  use the public pair specification. The large-equal cases use the general
  equal-input theorem and explicitly connect it to zero operand difference.

### Source qualification and reuse

The reviewer read the exact passages `Extract.v:65–66`,
`SearchTree.v:1290–1292`, and the displayed equality recursion in
`Trie.v:106–111`. The draft appropriately treats its theorem as a structural
model for the displayed unary `≤` recursion. It does not silently equate that
model with a particular strict Coq comparator or native Lean `Nat` execution.
Those source-specific bridges and broader chapter coverage remain open.

Using `Bool × Nat` was a documented staging accommodation for the unavailable
compiled `Resources.Measured` import. It is exactly that existing interface's
underlying type; the proposed `erasureSquare` adapter was explicitly uncompiled
at this initial review. The checked follow-up below resolves that limitation.
No competing generic resource framework was introduced.

Disposition: **no unresolved finding within this staging scope**. This permits
preserving/reusing the draft; it does not establish full chapter acceptance.

## Queue peek — initial model review, no unresolved findings

File: `../staging/queue-costs/QueuePeekCost.lean`.
Initial reviewed source SHA-256:
`9266dae6612db42d811f798ca012ae45688fbc438b7cc75113ac01eaf20e078f`.
Initial reviewed README SHA-256:
`8dfc66e98c400c4f45ba70a1a8933bd42c93d7f0d324194cf9a1d12a3b2faff2`.
Owner: `vfa_scope`. Owner reported final exact-byte one-thread pinned Lean
4.35.0 check exit 0 and no diagnostics, then froze the files. The reviewer
inspected the complete source, explanation and `VALIDATION.md`; the hashes
matched those supplied for the initial snapshot. No further compiler was
launched during review.

### Operational model and source correspondence

The reviewer checked the original ADT `TwoListQueueAbs` declarations, including
its cons-to-back enqueue and observing-only peek. The current chapter bytes
match SHA-256
`87d7ca279b38d22f31ff56bf9f2b11103b382c325969a269bc542de27e4a8fe2`.
The [official Rocq 9.0 List documentation](https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Lists.List.html)
was independently opened during review: direct `rev` recursively reverses the
tail and appends the head; a separate accumulator variant is also documented.

- The declared observation counts nonempty constructor visits in that direct
  reverse and its recursive append. It explicitly omits nil tests, dispatch,
  head reads, pair construction and enqueue. Zero observation in the empty or
  nonempty-front branch is therefore coherent and is not called zero runtime.
- `appendMeasured_value` and `reverseMeasured_value` establish value erasure;
  the cost recurrence is then derived from actual measured recursive calls.
  It charges append's visited first argument as well as the reverse input node.
- `peekMeasured_value` and `peekMeasured_relate` link the instrumented observer
  to both the source-style peek and the independent denoted queue head. The
  state adapter keeps the original pair, not a hidden normalized copy.
- `peekReversalInputBound` depends only on the representation. Its proved
  lower bound is back length for empty front. The counterexample does not
  assume the desired count formula or rely on a claimed quadratic closed form.

### Reachability, quantifiers and nonvacuity

- `enqueueCopies_reachable` constructs each witness from empty using the
  actual supplied enqueue transition; `enqueueCopies_shape` proves the empty
  front and arbitrarily long back. These are valid source-created states.
- `runPeeks` threads the output of the actual `peekStep` at every iteration.
  Unchanged state and `repetitions * perPeekCost` are derived theorems about
  that executor, not definitions substituted for an unrelated execution.
- `peek_potential_iff` correctly cancels the same state-only natural potential
  at both endpoints. `no_uniform_local_charge` chooses a reachable back of
  length `charge+1`, defeating the proposed charge for every such potential.
- `runPeeks_potential_iff` retains both boundary potentials before cancellation.
  `repeated_peeks_exhaust_initial_credit` separately handles a bound that
  discards the final potential: for the chosen fixed queue it uses
  `potential(q)+1` observations. The established lower bound exceeds the
  entire supplied initial credit plus `charge * repetitions`. The repetition
  count is strictly positive, and the argument also handles charge zero.
- Explicit default and payload parameters provide inhabited witnesses without
  imposing an unnecessary equality or order assumption on payloads. No
  unreachable invariant or impossible hypothesis supports the negative result.

### Examples, reuse and scope

The enqueue-4/9/2 example has the correct reversed storage, head 4, six counted
visits and eighteen visits for three repetitions. Empty/front-present branch
examples expose the chosen observation boundary. The back-length-potential
client directly specializes `no_uniform_local_charge`; the stored-credit case
exercises cancellation without pretending that initial credit was absent.

The initial draft used the exact pair and potential-inequality shapes of
`Resources.Measured`, `run_potential`, `run_constant_charge`, and `run_cost_le`.
Its small `runPeeks` recurrence was documented as a staging accommodation; the
initial README named the precise uncompiled adapter to existing `Resources.run`
and recommended eliminating the local executor at integration if appropriate.
The checked follow-up below resolves that adapter limitation. No competing
framework or native execution theorem was asserted.

The mathematical conclusion concerns the explicitly charged observing API.
It does not transfer unchanged to dequeue, a normalizing/caching observer,
another state space, memoized evaluation, native Lean reversal, compiler
output, physical allocation or elapsed time. The draft and explanation keep
those limits explicit, and do not claim that value equality transports cost.

Disposition: **no unresolved finding within the initial staging scope**. Full
queue implementation, source-coverage integration, exhaustive proof audit and
official chapter review remain separate. Resource adapters were initially
pending and are now reviewed below.

## Checked resource-interface follow-up — no unresolved findings

Date: 2026-11-02. This follow-up was independently reviewed only after each
owner reported the successful focused check and froze its files. It reviews
the added adapters, complete updated interfaces and assumptions, and current
README/validation claims. It retains the preceding independent analysis of
the original models, source qualifications, reachability and counterexamples.

### Exact current inputs and evidence

| Draft artifact | SHA-256 independently verified during this follow-up |
| --- | --- |
| `unary-costs/UnaryComparisonCosts.lean` | `997aa73ce69fe65712ba97a1217909a6f7af8c2d00e7e2978a4ca03a18c01c13` |
| `unary-costs/README.md` | `e676d55a1faa402bb70874e22fad817670eadce19512489b5d9e2d8610aeb853` |
| `unary-costs/VALIDATION.md` | `a6fe8da6252444051885dd7fa4157348ad8133dd52feb7a584149235ac69c896` |
| `unary-costs/resources-adapter-validation.txt` | `24fa8f8c6b65e664747f88d6da77413252d9b9d709699c9b203e9acfeaff3355` |
| `queue-costs/QueuePeekCost.lean` | `41486ba378124a2d459a74bd8199655e40a4c521e20abb75b9e5580671161df0` |
| `queue-costs/README.md` | `294235c2ae5454fd513bdce8a3b2e9c6764886d090227dfc36a6520cf670d5fe` |
| `queue-costs/VALIDATION.md` | `700ea4392b5a643fd6cfd103fa5be704317f1ac9aadd78e67f048e616394978a` |

Paths in that table are relative to `../staging/`. The unary owner records
exit 0 with no warnings/errors; its nonempty successful log contains the eight
explicit axiom reports. The queue owner records exit 0 with no diagnostics.
Both exact commands, pinned toolchain details, and historical unsuccessful
checks remain in the respective validation records. This reviewer did not
rerun any compiler or build, modify main source, or write caches.

The actual existing interfaces were read independently, not inferred only from
the owners' descriptions. Their current source hashes match the environment
record:

| Existing conaled module | SHA-256 |
| --- | --- |
| `Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `Applications/Resources/Workload.lean` | `5db2ef8f7a504b33b4dfbb26ed39de1a194fa59568ba16702f3ba2359b46b4f5` |
| `Applications/Resources/Potential.lean` | `680ea6df1c0271094a93b089a6fa2e7e8826a4da12937889ed5ecff8fc59cabe` |

The environment agent's authorized build of these existing targets is recorded
as successful; its build-log hash was independently verified as
`b9fc8b0ea81d69614dc659c211dd382043c3f85b1be09fe5a0b336dec76ba375`.
This is dependency availability for the focused adapter checks, not an
independent full-project acceptance result.

### Unary adapter review

`unaryLERun` now names `Resources.Measured Bool Nat`, which is definitionally
the original `Bool × Nat`. Its branches, termination, terminal-call charge,
erasure proof, exact-count specification, and difference-only counterexample
keep the previously reviewed meaning. No stronger source or runtime identity
was introduced.

- `unaryLESquare` calls the actual `Resources.erasureSquare` with paired Nat
  inputs, identity input decoding, the measured recursion as implementation,
  `unaryLE` as specification, and the existing `unaryLERun_erases` proof. It
  packages a genuine proved commuting square without assuming an arithmetic
  answer or any equality of costs.
- `unaryLESquare_value` consumes that square's `commutes` field and then the
  independent arithmetic theorem. The checked `(8,3)` example uses this
  public consumer and obtains false, so the adapter is exercised concretely.
- `compareBothWays` composes the actual two runs through existing
  `Resources.bind` and finishes with `Resources.pure`. Both directions are
  evaluated; no short-circuit behavior is implied. Pure adds zero observation,
  and the model explicitly leaves binding and pair construction uncharged.
- `compareBothWays_value` uses `Resources.bind_value` to preserve the two
  answers in the declared order. `compareBothWays_spec` proves the complete
  pair, adding the two established counts. Its two contributions are
  `min n m + 1` and `min m n + 1`; neither call is omitted or charged twice.
- `example_composed_directions` consumes that full specification at `(3,8)`:
  the answers are `(true,false)` and the total is eight. Differing answers
  make the orientation observable, and the total exercises both executions.

The legacy-import adjustment is documented accurately. The preserved error
log rejects importing the non-`module` resource file from a `module` file;
the staging source now uses ordinary imports without `module`/`public section`.
It introduces no private declarations, application axioms, or altered source
algorithm to resolve that compatibility issue. The error-log hash is
`c2b1e8d27b94b2c1b04ecd103e0a6c12d1eb9d54a71a1caee561d25dfa3f8dbe`.

The successful axiom output was read directly: `compareBothWays_value` uses
`propext` and `Quot.sound`; the other seven printed claims use `propext` only.
These are permitted foundational axioms. The current `.olean` hash matches
the owner's record, but neither that artifact nor these selected reports
substitute for the integrated exhaustive audit.

### Queue adapter review

Removing only the added resource import and four added theorem blocks from
the current source, in memory, reconstructs the initial reviewed source hash
`9266dae6612db42d811f798ca012ae45688fbc438b7cc75113ac01eaf20e078f`
exactly. The original source algorithms, instrumentation, erasure theorems,
size lower bounds, reachability, executor and potential counterproofs are
therefore byte-for-byte unchanged by this follow-up.

- `runPeeks_eq_resourcesRun` proves equality of the **complete** queue/cost
  pair with actual `Resources.run` on a replicated Unit command word. Its
  induction uses `Resources.run_cons` and threads the real step result. A
  value-only equality would be insufficient for transporting the count; this
  statement preserves both components.
- `resources_exact_accounting` actually applies
  `Resources.run_potential_exact`. Its local identity follows from unchanged
  state and addition commutativity, for every supplied natural-valued
  potential. The per-state charge is deliberately the measured traversal
  count itself. Thus it is a valid exact-accounting client, not a constant
  or asymptotic upper bound; source and README make that limitation explicit.
- `resources_peeks_exhaust_initial_credit` retains the existing reachable
  queue, positive repetition count, arbitrary initial potential, and strict
  budget failure. It transports these through the full executor equality
  and actual `Resources.budget_constant`, on the same trajectory. It does not
  discard initial credit or infer costs from an equality of values.
- `resource_workload_observation` connects the original enqueue-4/9/2 example
  to the existing executor and budget APIs. Its explicitly Measured-typed
  step returns the same queue and records 18 visits; the constant charge-two
  budget is six. The initial back-length credit is three, so nine is still
  strictly below 18. The proof consumes the original example and the new
  bridge rather than reducing an unrelated substitute workload.

The complete updated interface still requires no equality or order on payloads.
Explicit default and enqueue values supply actual witnesses. Potential
functions still range over queue states, not hidden histories or memoization
state. The README continues to distinguish this structural traversal model
from native execution, and to exclude transferring the obstruction to
normalizing dequeue or a changed representation without another proof.

### Follow-up disposition

**No unresolved findings.** The two previously uncompiled resource seams are
now concrete checked clients of the actual existing APIs, and independently
reviewed at the hashes above. No new generic resource framework is introduced.
The remaining local Nat-indexed queue executor is related by full equality;
whether to retain it as a convenience or replace consumers with direct
`Resources.run` statements is an integration choice, not an unproved seam.

Full source chapters, source-specific strict-comparator correspondence,
enqueue/dequeue amortized bounds, native/executable evidence where required,
public module placement, exhaustive proof auditing, and the chapter
Standards/Spec gates remain outside this bounded preparation review.

## Combined outcome

Both current exact-hash staged drafts and their checked resource adapters have
no unresolved findings in the assigned review scope. They may be checkpointed and later reused
through the main chapter-order workflow. This report supplies independent
statement/model review, not acceptance of a later chapter or of the whole book.
