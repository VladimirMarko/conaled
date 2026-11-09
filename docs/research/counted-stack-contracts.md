# Counted stack contracts and direct compiler clients

Issue #409 implements the bounded experiment proposed by
[the algebra/program-specification assessment](algebra-and-program-specification.md).
Retain the direct compiler APIs. The experiment also retains a small optional
`Certified.Budget` predicate and its composition theorem; it does not introduce
a universal execution wrapper or change the compiler target.

## Execution and observations

[Measured stack execution](../../Applications/Stack/Measured.lean) executes the
existing `runInstr` at each typed instruction, attaches one natural-number
charge, and sequences the results using `Resources.bind`. Empty code uses
`Resources.pure`. The unit charge includes structural and primitive
instructions equally. It abstracts over the implementation cost of supplied
total primitive functions. It measures neither wall time nor bit complexity,
and it does not add a partial primitive semantics to this finite interpreter.

`runMeasured_value` recovers `run` for every typed program and state, including
programs that change stack shape. `runMeasured_append` derives sequencing from
the instrumented interpreter. `runMeasured_cost` then establishes equality with
a static instruction count. The static count is a consequence of execution
accounting, not a disconnected estimate substituted for it.

`append_padding` proves that appending `dup; swap; swap; fst` retains the full
output state while adding exactly four steps, for arbitrary input and output
types and stack tails. `padding_changes_cost` excludes equality of the two
counts. This is a checked limitation of value equality as a resource contract.
The old semantic squares continue to forget costs deliberately.

## Matched clients and proof routes

The native clients were fixed before the optional predicate was designed:
`MatrixCompiler.linearCombination` computes `2*x+3*y`, and `Arithmetic.shared`
computes `(x*y)*(x*y)+x`. [CountedStack](../../Examples/CountedStack.lean) compares
two composed tasks:

| Task | Components | Same bound proved by both routes |
| --- | --- | --- |
| `linearThenTriple` | Compiled linear combination, then the existing scalar primitive with coefficient 3 | Linear code instruction count plus 1; the concrete count is 15 |
| `sharedThenNegate` | Compiled shared arithmetic, then the existing negation primitive | Shared code instruction count plus 1; the concrete count is 41 |

Each direct proof exposes measured append, rewrites the intermediate state
using `Certified.measured_correct`, and adds the component bounds. Each optional
proof applies `Budget.comp` to the same component evidence. The predicate is
on the unchanged `Certified` arrow; it only states a bound on its measured
execution for all inputs and tails. Its composition theorem proves the global
bound from actual sequencing. It does not require the global client conclusion
as a field. The scalar and negation evidence comes from the actual primitive
instruction. The two compiled component bounds come from `runMeasured_cost`
and reduction of their existing code.

The optional theorem saves the repeated intermediate-state rewrite and natural
addition step in the second client. Both routes still require the same
component evidence and the same tariff choice. Neither redoes the source
compiler induction. This is enough to retain the optional stack-specific lemma;
it is not evidence for imposing a new shared execution interface on all
backends. Clients needing only values can continue using `Certified.correct`
without learning the measured definitions.

`matrix_agreement` retains the quantified matrix/stack output and arbitrary-tail
guarantee. `arithmetic_after_update` retains the independent incremental-update
comparison. `arithmetic_enclosed` retains the interval relation on the actual
executed value for every related input box. These proofs erase the counter and
reuse the old theorems; they neither copy their compiler proofs nor weaken their
quantifiers. `linear_value_tail` and `shared_value_tail` give the concrete
composed value formulas with arbitrary tails.

## Partial higher-order boundary

The separate #308 syntax remains separate. `Partial.looping_related` relates a
syntactic lambda whose body diverges to its partial semantic function.
`retained_partial_function` applies the existing related-input application
result at function type: a higher-order identity caller can return that partial
function as a value. `applied_loop` uses the same result when the function is
invoked on a numeral. `no_totality` uses return/divergence adequacy to prove
infinite execution and exclude every ground return.

No decoder for arbitrary host functions is required. These results show why a
universal adapter demanding total execution would exclude an existing useful
client. They do not transfer stack instruction counts to the partial language
or infer cost preservation from its denotational equality.

## Validation, reuse and author obligations

[Executable controls](../../Examples/CountedStackRun.lean) check empty code,
one arithmetic instruction with a nonempty tail, four-step padding, unequal
counts despite equal outputs, and both composed clients. The fixed inputs
`(3,4)` and `(3,2)` give respectively `54` at cost 15 and `−39` at cost 41;
padding the latter leaves `−39` and raises the count to 45. These observations
supplement the universal projection, append and padding proofs. They do not
benchmark the Lean runtime.

| Obligation | What was done |
| --- | --- |
| Setup | Added an instrumented instruction and sequence interpreter, projection and append proofs, static-count connection and padding laws. Existing `Resources.bind` supplies the additive sequencing operation. |
| Component evidence | Reduced the existing compiled linear and arithmetic instruction sequences; used the single primitive budget theorem for their suffixes. No new source syntax or compiler correctness induction. |
| Reused proofs | `Certified.correct`, `MatrixStack.agree_preserving_tail`, `ArithmeticPipeline.stack_after_update`, `stack_enclosed`, and #308's related-input and adequacy results. |
| Repeated client work | Direct proofs repeat measured append, intermediate-state rewriting and adding bounds. Optional proofs reuse `Budget.comp`; both still establish component bounds. |
| Changed client | Padding changes the resource claim by four while preserving value/tail claims. The generic theorem and executable padded arithmetic control exercise this distinction. |
| Repairs during development | Added the explicit natural additive-monoid instance import; supplied primitive types where elaboration could not infer them; supplied the empty program's stack indices. The shared compiled-code reduction needed a local heartbeat allowance. These were encoding/proof-setup repairs, not changes to the frozen mathematical expectations. |

No trustworthy author-time or token comparison between routes was collected.
Source length and successful elaboration do not establish agent productivity.
The comparison is limited to two finite first-order compositions under one
instruction tariff. Variable primitive costs, retained caches, storage,
branching and partial execution require their own observations and laws.

The acceptance checks are the README candidate build and exhaustive proof audit,
plus the executable controls above. Independent review is coordinated by the
enclosing implementation loop. Open #394/#399/#400/#406 retain their research
scopes. This experiment adds no foundational model, new axiom, audit exception,
backend migration, or requirement to adopt the optional predicate.
