# XT04 bounded source assessments

These are independent source-only readings of a stopped draft, not final
Standards/Spec review, elaboration, a build, an audit or acceptance. Frozen
requirements and original base remain unchanged. Root's reading-phase source
identities are in `tree-accumulator-source-preflight-snapshot.json`; readers
are not claimed to have checked those digests. The old Chapter 1 gate remained
unchanged, with no second compiler/checker/project hash helper.

## Core invocation, all-suffix work and transport — book_inventory

**No concrete finding arose from this bounded reading. No XT04-SP ID is
assigned.** The stopped core's definitions, statements and proof structure
match XT04-01/02 at the source level.

The reader read the complete frozen requirements and complete
`Applications/Resources/TreeAccumulator.lean`, together with relevant
`Trees.Observations`, `Resources.Measured` and `Resources.CallCount` definitions
and laws. No file digests or declarations were elaborated.

### Actual execution and raw observation

`nodeRun` uses `bind (right suffix) (fun rest => left (a :: rest))`. The left
function receives the actual returned right list. The definition neither
computes an independent specification list nor uses append. Its exposed
observation is precisely `(R.observation + L.observation) + entry`.

Raw operation, constructor equations and value laws require only `Add C`,
without zero, associativity, commutativity, order, label equality or inhabitant
assumptions. Payload, source-observation and target-observation universes remain
independent.

`invoke` applies the existing ordinary `Trees.fold` at the measured-function
summary type. There is no second recursive tree executor or cost evaluator.
Nil retains its entry observation; `invoke_node_tick` connects Nat entry one
to post-body `tick`, preserving both empty-child invocations.

### All-suffix correctness and length

`invoke_value` quantifies over arbitrary suffixes and generalizes them in tree
induction. Its proof uses the right result before the left induction hypothesis
at the resulting cons suffix. Append associativity occurs in the specification
proof, not the executable definition.

`invoke_length` derives `t.numNodes + suffix.length` from the value theorem and
existing inorder length law, keeping output length distinct from invocation
work. Empty trees, repeated labels and empty payload types remain covered
without additional premises.

### Natural work and positive-size bound

`invoke_cost` also generalizes every suffix. The left induction hypothesis
therefore applies to the actual right-produced argument without an assumed
uniform cost law for unknown callbacks. The exact pair is the frozen one:

```text
invoke entry t suffix =
  (Trees.inorder t ++ suffix, entry * (2 * t.numNodes + 1)).
```

It includes zero entry, nil and arbitrary suffixes. The positive-size theorem
assumes `0 < t.numNodes` before deriving `1 <= t.numNodes` and
`cost <= 3*entry*t.numNodes`. It makes no false proportional bound at nil.
Natural algebra stays confined to these quantitative proofs.

### Reweight transport and boundary

`reweight_nodeRun` uses existing `reweight_bind` and preservation of the final
entry addition. Returned values are unchanged, preserving the dependent left
argument. No commutativity or reordering is used. `reweight_invoke` lifts that
node law through `Trees.fold_fusion` and evaluates the resulting function
equality at the supplied suffix. AddMonoid assumptions remain local to the
existing hom interface.

The module explicitly assigns observations to later invocation and requires
separate measurement of construction. It does not import XT03 construction or
XD01, claim construction is free, or identify counts with compiler/runtime work.
Construction programs, product clients, comparison execution and ordered
trace were outside this core-only reading; their absence from that core is
not a finding against the unfinished unit.

This is uncompiled source assessment, not validation, either final review axis
or acceptance. No code, control file, Git state, cache or gate was changed.

## Product and ordered diagnostic — architecture

**No concrete XT04-OP defect was found in the stopped source.** The product
client and ordered diagnostic match XT04-02/05. Proof shapes are consistent
with public core contracts; this remains source-only assessment.

### Product observation: same invocation, preserved values

`invoke_pair` derives both components from actual
`invoke (entry1,entry2) t suffix`, using the existing first/second projection
homs through `reweight_invoke`. Each transport is an equality of complete
measured results; `congrArg Prod.snd` extracts its observation component.
Actual returned lists and dependent left-call suffix are preserved, rather
than merely comparing independent numerical recurrences.

Coercions and projections are definitionally compatible with the pinned homs.
`invoke_cost` supplies the natural counts after transport. `pair_sample`
separately consumes `invoke_value`, connecting the full result
`([0,1,2,3,9,8],(9,18))` to actual execution. These are two tariffs on one
invocation, not construction and invocation phases.

### Ordered diagnostic: actual dependency and its own value law

`traceInvoke` uses existing `Trees.fold` and public `nodeRun`. Nil returns the
suffix at zero observation, and each node supplies its own post-body label
token. This label-dependent entry differs from `invoke`'s fixed entry. The
implementation correctly proves `trace_value` through `nodeRun_value` and its
own all-suffix induction instead of applying fixed-entry `invoke_value`.

The order is right word, left word at the actual right result, then node
label, grouped `(rightObservation+leftObservation)+nodeToken`. Both value
and observation reasoning retain `a :: rightResult` and the child order.
The sample therefore yields `[2,3,0,1]` for every suffix. Nil is silent and
node tokens are post-body. Pinned root-level `toMul_add`, `toMul_ofMul`,
`toMul_zero` and the FreeMonoid decoder laws match the proofs; no commutativity
is used.

### Comparison with the earlier trace

`invocation_order_differs` compares only decoded words: new `[2,3,0,1]` and
old `[0,2,3,1]`. The earlier theorem's second conjunct is its proven word law.
The new execution retains its inorder-list value theorem; the earlier one
retains its size-valued theorem. Code/comments do not conflate returned types
or assert equality of the measured computations. Rewriting leaves a concrete
Nat-list inequality, appropriately closed by ordinary `decide`.

### Assumptions, transport and verification limits

The core preserves independent payload and observation universes. Only `Add C`
is used for raw invocation and value correctness; nil directly returns the
entry without requiring zero. AddMonoid assumptions are local to transport;
quantitative statements are explicitly Nat-specific. No payload inhabitant,
equality, order or nonempty-tree assumption is introduced.

The node transport uses `reweight_bind` and `map_add`. The function-valued
fold fusion followed by `congrFun` fits the existing signature and requires
no observation reordering. Outstanding checks are compilation of coercion/
projection reductions, function-valued fusion and concrete word simplification.
The reader found no source-level mismatch and did not label untested expressions
as defects. No files, requirements, trackers, Git, caches, compiler/checker
state or gate were changed; no final-review claim was made.

## Construction and main invocation clients — tail_examples_preflight

**No XT04-CP finding identified.** The reader read the complete stopped
`Examples/TreeAccumulator.lean`, frozen requirements, invocation core and
XT03 contracts needed by these uses. No concrete mathematical, scope or
obvious proof/API mismatch arose in the requested client scope.

### Actual construction and applications

`build` is the actual XT03 measured fold. Its callback returns
`pure (nodeRun invocationEntry left a right)`, capturing a function without
applying either child. `build_value` consumes `run_value_of`, while
`build_cost` consumes the constant-zero callback law. Construction and
invocation entries remain distinct.

`buildOnce` binds construction and applies its returned function. `buildTwice`
binds construction once, applies that same returned function to both supplied
suffixes and retains both results. Neither program independently reconstructs
an invocation function or rebuilds it for the second application.

| Construction entry | Invocation entry | Construction | Once | Twice |
| --- | --- | --- | --- | --- |
| 1 | 1 | 9 | 18 | 27 |
| 2 | 3 | 18 | 45 | 72 |

The generic formulas and these distinguishing sample values are correct.
Application costs come from `invoke_exact` after consuming the actual
construction result; algebraic simplification is confined to Nat observations.

### Actual suffix dependency and boundaries

`sample_right` establishes the actual right-subtree result `[2,3,9,8]`.
`sample_left_after_right` places that actual invocation's value projection in
the left-call suffix, with root label `1` prepended. It checks the intended
argument dependency rather than substituting only a guessed list.

Nil, singleton and sample results match the arbitrary-suffix law and costs
`e`, `3*e` and `9*e`. The noninjective repeated-label case retains all four
tree occurrences and both suffix occurrences. `empty_payload` eliminates
the impossible node and cons constructors directly, introducing no payload
inhabitant. `repeated_child` retains both occurrences and cost `e*(4*n+3)`.
The zero-entry case and nil counterexample to a pointwise `K*n` bound are
mathematically correct.

### Materialize-then-append comparison

`materializeAppend` genuinely runs XT03's single-append inorder and passes
its returned prefix to `appendRun`. Its cost proof uses `single_value` and
`inorder_length` before replacing the append input's length by `t.numNodes`.
Thus the extra work is the actual append cost `n+1`; sample `15+5=20` is
correctly contrasted with accumulator work `9`. The returned lists agree.

### Empty-suffix-only countercase

The three statements jointly establish that nil invocation and suffix-copy
append agree as measured results on `[]`, that their erased values agree
for every Nat suffix, and that on `[9]` their costs differ, `1` versus `2`.
This supports the need for an all-suffix invocation theorem without importing
XD01 or changing its tariff.

### Limits

Referenced public theorem signatures and proof expressions appear consistent
on source inspection. No compiler/checker confirmed elaboration. The assessment
does not cover integration, documentation, the separately assessed ordered/
product clients, or final review. No files were edited and no compiler,
checker, hash helper, Git/ref/cache operation or gate change occurred.
The completed bounded read supplies no final-review approval or acceptance.

## Reconstruction documentation — book_inventory

**No concrete finding arose. No XT04-DOC ID is assigned.** The reader read
the full `fdsa-tree-accumulator-invocation.md` and only the appended FDSA-XT04
section of `fdsa-reconstruction-map.md`, against the frozen requirements
and retained source preflight.

### Source correspondence and invocation

The note accurately gives the cons-only source recurrence, including the
right-result dependency and all-suffix requirement. It distinguishes
right-before-left execution from left-root-right output order. The provenance
qualifications remain explicit: the Isabelle snapshot postdates the manuscript;
`Tree.inorder2` supplies the recurrence and arbitrary-suffix value proof;
no generated `T_inorder2` declaration is claimed. The exact count belongs to
the declared measured execution.

Raw `Add` grouping, post-body charge, independent universes, nil charge,
zero-entry boundary and positive-size proportional bound match the frozen
statements. They are not promoted to compiler, physical-runtime or
constant-stack results.

### Outer erasure and inner measured functions

The construction explanation correctly states that its returned-function
equality has codomain measured results. Removing the outer construction
observation preserves both components of each later invocation result.
The construction value law identifies the returned function with `invoke e t`;
the independent all-suffix invocation theorem supplies its numerical cost.
This neither loses the inner observation nor claims that equality of erased
output lists establishes invocation work.

### Tariffs, composition and examples

With `m=2*n+1`, construction, once-applied and twice-applied counts are
respectively `b*m`, `(b+e)*m` and `(b+2*e)*m`. Sample totals `9/18/27` and
unequal-tariff totals `45/72` are consistent. Product observation `(9,18)` is
two tariffs on one invocation, not the construction/application phases.
The XD01 comparison retains its different composition tariff; `4*n+1` is
consistent with its retained unit-cost empty case.

The documented sample dependency, repeated occurrences, actual materialize-
plus-append comparison `20` versus `9`, empty-suffix-only counterexample and
ordered word `[2,3,0,1]` are consistent with the retained recurrences. Trace
discussion distinguishes this list-valued execution from XT03's size-valued
execution and compares their words only.

### Scope and status

Both documents retain partial coverage of C04-017/018, the separate direct-
inorder quadratic obligation, pending chapter/appendix work, prerequisite
acceptance and outstanding validation/reviews. Exclusion wording does not
impose additional framework requirements.

The reader did not independently inspect the newly described example
implementations or import closure in this documentation pass, and did not
repeat the completed core reading. No edits, compiler/checker/hash-helper
execution, Git/cache changes, final-review claim or acceptance action occurred.
