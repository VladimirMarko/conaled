# XT04 tree accumulator invocation draft handoff

## Exact identities and authority

- Local ticket: FDSA-XT04; parent FDSA-000; original whole-book task unchanged.
- Frozen requirements: `tree-accumulator-invocation-requirements.md`, version 1,
  SHA-256 `1c97ae18eb32c4ea582e8ee38162fe7963f3ba54394c919e91b7bd92c1b90477`.
- Original and immediate parent base:
  `b0fce71fa00b2ff6250b09002176bdc75baf1f46` (saved unaccepted XT03).
- Candidate: `b035f1151ab4f0c7d7380818576cfe97dae434c4`.
- Branch: `work/fdsa-tree-accumulator`; checkout: `conaled-tree-accumulator`.
- Commit: `feat(resources): add measured tree suffix invocation (#174)`.
- Six changed paths, 671 inserted lines; source clean after commit, confirmed
  by Git operations within the pinned Nix environment.
- Checkpoint 0033 saved the clean pre-code scope and complete preflights before
  source edits. Checkpoint 0034 will preserve this committed draft and readings.

Accepted repaired Chapter 1, XT01 and XT03 remain prerequisites to integration
or acceptance. XT02 and XD01 are not implementation dependencies. This shared
unit does not change the Chapter 2-first integration plan. Preserve the original
base, development history, frozen requirements, all inherited findings and
original book obligations when adapting to an accepted tip. No GitHub write
has occurred.

## Actual execution, construction and connected cases

`Applications.Resources.TreeAccumulator` specializes the ordinary `Trees.fold`
at suffix functions returning actual measured lists. Its public node algebra
first invokes the right child, then passes the actual result with the root
label prepended to the left child. Raw grouping is `(right+left)+entry` and
requires only `Add`; payload and observation universes remain independent.
There is no new recursive tree executor or separate cost evaluator. Nil retains
its entry observation, and the unit Nat entry connects to existing post-body
`tick`.

Both value and cost proofs generalize arbitrary suffixes. The exact natural
result is `(inorder t ++ suffix, e*(2*numNodes t+1))`, including nil and zero
entry. Length follows from the value law. The proportional `3*e*numNodes t`
bound explicitly assumes positive node count. Existing additive-hom transport
uses the actual dependent bind and function-valued fold fusion without
commutativity or observation reordering.

The construction client is actual XT03 `TreeFold.run` with zero-observation
callbacks that return `nodeRun e`. Its outer value theorem identifies the
returned function at the full inner measured-result type. Its outer work
is `b*(2*n+1)`. Actual binds consume this returned function once or twice;
the latter constructs it only once and retains both invocation results.
The complete pair statements give `(b+e)*(2*n+1)` and `(b+2*e)*(2*n+1)`.
The independent all-suffix invocation theorem supplies the application counts.

Connected examples retain:

- Arbitrary suffixes, nil, singleton, the asymmetric four-node sample and
  its actual right-result dependency in the subsequent left invocation.
- Noninjective repeated payloads, `Empty`, repeated child occurrences,
  zero entry and the nil counterexample to an all-tree `K*n` bound.
- Sample construction/once/twice work `9/18/27`, plus unequal-tariff totals
  `45/72` for construction entry two and invocation entry three.
- Actual single-append materialization followed by append of its returned
  prefix: sample work `20` versus invocation work `9`, with equal values.
- Nil/suffix-copy computations agreeing as measured results at empty suffix
  and agreeing in values everywhere, but having costs `1` versus `2` at `[9]`.
- Existing product hom projections giving `(9,18)`, two tariffs on the same
  invocation rather than a confusion of construction and invocation phases.
- Actual function-valued FreeMonoid trace, its own all-suffix value theorem,
  silent nil and post-body word `[2,3,0,1]`; comparison only of observation
  words with XT03's `[0,2,3,1]`, whose returned value is a size.

The reconstruction note preserves the dated source provenance and source/model
boundary, statement assessment, phase accounting, partial C04-017/018 coverage
and remaining original book obligations. No source-cost translator, general
closure/history framework, physical allocation or constant-stack claim is
introduced. The direct-inorder quadratic family remains separate open work.

## Independent bounded source readings

Full retained assessments: `tree-accumulator-invocation-source-preflight.md`.
Original reading-phase identities: `tree-accumulator-source-preflight-snapshot.json`.
Final six-path identities: `tree-accumulator-invocation-source-identities.json`.

- `book_inventory`: complete core against XT04-01/02 and reused APIs; no
  concrete finding. Separately read the complete note and appended XT04 map
  section against the frozen requirements and source preflight; no finding.
- `tail_examples_preflight`: complete construction/main client against
  XT04-03/04 and relevant XT03 contracts; no concrete mathematical, scope
  or obvious proof/API mismatch.
- `architecture`: complete product and ordered-observation client against
  XT04-02/05 and the core contracts; no concrete finding. Actual dependent
  arguments, result types, hom projections and noncommutative order retained.

These are source-only assessments, not elaboration, validation, final review
or acceptance. No findings were closed by these readings. Inherited XT03-CP01
and XT03-DOC01 retain their original source correction/recheck history and
pending compiler/final confirmation as applicable. Untested coercion/fusion,
function equality and concrete simplification remain ordinary compilation
obligations; no observed compiler failure is invented for them.

## Validation and continuation

Passed: tracked unstaged `git diff --check`, complete staged
`git diff --cached --check`, explicit six-path staging check, source commit
and clean post-commit status in the pinned Nix shell. Public closure is intended
through the new `Examples.TreeAccumulatorObservations` root import to the main
client and core. This is not a project-checker result.

Not run: any XT04 compiler, focused build, candidate gate, exhaustive proof
audit or final Standards/Spec review. No second compiler, checker or project
hash helper ran during old Chapter 1 session 80227. That old candidate remains
`1aabd512284fe86254278ac631eda061d311050b` and its eventual result cannot accept
the Chapter 1 repair or this unit.

Next: create and upload checkpoint 0034 immediately. Continue the old gate
unchanged to actual exit, preserve its historical outcome, then follow the
retained repaired Chapter 1 acceptance process and initial Chapter 2 plan.
Integrate XT04 only when its prerequisites have been accepted, preserving
history and incorporating their corrections. The full matching candidate must
receive applicable build/guards/audit, both independent final axes with full
scope and carried findings, and immediate candidate verification. No chapter,
appendix or shared unit is accepted by this handoff.
