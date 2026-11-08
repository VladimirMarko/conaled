# Local theory maps with a selected higher identity

[#355](https://github.com/VladimirMarko/conaled/issues/355) connects the generic
local-certificate transport from [#344](dependent-theory-maps.md) to an
independently typed Id/J argument. The translated argument is the existing
frozen client's dependent action on its selected higher identity, after the
client's original two substitutions. Its interpretation recovers the actual
chosen action and higher cell, rather than their inhabitedness.

## Frozen source and client

The source inference relation is `Reference.Derives`, specified before this
experiment in `ReferenceCalculus.lean`. Its judgments distinguish contexts,
types, terms, substitutions, finite dependent tails and typed equality.
`Reference.Tail` has arbitrary finite length. J requires a formed motive over
the whole path context and tail, and a branch at the reindexed root boundary.
The source includes explicit substitution, typed conversion/congruence,
identity formation/reflexivity, J computation and J substitution with their
boundary premises. These are existing rules, not consequences of generic
transport. There is no equality reflection or identity-witness truncation rule.
The [reference-calculus report](reference-dependent-calculus.md) describes the
original forward interpretation and its assumption boundary.

The selected client is `GuardedGroupoidMemo.signature`, interpreted here in the
existing cubical cocycle model. Its context contains points `x,y,z`, parallel
paths `p,p'`, a selected identity `h : Id(p,p')`, and two further dependent
binders `q,u`. The native action is `apd` of its J-built eta certificate section
along **that same `h`**. Despite the historical signature module's name, this
experiment does not infer higher behavior from a groupoid or set model.
`CubicalFrozenHigherObservation` supplies the existing nonzero higher cell.

`ReferenceFrozenInput` reconstructs these context extensions in the independent
source calculus. Its `sigma` duplicates the first point through the remaining
display; `tau` replaces the next point through the reindexed display. Neither
map is an identity (`sigma_nonidentity`, `tau_nonidentity`). These are exactly
the original frozen maps, including the later dependent binders.

The independently derived argument is bounded deliberately. Its signature has
four fresh leaves:

1. A family over the empty context.
2. A family over its first extension.
3. A family over the frozen input's path-variable context.
4. A section of that family.

`signature_valid` constructs a `WellFormedSignature` in declaration order. The
last two declarations parameterize the section on which the source proves
`apd`. They do **not** declare the resulting dependent action or its transport
law. `ReferencePath` and `ReferenceApd` derive transport, the motive and branch
boundaries, and `Derives.apd` from the independent rules.

During compilation, the last two symbols expand to the native certificate
family and its J-built eta section. `Interpretation.declarations_valid`
discharges those additional meanings using the native section's own formation
and typing derivations. This experiment independently derives the dependent
action of a supplied section; it does not independently rederive the entire
native eta-certificate construction in `Reference.Derives`.

## Adapter and composition

[ReferenceRulePresentation](../../SquareKit/Internal/DependentJudgments/ReferenceRulePresentation.lean)
turns the independent primitive constructors into a finite-premise `Rules`
table. `encode` is exhaustive over `Reference.Derives`; `applyRule` reconstructs
an independent inference from every table entry, and `decode` recursively
recovers the source inference relation. Premise positions, including congruence
arguments, remain indexed occurrences. Declaration membership is a local guard.
These constructions establish derivability in both presentations. No equality
between `decode (encode d)` and `d` is claimed here.

Each `Rule.instantiate` case checks the boundary of a primitive rule under a
free-leaf template. The J cases retain the instantiated finite tail, branch
map, motive and typing premises. `templateMap` turns that result into the
corresponding local certificate. Whole-proof `transport` and exact
`transport_comp` then use #344's `TheoryMap.transport` and
`TheoryMap.comp_transport`; there is no assumed whole-client correctness field.

This adapts #344's rule-certificate layer to the existing explicit-substitution
syntax. It does not port Id/J into #344's separate scoped binding AST or assert
full BHL acceptability. Free leaves are schematic symbols; dependent variables
are represented by the source calculus's context, generic-term and explicit
substitution operations. Accordingly, a free-leaf template and an object
substitution have different interfaces and different typing obligations.

The first client template maps four source leaves to three intermediate leaves,
expanding the chosen section symbols into native syntax. The second maps those
intermediate names into the original two-leaf namespace. The intermediate third
leaf is unused by the first map's output. The second stage is a namespace
adaptation, not a second change of logical principles. `compilation_stages`
checks equality of the resulting **proof trees** for composition versus staged
execution. `compiled_expression` independently identifies the translated raw
action with the old native expression after `sigma` and `tau`;
`compiled_witness_expression` identifies its selected cell with
`native.thetaInput.h`.

## Checked preservation and controls

The main checked specialization is
[ReferenceHigherTheoryMaps](../../Examples/ReferenceHigherTheoryMaps.lean).

| Evidence | Exact contract |
|---|---|
| `action_typed`, `action_twice` | Independent typing of the J-derived action, then its two typed object substitutions. |
| `motive_twice`, `branch_twice` | Formation of the substituted motive under both lifted path substitutions, and typing of the branch under both base substitutions. |
| `branch_family_twice`, `motive_context_twice`, `substitution_contexts`, `composition_operands` | Required families, contexts and both operands at the common equality boundary, using the existing presupposition results. |
| `compiledMotive`, `compiledBranch`, `compiledCompositionOperands` | Those dependent boundaries survive the same local-certificate compilation route. |
| `Interpretation.compiled_typed`, `compiled_witness_typed`, `source_witness_typed` | Soundness consumes decoded generic translations with all instantiated declarations validated. |
| `Interpretation.selected_action`, `recoveredAction_eq` | Evaluation and dependent extraction return the actual native chosen action after both original substitutions. |
| `Interpretation.selected_witness` | Evaluation returns the actual selected `tauHomotopy.value`, retained by the original display pullbacks. |
| `HigherControl.recovered_eq`, `observation_one`, `rejects_truncation` | Extract the translated original higher binder, reindex it at the existing cubical assignment and observe `1`; replacing it by the reflexive cell would observe `0`. |

The action and witness are connected through the argument of `apd`, not paired
as unrelated results. The negative control observes the original input's
translated cell. After both object substitutions the theorem is exact equality
to the native retained displayed cell and its action; this work does **not**
add a separate numerical observation at an assignment to the twice-reindexed
context. The distinction prevents the source observation from being advertised
as a new post-substitution numerical calculation.

The apd derivation uses based J with an empty J tail inside a context that
already has the later dependent binders. To exercise J's explicit nonempty-tail
rule as well, `NonemptyTail` compiles the existing independently specified
two-entry-tail example from `ReferenceDependentCalculus`. Its motive mentions
the final generic term, and its last family varies with the previous entry.
The example transports J, beta and the branch-map naturality proof through two
permutations. `interpreted_naturality` validates the decoded compiled proof in
the original inhabited dependent model after the permutations cancel. This
auxiliary set-level example checks tail bookkeeping; higher nontriviality comes
only from the separate cubical client above.

## Equality and assumptions

Proof trees and raw syntax are compared with Lean propositional equality.
The trees live in `Type`; their equality does not follow from proof
irrelevance. Semantic extraction uses equality of the actual indexed section
values. The modeled identity witnesses remain data, distinct from the host
equality proofs used to align their types. The cubical observation transports
only the established family equality before observing the selected cell.

A template does not automatically yield a conventional fresh-leaf declaration
list. Expanded section declarations are interpreted assertions whose validity
is proved by `declarations_valid`. Arbitrary target declarations cannot be
assumed valid merely because the source is a `WellFormedSignature`.
`Reference.sound` requires their validity in the selected `Typed.Model`.

The local obligations include typed substitution in contexts and tails,
formation of J motives and branches, and the existing branch square/J
substitution laws. Neither endpoint equality alone nor an inhabitant of the
right identity type replaces the chosen witness. Native evaluation theorems
supply the semantic behavior of the selected eta section and apd; the generic
map theorem supplies syntactic proof transport. Neither theorem is substituted
for the other.

## Cost, direction and deferred work

The reusable gain is whole-proof composition from primitive local certificates:
this client does not need another recursive proof translator or another proof
of its composition law. The adapter nevertheless has a cost. It repeats the
primitive rule table, reconstructs each case for `decode`, quotes each source
constructor for `encode`, and checks every instantiated rule boundary.
Changes to `Reference.Derives` must update that adapter. Its exhaustive
pattern matches catch missing source cases, but are not a maintenance-free
schema generator.

The independent path/apd derivation and frozen-context reconstruction also
required typed boundary conversions that the native guarded proof can omit.
The native context/display and semantic evaluation proofs were reused, not
replaced. Most client-specific connection work concerns exact raw recipes,
the four declaration meanings and dependent extraction. The separate
finite-tail example reuses its existing model and branch proof. These are
source-level obligation comparisons, not measured human or agent productivity
claims.

The experiment supports retaining the independent calculus and using generic
local maps at its compilation boundary. It gives no reason to replace the
native higher semantics or force the source into a universal AST. A future
Id/J port into the scoped #344 syntax should justify its additional binder and
substitution machinery with a client benefit, and preserve these same witness,
action and tail tests. #356 owns the adjacent shared-meaning comparison; #235
owns decisions beyond this bounded experiment.

Intermediate administrative erasure remains a deferred optimization. This
adapter retains explicit object-substitution instructions through composition
and uses the existing interpretation at the end. It adds no theorem permitting
earlier erasure of #344's administrative instructions. Such an optimization
needs a consumer and a compatibility proof. General reflection, reverse
compilation and executable proof translation remain separate consumer-driven
work. #107 stays paused, #108 unselected and #260 inactive.

## Statement review and validation

Statement review checked the independent source premises, ordered signature,
J motive/branch boundaries, distinction between the two kinds of substitution,
and the connection of apd to the actual selected higher binder. The concrete
cubical assignment witnesses nontriviality; the auxiliary dependent-tail model
witnesses satisfiability of its declarations. The formal conclusions are the
contracts listed above, not equality reflection or general equivalence of
calculi.

The new example is imported by `SquareApplications.lean`, so the normal build
and exhaustive proof audit include the adapter, independent path/apd proofs
and client. Focused Lean checks passed without warnings. Candidate acceptance
uses the repository's `check.sh --candidate HEAD` and corresponding verification
record; the orchestration review records the exact candidate and results.
