# Compositional durability

Investigate durability as a realization of program semantics. Authors should
state what must survive, which observations are permitted, and which failures
the guarantee covers. Reusable constructions should connect those requirements
to persistence, recovery and coordination mechanisms while allowing specialized
representations. The project owner established this research direction on
2026-10-29; it does not select an implementation architecture.

The motivating concern is that choosing a database can make its operations,
constraint language, query facilities and failure guarantees shape the program.
We want to investigate how much of that choice can instead follow from the
program's requirements. An embedded database remains a possible realization;
avoiding a separate process alone does not answer the semantic question.

## Requirements and realizations

Keep the following distinctions available to authors:

- The program's meaning: valid states, transitions, mathematical relations and
  externally observable effects.
- Durability requirements: what acknowledgment commits to, admissible failures,
  permitted recovery histories and conditional progress.
- Realizations: representations, storage operations, recovery procedures and
  distributed protocols, together with their preservation contracts.

For example, a program might preserve accepted inputs for replay, persist a
result before publishing it, or preserve evidence that an external effect has
already happened. These are candidate requirements with different obligations;
none is the mandatory representation of durable computation.

Mathematical invariants, including ones involving transitive relations, should
be specified independently of storage layout. Whether to compute a relation,
store its closure or maintain a specialized representation is a realization
question. Query expressiveness, invariant enforcement under concurrent updates,
and invariant preservation across recovery need separate assessment.

## Composition and optimization

Independent durability does not establish atomicity of a joint operation. A
hypothetical pair of persistent components can each recover its own update while
a crash leaves only one side of an intended transfer recorded. The research
must identify the composition obligations and mechanisms that exclude such
histories. Distribution adds environmental and coordination assumptions that
must remain visible in the contract.

Local optimization is justified only relative to observations and dependencies
that other components rely on. Compare distinct realizations of the same
contract, including their client proof obligations, retained information,
storage traffic, synchronization and recovery costs. Semantic equivalence alone
does not establish a performance improvement or an optimal representation.

Arbitrary queries may serve diagnostics rather than operational behavior. A
reconstructible, delayed diagnostic view could have a separate observation
contract; an immediate consistent snapshot could impose stronger requirements
on authoritative state and publication. Neither separation nor staleness should
be assumed acceptable without stating the consumer's requirements.

A traditional relational database is a candidate specialization combining
query, constraint, transaction, introspection and runtime evolution requirements.
Recovering a bounded instance would test the generality of the constructions.
A complete derivation, universal optimality and automatic inference of weakest
requirements remain unestablished hypotheses.

## Verification and research method

Follow preservation obligations through serialization, storage ordering,
publication and recovery, rather than ending at an assumed database contract.
Keep remaining runtime, operating-system, device and environmental assumptions
explicit. A proof about a storage model does not establish that a physical device
implements it. Recovery during further crashes and representation evolution
must be covered or explicitly excluded from each bounded result.

Start with primary-source comparisons and discriminating examples. Reuse current
interaction, refinement, observation and resource constructions where their
actual hypotheses fit. Avoid requiring a universal effect language, canonical
log, database replacement or new package hierarchy before examples establish
the need. New formal claims follow the repository's checked-example, statement
review and build/audit requirements.

## Evidence and ownership

The [preliminary research](research/compositional-durability.md) compares prior
work, current local contracts and remaining questions. It is an assessment, not
evidence that the proposed durability realizations have been implemented.

- [#225](https://github.com/VladimirMarko/conaled/issues/225) owns this direction
  within the broader [interaction and recovery research
  #196](https://github.com/VladimirMarko/conaled/issues/196).
- [#226](https://github.com/VladimirMarko/conaled/issues/226) owns the next
  contract/composition assessment and bounded crash-recovery experiment design.
- [#227](https://github.com/VladimirMarko/conaled/issues/227) owns specialization,
  diagnostic-query contracts and representation/cost comparisons.
- [#194](https://github.com/VladimirMarko/conaled/issues/194) retains its existing
  external-process and filesystem consumers. [#174](https://github.com/VladimirMarko/conaled/issues/174)
  and [#177](https://github.com/VladimirMarko/conaled/issues/177) own shared
  data-structure and resource questions; [#36](https://github.com/VladimirMarko/conaled/issues/36)
  owns the broader internal-language direction.

GitHub Issues hold acceptance criteria and dependencies. Completion of the
preliminary survey does not complete this direction or gate all related work.
