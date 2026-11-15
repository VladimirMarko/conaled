# Persistent histories and debit accounting: bounded reuse inventory

Prepared 2026-11-03 by `/root/trace_reuse_map` for local10017. This is a
read-only architectural investigation and proposal, not implementation,
independent review, a Lean proof, task activation, or chapter acceptance.
Only this note was written. No compiler, source, Git, tracker, cache or
validation process was changed. Chapter2 remains the earliest unaccepted
chapter; the source owner is separately inspecting thesis19–24 and book6.

## Inspected inputs and conclusion

The existing resource executor is the appropriate execution layer. A small
debit/history layer can reuse it without introducing another state executor,
writer monad, graph reachability implementation, or potential framework.
The missing argument is specifically about persistent logical histories and
the difference between repeated charges and shared realized identities.

Repository code was inspected at main
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`; the newer suspension interfaces were
inspected at frozen candidate
`3dd930c3e3989f3e5530463f3ac937a629551335`. The latter is still unaccepted.
Mathlib source was inspected at its actual pinned checkout
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Names below are source-inspected
interfaces, not newly compiled experiments.

The architectural constraints applied were `AGENTS.md`,
`docs/agents/architectural-quality.md`, `docs/agents/domain.md`, `GLOSSARY.md`,
ADRs0001/0010 and `docs/language-direction.md`: reuse existing mathematics;
separate operations, meaning and laws; preserve observations and ordinary
clients; expose only required structure. No Felix parity claim or upstream
replacement is proposed by this bounded application foundation.

## Existing local constructions

| Existing source | Reusable capability | Boundary that must remain explicit |
| --- | --- | --- |
| `Applications/Resources/Measured.lean` | Ordinary value/observation pairs; `bind`, `reweight`, `reweight_bind`, `erasureSquare`; observations need not commute. | Equality of returned values does not identify resource observations. `reweight_bind` requires an additive homomorphism. |
| `Applications/Resources/Workload.lean` | `run`, `run_append`, `run_invariant`, `run_value_fusion`, `reweight_run`; arbitrary instruction and state types. | The chronological sequence is one actual global execution, not necessarily one logical version path. A global state can retain all persistent handles and shared memory. No replacement executor is needed. |
| `Applications/Resources/Potential.lean` | Same-trajectory `budget`, `run_potential`, exact telescoping, initial/final boundary potential, constant-charge corollaries. | A potential attached to one reused version cannot be spent independently along several branches by merely applying this theorem twice. The existing theorem requires the actual successive global states. |
| `Applications/Durability/Storage.lean` | `Heap`, immutable extension `Extends`, fresh `put`, preservation of represented retained roots. | This is a storage realization, not the source logical-operation graph. Its linked-history layouts should not become the generic debit model. |
| `Applications/Durability/DiagnosticRelational.lean` | Distinguishes accepted record occurrences/positions from the set-of-endpoints observation; `orderedRows` preserves the list of occurrences. | Useful precedent for keeping occurrence identity before quotienting. It is specialized to durable request identities and bounded graph endpoints. |
| `Applications/Durability/DiagnosticGraph.lean` | `Edges`, `Relation.TransGen` reachability, monotonicity under history extension, finite closure correctness. | The admission layer explicitly requires `Acyclic` and rejects loops/cycles. Its `allows`/`AdmittedStep` policies are incompatible with the stated TU.TRACE scope. Its edge relation also forgets parallel-edge identity. Do not adopt those policies as trace validity. |
| `Applications/Durability/ResourceEvents.lean` | Instruments existing storage transitions; proves erasure to protocol steps; keeps primitive weights explicit. | It deliberately does not charge all planning/client work. It is a useful composition example, not the missing complete PFDS cost model. |
| `Applications/Durability/Retention*.lean` | Bounded retained-history storage, finite layouts and preservation/refinement laws. | These are physical retention/resource protocols. They do not provide persistent-version logical histories or debit discharge. |

The finite suspension observer at3dd already uses `Resources.run` with
`FreeAddMonoid Event`. `Suspensions.Core.Observation.workload_append` composes
actual prefixes; `completion_eq_search` connects the event observation with
the finite evaluator; `traced_evaluates_observe` preserves the full answer and
the exact newly appended ordered events. Those are the right operational
inputs for later adapters. A new unrelated event generator would lose that
connection.

The3dd source theorem `Suspensions.Pure.Simulation.source_cacheWrites_le_one`
counts successful cache writes in an actual finite admitted pure execution,
with primitive compatibility, hereditary preservation and representation
premises. It does **not** count all body work or all failed forcing attempts.
Its exception/retry cases can perform repeated body attempts with no cache
write. Consequently, this theorem alone does not justify replacing arbitrary
execution cost by the number of distinct suspension addresses. A debit must
represent the appropriate cost unit, and the adapter must account for every
charged operation, including work outside successful memoized bodies.

## Pinned Mathlib interfaces already cover the basic mathematics

1. `Mathlib.Combinatorics.Quiver.Basic`: `Quiver` has Type-valued arrows,
   so it supports parallel edges, loops and cycles without extra axioms.
   `Quiver.IsThin` is an optional restriction and should not be imposed.
2. `Mathlib.Combinatorics.Quiver.Path`: `Quiver.Path`, `Hom.toPath`,
   `Path.comp`, `Path.length`, `length_comp` and associativity preserve
   actual edge witnesses. Use this when edge identity or a path witness is
   part of the observation.
3. `Mathlib.Combinatorics.Quiver.Prefunctor`: `Prefunctor` maps vertices and
   edge witnesses. It is the existing map interface if a source/backend
   graph correspondence needs one; no parallel custom graph-map class is
   justified merely for this task.
4. `Mathlib.Logic.Relation`: `Relation.TransGen` and `ReflTransGen` provide
   nonempty and reflexive reachability, with `trans`, `single`, `mono` and
   path induction. A Prop-valued adjacency projection is adequate only for
   a reachability observation that deliberately forgets parallel-edge identity.
   The source owner must settle the direction and treatment of the current
   vertex; choosing reflexive closure by convenience would change the claim.
5. `Mathlib.Data.Finset.Union`: `Finset.biUnion` and `mem_biUnion` provide
   finite unions and their membership witnesses.
6. `Mathlib.Data.Finset.Card`: `Finset.card_le_card`, `card_union_le`,
   `Multiset.toFinset_card_le`, and `toFinset_card_of_nodup` distinguish
   unique support from multiplicity.
7. `Mathlib.Algebra.BigOperators.Group.Finset.Basic`:
   `Finset.card_biUnion_le` bounds the cardinality of a finite union by the
   sum of cardinalities; `card_biUnion` gives equality for pairwise disjoint
   families. `Multiset.toFinset_sum_count_eq` recovers total multiplicity
   from support and counts.
8. `Mathlib.Algebra.BigOperators.Group.Finset.Defs`:
   `Multiset.card_sum` states that the cardinality of a finite sum of
   multisets is the sum of cardinalities, via `Multiset.cardHom`.

These are narrow source modules to consider when the first implementation is
scoped; no broad `Mathlib.Tactic` import is needed merely to obtain the above
concepts. The exact minimal import closure remains a compiler question for
that later implementation. `DecidableEq` should be required where finite
support operations need it, rather than strengthening every graph or semantic
interface; classical finite-set proofs remain separate from executable claims.

## Smallest honest additional layer

### Data before laws

Retain an occurrence-level trace carrier and edge identity. A finite list of
operation occurrences supplies chronological multiplicity; a finite quiver or
an edge-occurrence carrier with source/target maps supplies graph incidence.
If operations have several arguments/results, edge metadata must identify the
relevant ports or result occurrences. Object/data-structure identity can be a
label; it must not force the graph to be a disjoint union of single-identity
histories. No ordering/acyclicity law belongs in the raw graph carrier.

This is a proposal about representational capacity, not a declaration that
these are the source's precise node/edge definitions. In particular, do not
identify chronological occurrence, returned value, persistent object identity,
and memory address. The source inspection must determine which occupy graph
vertices and which are labels. It must also explain how permitted cycles
coexist with any chronological or logical ordering used by the debit rules.

Debit annotations can initially use ordinary functions into existing types:
fresh allocations `s : Occurrence → Finset Debit`, discharge and realization
annotations `a r : Occurrence → Multiset Debit`, and unshared unit costs
`u : Occurrence → Nat`. Freshness, origin legality, logical-history discharge
and realization rules should be separately named predicates/theorems. They
must come from the inspected source definitions, not be invented to make the
aggregate theorem automatic. A global fresh-tag construction can later
discharge freshness for a concrete realization; it must preserve its actual
allocation identities.

There is no need for a giant law-bearing typeclass bundling graphs, evaluators,
potentials, costs and correctness. Two focused layers—history/annotation data
and debit-accounting laws—would expose the missing obligations while leaving
existing `Resources` operations intact. Tentative locations are
`Applications/Resources/PersistentHistory.lean` and a small debit-accounting
module, with connected cases in `Examples`; naming and splitting are still
root's implementation decision.

### The reusable cardinality argument

For a finite collection `U` of operation **occurrences**, define the support
observations

\[
 R_U=\bigcup_{v\in U}\operatorname{support}(r(v)),\qquad
 A_U=\bigcup_{v\in U}\operatorname{support}(a(v)).
\]

The algebraic helper should establish, from a proved support inclusion,

\[
 |R_U|\le |A_U|\le\sum_{v\in U}|a(v)|.
\]

The first step uses `Finset.card_le_card`; the second combines
`Finset.card_biUnion_le` with `Multiset.toFinset_card_le` pointwise. The
sum on the right keeps every discharge occurrence. Equivalently it is the
cardinality of the multiset sum, by `Multiset.card_sum`. These steps do not
need graph acyclicity or a topological sort.

**This support inclusion is not the source theorem's premise to assume away.**
The substantive source proof must derive it from fresh allocation and the
actual logical-history discharge/realization conditions. That derivation may
need closure of the selected trace under logical history. For a subtrace
whose relevant charges lie before its boundary, retain a boundary multiset or
an explicit initial-debit term rather than silently asserting that all
discharges occur inside `U`.

Only after an operational/refinement theorem identifies actual work with the
appropriate unshared cost plus shared realized support may one conclude

\[
 C_{\mathrm{actual}}(U)
 \le \sum_{v\in U}\bigl(u(v)+|a(v)|\bigr)
\]

with any required boundary term. The source owner must establish whether the
first comparison is an equality or a bound and which cost units it covers.
Defining an observation to be this right-hand side is not a proof about the
actual evaluator. Unit-cost counting is a useful first theorem; weighted
versions should add explicit nonnegative unit weights only when a client
needs them, preserving the separation from host runtime performance.

### Composition must respect the observation algebra

Ordered events can project to discharge multisets using an additive map;
their cardinalities then use `Multiset.cardHom`. This fits
`Resources.reweight_run` directly and preserves repeated charges.

Unique realized support cardinality is different: observing `[d]` twice gives
individual cardinalities1+1 but union cardinality1. It is not an additive
homomorphism to `Nat`. Do not assert a `reweight_run` equation for it or add
an inappropriate global additive instance on `Finset`.

One concrete operational adapter can retain a `seen` support in the existing
global state, charge only new realized identities, and prove that the actual
sum of these incremental charges equals final-support minus initial-support
in a subtraction-free form. This is an adapter/proof obligation, not a new
executor. The simpler finite-union theorem does not require implementing this
adapter first, but the full source cost connection cannot omit it or an
equivalent established argument.

## Discriminating connected cases for a later implementation

These are proposed mathematical cases, not compiled examples in this note.

- **Forked reuse:** two valid branches both mention one previously allocated
  debit `d`; discharging it on each logical branch counts two multiset
  occurrences, while shared realized support contains `d` once. State and
  prove the actual source legality conditions for both branches. This exposes
  why a single-version potential telescope and deduplicated charges differ
  from the desired accounting.
- **Parallel edges and a cycle:** retain two distinct edge witnesses with
  the same endpoints and a permitted return/self edge. A reachability
  projection may agree, but the raw trace must still distinguish the edge
  occurrences. A cyclic graph is a representation boundary case; it does
  not by itself assert a terminating operational run.
- **Several inputs/results and identities:** a recorded operation consumes
  handles from two persistent identities and yields two result handles.
  Verify that its incidence and logical history are not reduced to one
  predecessor or one per-identity list.
- **Missing-history boundary:** select only a realizing occurrence while
  its discharging predecessor lies outside the selected subtrace. With one
  realized token and no local charge, the zero-boundary aggregate inequality
  fails. This requires a closure premise or explicit initial credit/debit
  boundary, not a proof repair by dropping the example.
- **Identity versus equal body/value:** two freshly allocated equal-body
  suspensions remain separate cost identities; repeated force of the same
  suspension shares its successful cached result. Existing3dd source cases
  are operational inputs, but the debit annotation correspondence still
  needs proof.
- **Exceptional retry:** repeated failed body attempts with zero successful
  cache writes must remain visible in actual work. Either account for that
  work separately or prove the relevant success/totality restriction for a
  particular algorithm; the cache-write theorem cannot erase it.
- **Positive composition case:** derive a debit observation from an actual
  finite suspension trace, use `traced_evaluates_observe`/`workload_append`
  for the same full answer and exact events, then apply the proved accounting
  laws. This is the needed cross-domain use of the new layer.

## Scope decision left to root

An algorithm-independent cardinality/history foundation is mathematically
separable from implementing queues or numerical structures. The existing
resources and ordinary Mathlib interfaces suffice for its execution and
finite combinatorics. The missing source definitions, logical-history
legality proof, debit-to-work correspondence and connected examples are real
work; this inventory does not establish them or authorize changing10017's
dependencies. Complete TU.TRACE acceptance must still cover its full source
scope, all explicit assumptions, the intended operational cost connection,
and the project's exact-candidate build/audit and independent review gates.
