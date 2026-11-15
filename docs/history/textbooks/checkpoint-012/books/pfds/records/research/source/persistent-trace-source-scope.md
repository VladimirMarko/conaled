# Persistent traces and debit accounting: source scope for local10017

Prepared 2026-11-03 by `/root/persistent_trace_scope`. This is a bounded
source investigation and planning note. It is not implementation, independent
formal review, a proof, a ticket activation, or an acceptance decision.
Chapter1 remains accepted, Chapter2 remains earliest unaccepted, and later
chapter algorithms have not been implemented by this task. Existing10017
dependencies and every frozen candidate remain unchanged.

## Sources checked

The supplied Cambridge digital-print book has SHA256
`b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`;
the 1996 thesis has SHA256
`f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`.
These are the existing identities recorded in `union-source-identities.json`.
Physical one-based PDF page is printed Arabic page plus12 in both files.

| Material | Thesis | Book |
| --- | --- | --- |
| Execution traces and logical time |3.2.1, printed19-20 / PDF31-32|6.1, printed57-58 / PDF69-70|
| Memoization motivation |3.3.1, printed20-21 / PDF32-33|6.2.1, printed59 / PDF71|
| Shared/unshared work and debt |3.3.2, printed21-22 / PDF33-34|6.2.2, printed59-61 / PDF71-73|
| Debit placement and method |3.4, printed23 / PDF35|6.3, printed61-62 / PDF73-74|
| Exact set/multiset justification |3.4.1, printed23-24 / PDF35-36|6.3.1, printed62-63 / PDF74-75|

All listed passages were inspected in extracted text. The decisive graph
definitions on thesis19-20 and book57-58 and all three formula conditions on
thesis24 and book63 were also checked on rendered page images. The two sources
agree on this abstract framework. This pass does not inspect the subsequent
queue analyses or the whole of Chapters4-6.

## 1. The graph represents operations and dependency occurrences

An execution trace has operation nodes. An edge from `u` to `v` says that `v`
uses a result of `u`. It is not a graph whose nodes must be versions of one
object. A node can take several arguments, return several results, or perform
a query returning no new persistent version. A trace can combine several
persistent identities and data types. The sources explicitly allow unrestricted
in-degree and out-degree, directed cycles from recursive definitions, and
parallel edges such as two uses of the same list as catenation arguments.
[Thesis19-20; book57-58.]

Consequently, a DAG, rooted tree, single-version path, or simple graph alone
would narrow the requested source model. For example, two distinct argument
edges `u -> v` must remain representable even though they have the same
endpoints. Reachability may subsequently forget their multiplicity; the
operation representation must not silently erase it.

Write `H(v)` for logical history. The source definition is

\[
H(v)=\{w\mid w\text{ reaches }v\text{ by a possibly zero-length path}\}.
\]

Thus `v` belongs to its own history. An edge `u -> v` implies
`H(u) ⊆ H(v)`, and reachability is transitive. In a directed cycle distinct
nodes can belong to each other's history. Antisymmetry and strict chronological
precedence are not part of this definition. [Thesis19; book57.]

A logical future is a path from a node to a terminal node, where terminal
means no outgoing edge. No source requirement says every node has a terminal
successor. A component consisting only of a directed cycle can have none.
The aggregate cost argument does not enumerate logical futures or require
their number to be finite. If a realization uses finite walks that retain
repeated vertices, a cycle with an exit can generate arbitrarily many such
future walks; that is a consequence of that explicit path convention, not a
separate numerical theorem asserted by the source. Keep path conventions
visible if future-counting results are added. Book Exercise6.1 on p58 gives
an acyclic connected example for its later chapter owner; this note does not
close that exercise.

## 2. Exact debit labels and conditions

Let `D` be debit identities. In a finite accounting specialization, each node
`v` has an allocation set `s(v)` and finite discharge and realization multisets
`a(v)` and `r(v)`; finite allocation sets additionally support the natural-number
formula for total shared work. The sources say sets and multisets, without
requiring a finite universe of debit identities or ruling out infinite lazy
structures. The support inclusions themselves need no finiteness of allocation
sets; cardinality statements must expose their actual finiteness premises. A debit
denotes a constant unit of suspended work. It need not denote an entire
suspension: a suspension with many work units has many debits, and incremental
work can distribute them among partial results. Creation itself contributes
no debit-discharge charge. [Thesis23-24; book61-63.]

Writing `supp` for the set of elements occurring in a multiset, the printed
conditions are exactly:

\[
\begin{aligned}
\mathrm{I}:\quad &u\ne v\implies s(u)\cap s(v)=\varnothing,\\
\mathrm{II}:\quad &\operatorname{supp}(a(v))
 \subseteq\bigcup_{w\in H(v)}s(w),\\
\mathrm{III}:\quad &\operatorname{supp}(r(v))
 \subseteq\bigcup_{w\in H(v)}\operatorname{supp}(a(w)).
\end{aligned}
\]

Both inclusions ignore multiplicity. They are not multiset inequalities.
Fresh allocation is global across distinct operation nodes; it is not merely
freshness within one label. Duplicate discharge or realization occurrences
within one node are permitted. [Visually checked thesis24/PDF36 and
book63/PDF75.]

These conditions retain distinct roles:

- I supplies unique allocation provenance and prevents identifying independently
  created work merely because its code or result agrees.
- II requires discharge to refer to work allocated in the operation's logical
  history. It excludes invented debits.
- III requires each realized debit to have a discharge in that logical history.
  It prevents two incomparable futures from each paying part of a debt and
  treating their combined payments as locally sufficient.

Since history is reflexive, the conditions allow a node's own allocation and
discharge to support its own realization. They do not encode the order of
substeps within that operation. With cycles, they also do not define a strict
order between nodes. The surrounding prose's requirement that payment precede
forcing therefore needs an execution correspondence, beyond these final graph
labels, when used as a claim about operational timing.

## 3. The finite aggregate theorem and its actual hypotheses

For a finite accounted node set `V`, define

\[
R_V=\bigcup_{v\in V}\operatorname{supp}(r(v)),\qquad
A_V=\bigcup_{v\in V}\operatorname{supp}(a(v)).
\]

On a complete finite trace, III implies `R_V ⊆ A_V`: a realization at `v`
has a discharge witness `w` in its logical history, and `w` is also a node
of that trace. Finite-set union and multiset support then give

\[
|R_V|\le |A_V|
 \le\sum_{v\in V}|\operatorname{supp}(a(v))|
 \le\sum_{v\in V}|a(v)|.
\]

This spells out the two inequalities printed on thesis24 and book63. The
numerical bound itself needs III and a finite scope containing its discharge
witnesses. It does not need acyclicity, unique allocation, conditionII, or an
ordering of all operations. Those omitted hypotheses still belong to the full
source accounting discipline; their absence from this one proof is not a
reason to drop them from local10017.

For a finite subset of a larger graph, the exact sufficient condition is:
every debit in `r(v)` for `v` in the subset has a supporting discharge `a(w)`
at a node `w` in that subset. History closure plus globalIII is one sufficient
way to obtain it. Merely selecting a chronological prefix of node names is
not sufficient without a proved connection between that prefix and the labels.
No finite-type assumption on the universe of all possible operation names is
mathematically necessary; a finite accounted scope suffices.

Other useful consequences of the complete source conditions are separate:

- I identifies the cardinality of all allocated debits with
  `Σ v, |s(v)|`, the source's total shared cost.
- II and III, using transitivity of history, give an allocation origin in
  `H(v)` for every debit realized at `v`; I makes that origin unique.
- Realized debits are consequently among allocated debits. The unallocated
  complement must not be counted as unrealized work. Within the finite allocated
  set, realized and unrealized debits partition the total shared work.

Let `u(v)` denote unshared cost. The abstract source charges are

\[
\text{memoized work}=\sum_v u(v)+|R_V|,\qquad
\text{amortized charge}=\sum_v u(v)+\sum_v|a(v)|.
\]

Adding the same unshared total to the cardinality theorem proves their
inequality. To use it for an actual measured execution `C`, prove an independent
realization contract such as `C ≤ Σ u(v) + |R_V|`, or the exact equality of the
idealized source cost convention. Defining actual execution cost to equal the
right-hand side would not establish that contract. Unit-cost scaling or weighted
debits likewise require explicit compatibility with the chosen observations.
[Source cost decomposition: thesis21-24; book60-63.]

## 4. Required boundary specializations

These are mathematical examples for a future checked development, not Lean
proofs supplied by this note.

| Case | Labels / graph | What it separates |
| --- | --- | --- |
| Parallel argument use | Two distinct edges `p -> c`; `s(p)={d}`, `a(c)=[d,d]`, `r(c)=[d,d]`, other labels empty | A realization support of size1 versus discharge cardinality2; graph edge multiplicity and multiset multiplicity are both retained. |
| Repeated forcing after shared payment | Edges `p -> l`, `p -> r`; `s(p)={d}`, `a(p)=[d]`, `r(l)=r(r)=[d]` | I-III hold, realized support has size1 and discharge cost1, but realization multiplicities sum to2. The latter is not bounded by the discharge total. |
| Incomparable partial payments | Edges `p -> l`, `p -> r`; `s(p)={d,e}`, `a(l)=[d]`, `a(r)=[e]`, `r(l)=[d,e]` | Global discharge coverage holds, but III at `l` fails because `r` is not in `H(l)`. Global budget sufficiency does not imply the source's local discipline. |
| Cyclic prefix boundary | Edges `u -> v`, `v -> u`; `s(u)={d}`, `a(v)=[d]`, `r(u)=[d]` | The complete graph satisfies I-III and the bound1≤1. The selected scope `{u}` has realized1/discharged0. A prefix theorem needs its own validity premise. |
| Invented debit | One node, empty allocation, `a(v)=r(v)=[d]` | III and the numerical inequality hold, while II fails and the purported shared-work partition is false. |
| Duplicate allocation identity | Distinct allocations both named `d` | I fails; equal bodies or equal values must not justify treating two distinct work allocations as one memoized unit. |
| Cyclic component without terminal nodes | A self-loop with all labels empty | Histories exist and include the node, while no terminal logical future is required; the aggregate bound still makes sense. |

The repeated-forcing row is also the source's call-by-name boundary in precise
finite form: when actual work counts repeated realizations instead of their
union, I-III alone provide no required bound. [Thesis24 remark; book63 remark.]

## 5. Dependencies on current conaled work

The graph and finite set/multiset argument is independent mathematics. Its
proof does not need completed Chapter4 or Chapter5 algorithms, or a suspension
evaluator. It can therefore be developed as a bounded cross-cutting foundation
without accepting later chapters. This conclusion is about logical dependency;
it does not change the existing local ticket's acceptance dependencies.

The eventual operational use has substantial additional premises:

1. Match operation nodes, repeated argument edges and logical histories to
   actual source clients, while preserving cycles, several identities and
   multiple results.
2. Assign globally distinct debit identities to shared work, with a justified
   decomposition of unshared work, newly suspended work and its realized part.
   The source attributes deferred work to the operation that created it.
   The printed claim that an operation contributes between its unshared and
   complete costs must not be mistaken for a bound on wall-clock work performed
   between that operation's call and return; forcing older work can be costly.
3. Prove the labels' local conditions and the actual-cost realization contract.
   In particular, preserve the distinction between a repeated force/hit and
   repeated execution of an uncached body.

The inspected local interfaces support, but do not discharge, these bridges.
`Applications/Resources/Workload.lean` executes actual measured state transitions
and composes/reweights their observations. `Applications/Resources/Potential.lean`
telescopes charges along that same trajectory with explicit boundary potential.
It does not already provide the arbitrary persistent dependency graph or the
debit union argument. Keep the existing executor and its trace observations;
deduplicating debit identities is a separate global observation, not ordinary
addition of per-operation natural-number realization counts.

At current unaccepted candidate
`3dd930c3e3989f3e5530463f3ac937a629551335`,
`Suspensions.Pure.Simulation.source_cacheWrites_le_one` bounds successful
cache-write events in every observed budget of an admitted finite pure source
run. It does not bound body attempts or measured body work. The existing
`Examples.SuspensionPureCacheCounts.Exceptions.two_attempts_without_write`
has two body entries and zero writes/hits, even though the whole handled source
program returns a value. Thus10020 alone cannot justify counting all work of
every pure suspension once. An actual-cost bridge needs suitable successful
memoization/work-accounting conditions for the represented algorithms, or a
separately proved accounting treatment of exceptional attempts. No exception
case may silently disappear from the general source model.

This was checked against `Applications/Suspensions/Pure/CacheCounts.lean`,
`Examples/SuspensionPureCacheCounts.lean`, and `docs/research/pfds-cache-counts.md`
in that exact frozen candidate. No compilation or new theorem validation was
performed. Chapter4's evaluation/demand correspondences and Chapter5's classical
methods/failure examples remain independent chapter obligations. Their source
motivation is useful, but their full acceptance is not a logical prerequisite
of the bare graph/cardinality lemma. Their execution and cost contracts may be
prerequisites of the concrete operational bridge.

## 6. Recommended bounded scope, without activation

An initial cross-cutting task can cover an unrestricted directed multigraph
realization with finite accounting scopes, reflexive logical history, I-III as separate label laws, their
allocation/provenance consequences, the exact union-versus-discharge bound,
and the boundary specializations above. Its public conclusion should identify
its abstract costs and expose any measured-execution bridge as a separate
proved compatibility law. It must not claim that a graph/cardinality result
already establishes algorithmic runtime or all of `TU.TRACE`.

The root's proposed raw `Quiver` plus reflexive finite `Path` interface fits
this source level: distinct arrows can represent distinct uses of results,
including parallel argument occurrences. The printed graph definition does
not require typed input/output port fields. Conversely, raw arrows alone do
not prove that a concrete source result is passed to a particular argument;
that correspondence remains in the operational bridge. Vertex identities
denote operation occurrences, not reusable function names or operation kinds.

An explicit helper using unchanged `Resources.run` can maintain a finite set
`seen`, charge the unshared work plus the cardinality of `supp(r(v))` minus
`seen` as a set difference, and add `supp(r(v))` to `seen`.
Its proposed subtraction-free accounting identity is

\[
C_{\mathrm{run}}+|\mathrm{seen}_0|
=\sum_{v\text{ in the operation list}}u(v)
 +|\mathrm{seen}_0\cup R_{\mathrm{list}}|.
\]

This is a defined interpreter of the abstract debit observation, not yet a
claim about arbitrary suspension-machine body work. The list sum counts every
occurrence. To identify it with the source's finite-node sum, use an exact
duplicate-free enumeration of the accounted operation nodes, or keep all
charges explicitly multiplicity-counted. Reusing a vertex in that list does
not by itself model two distinct source operation occurrences. An injective
renaming of debit identities is also a suitable transport obligation: it
preserves distinct allocations and support/cardinality observations, unlike
the noninjective identification of equal bodies at different allocations.

Retain local10017's full source coverage and its existing dependencies until
the root explicitly records any justified subdivision. Its eventual completion
still needs the required source/measurement correspondences, connected
specializations, both independent review axes and the exact candidate gates.
No new ticket, dependency change, source row completion, or chapter acceptance
is made by this note.
