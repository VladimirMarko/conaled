# Local10021 — persistent history and debit accounting foundation

Version1, 2026-11-03. This is a bounded cross-cutting implementation scope
under the user's explicit exception for shared concerns. It supports10017
and the later persistent-amortization chapters. Chapter2 remains the earliest
unaccepted chapter. No later chapter algorithm or forward cost contract is
accepted by completing this foundation.

## Source and baseline

Governing requests: `REQUEST.md` and `REQUEST-union-v2.md`. Source evidence:
`research/persistent-trace-source-scope.md` (thesis printed19–24/PDF31–36;
book printed57–63/PDF69–75) and `research/persistent-trace-reuse.md`.
Both exact manuscript identities remain in `union-source-identities.json`.
The source graph definitions and conditions I–III were visually inspected.

Starting state: clean `persistent-accounting`, branch
`pfds/persistent-accounting`, at
`3dd930c3e3989f3e5530463f3ac937a629551335`. The bounded and original integration
review bases are this exact commit. No pre-existing task changes or unrelated
exclusions. The inactive clean10020 development materialization was moved;
its old branch and all history remain at3dd, and the immutable10020 candidate
in `validation-cache-counts` is unchanged. See the recorded baseline.

Local10017 retains its existing Chapter4/5 dependencies and complete
source/actual-work correspondence requirements. Add10021 as a prerequisite
without closing TU.TRACE. The abstract graph/cardinality argument is independent
of those algorithms; this is the justification for the bounded subdivision.
10021 inherits the unaccepted10020 source base and cannot be accepted before
the applicable integration/dependency gates are satisfied.

## Intended mathematics and public interface

Reuse ordinary Mathlib `Quiver` and `Quiver.Path`: vertices identify operation
occurrences, and distinct arrows can identify distinct result-to-argument uses.
Retain loops, cycles, parallel edges, several inputs/results and histories
crossing persistent identities. Do not impose acyclicity, thinness, one
predecessor, a single persistent identity or a finite universe of all vertices.
Concrete source incidence extraction remains10017.

Logical history of v is the set of u with a possibly empty finite path u→v.
Prove reflexivity, path/edge inclusion and transitivity. A finite accounted
scope is history-closed when it contains every logical predecessor of each
of its members. Expose this separately from raw graph data. Elementary closure
and ordinary graph-map transport should reuse Mathlib interfaces where needed;
do not build a parallel graph library. No antisymmetry or chronological
substep-order conclusion follows from history membership.

Use allocation sets `s : V → Set D`, discharge multisets `a : V → Multiset D`
and realization multisets `r : V → Multiset D`. Allocation sets need not be
finite for support/provenance claims. Finite support operations may require
decidable debit equality; graph and source-law definitions should not inherit
that requirement unnecessarily. Keep data and source laws separate:

1. I: distinct operation occurrences allocate disjoint debit sets.
2. II: every debit discharged at v was allocated at some u in v's history.
3. III: every debit realized at v was discharged at some u in v's history.

II and III are support-membership conditions, not multiset inequalities.
Self-history permits allocation/discharge/realization in the same node.
Retain separate predicates and optionally a small proposition bundling the
three laws. Prove realized allocation provenance from II+III using history
transitivity, and uniqueness of the allocating occurrence from I. A source
law must not be replaced by the desired global cost inequality.

For finite scope S, let R be the finite union of supports r(v), and A the
finite union of supports a(v), over v∈S. Derive R⊆A from III and history closure
(or an explicitly named local discharge-witness premise); then prove

    R.card ≤ A.card ≤ ∑ v∈S, (a v).card.

Use existing finite-union and multiset cardinality lemmas. No disjointness of
discharges or realizations is assumed. Preserve the stronger local law III
even though global support inclusion alone would suffice for the numerical
helper. For an open scope, support a finite boundary set of already discharged
debits with the explicit witness condition and bound its cardinality separately.
Do not confuse this boundary with a set of already realized/cached work.

For finite allocation labels, specialize the general set laws: prove that
fresh allocation makes the cardinality of their finite union equal the sum
of their cardinalities; derive realized-support inclusion in allocated support;
and partition allocated support into realized and unrealized parts. Require
only the laws each conclusion actually needs. An unallocated complement is
not unrealized allocated work.

Provide injective debit-renaming transport using ordinary embeddings, set
images, multiset maps and finite-set maps. Preserve freshness, provenance,
paid-realization laws and support/cardinality observations. Noninjective
identification of independently allocated equal-body work must not acquire
the same conclusion.

## Connection to the existing measured executor

Keep `Resources.Measured`, `Resources.Workload` and `Resources.Potential`
unchanged unless an actual necessary compatibility gap is separately justified.
Use the existing `Resources.run`; do not introduce a competing executor.

Define a small interpreter of debit observations. Its state is a finite set
`seen`; processing operation occurrence v unions `support(r(v))` into seen
and charges `u(v) + card(support(r(v)) \ seen)`, where u(v) is its unshared
unit charge. Derive the state observation and the subtraction-free identity

    runCost + initialSeen.card
      = listSum(unshared) + finalSeen.card.

For empty initialSeen, identify finalSeen with the union of realized support.
Connect the generic source accounting theorem to this same measured run. The
run's list sum counts occurrences: translating to a finite-node sum requires
an exact duplicate-free enumeration, or charges must remain explicitly
multiplicity-counted. Preserve initial-state and boundary terms. Composition
uses existing run_append rather than a separately invented trajectory.

This is an interpreter of the abstract debit observation. It does not yet
identify arbitrary suspension-machine body work with distinct debit support.
Unique support cardinality is not an additive map from ordered events to Nat;
do not manufacture a global Finset additive instance or a false reweighting
equation. Discharge multiplicities do admit the existing additive observation
and cardinality machinery.

## Checked specializations and statement review

Develop each theory layer with meaningful connected cases. Independently
justified expectations must survive proof repairs. Existing cases may serve
several helper lemmas; no theorem-count quota applies.

- Parallel argument edges remain distinct, while history can forget their
  multiplicity. A source-valid label example has discharge/realization
  multiplicities2 and realized support1.
- A fork with one prior discharge and two later realizations satisfies I–III:
  distinct realized support1 is paid by1, while summed realization multiplicity2
  is not bounded by1. This exposes the call-by-name boundary.
- Incomparable partial payments can cover all debits globally while failing
  III at the realizing branch; do not infer local legality from global totals.
- The two-node cycle u↔v, allocation at u, discharge at v and realization at u,
  satisfies complete I–III. Its full scope has1≤1; the open scope{u} has1>0.
  Connect full, history-closed and explicit-boundary theorems to these cases.
- An invented debit can satisfy III while failing II; duplicate allocation
  identity fails I. Both source laws must remain nonvacuous and separate.
- The measured interpreter must have a shared-reuse run, an initial-seen case
  and a composition case using the public run theorem. Demonstrate the
  enumeration/multiplicity boundary explicitly where it matters.
- Preserve the existing actual-source exception/retry boundary from
  `Examples.SuspensionPureCacheCounts.Exceptions.two_attempts_without_write`:
  two body attempts and zero successful writes are compatible with a returned
  value. A checked connection or public theorem reuse should make clear that
  one-write-per-address does not justify deduplicating arbitrary body work.
- At least one positive application must compose the new accounting result
  with the existing measured-run infrastructure, and renaming must be exercised
  by an injective concrete or generic specialization.

Statement review checks all quantifiers, finite scopes, support versus
multiplicity, occurrence identity, admissibility and boundary premises. The
source's logical graph laws are not a proof of chronological payment-before-force
in a concrete evaluator. Every claimed source/target compatibility must state
and prove that additional relation; the full relation remains10017 here.

## Completion and retained boundaries

Integrate new core and connected client modules through SquareApplications.
Keep application-facing documentation focused on the public APIs and their
limits; retain source correspondence, cases and statement review in the
implementation report. Do not import unrelated historical formalizations.

No new axioms, admissions, unsafe proof shortcuts, native-decide substitutes,
proof-budget increases, blanket linter suppression or gate weakening.
Focused checks are development evidence only, with exact stable input hashes
and retained failures. Freeze a clean isolated final candidate; run the stock
pinned-Nix complete candidate check and exhaustive audit, preserve the matching
verification record, obtain both independent full-scope Standards and Spec
outcomes in one retained loop, and perform immediate final candidate verification
before acceptance of identical bytes. Preserve all work and local tracking in
uploaded recovery checkpoints. Neither10017 nor any later chapter or forward
cost contract closes solely because this bounded foundation passes.
