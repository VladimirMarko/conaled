# Unary theory interaction and exact open-system hiding

Research and checked comparisons for [#364](https://github.com/VladimirMarko/conaled/issues/364),
2026-11-08. This follows the [#362 disposition](disposition.md).

Two bounded alternatives derive composition from local structure. Unary
interchange admits a block representation of arbitrarily interleaved operation
words. Equality-wire cospans admit a boundary partition after internal nodes
are hidden. Both agree with the existing semantic interfaces on their stated
fragments. Neither subsumes arbitrary guarded theories or arbitrary constraints.
A stronger observation can invalidate the proposed quotient without invalidating
the weaker existential semantics.

## Independent unary presentations and guarded admission

[UnaryInteraction](../../../SquareKit/UnaryInteraction.lean) defines a presentation
by a set of unary symbols and equations between finite words. These equations
are independent of guarded rule syntax. A word acts from the right: `[s,t]`
means `s(t(x))`. The common presentation uses the disjoint union of symbol sets.
`union` includes each theory's own equations; `tensor` additionally includes
`[left s,right t]=[right t,left s]` for every pair of generators.

The terminology is bounded. Hyland, Plotkin and Power define sums of countable
Lawvere theories by the categorical coproduct and tensors by the universal
commuting combination. Their Set-based tensor presentation adds all
cross-theory commutation equations (Definition 5, §4). Our unary equation
presentation implements that generating equation scheme; it does not construct
the complete Lawvere category or prove its universal property. In particular,
we have not built enriched effects or a general monad transformer. A
distributive law is a different construction with coherence requirements;
§3 distinguishes the endofunctor-over-monad variant from the usual
monad-over-monad law. We do not claim a distributive law merely from two
operations commuting. [Primary paper](https://www.dpmms.cam.ac.uk/~jmeh1/Research/Publications/2006/hpp06.pdf).

The incumbent route uses `GuardedTheory` directly:

- `term` translates a unary word to a nested unary `FinitaryTerm`.
- `eval_term` proves agreement with the independently defined word semantics.
- `model` constructs `GuardedTheory.Model (guarded P)` from each presentation
  equation's validity. No desired whole-program conclusion is a model field.
- Existing guarded derivation soundness and substitution are then available
  for that model. This experiment does not prove completeness or a reverse
  translation of arbitrary guarded derivations.

The alternative uses a pair of homogeneous blocks `(leftWord,rightWord)`.
`split` retains each side's order while separating the two alphabets.
`normalize_sound` proves that interpretation of the pair equals interpretation
of every mixed word. `interpret_product` derives correctness of componentwise
concatenation. Both use the pairwise operation interchange law through
[CommutingOperations](../../../SquareKit/CommutingOperations.lean), which proves
commutation for arbitrary finite words. `comparison` connects this independent
representation to guarded evaluation. These are semantic equalities on every
input, not observations of a few closed terms.

The block representation is not a canonical normal form modulo each theory's
own equations. It retains repeated generators; it only removes cross-theory
interleaving. It therefore supplies a useful representation and interpretation
comparison without claiming a word-problem algorithm or general completeness.
`interchange_iff_words` also proves necessity: a purported all-word theorem
includes the singleton cases and cannot conceal a failing mixed law.

### Inhabited model and maintenance failure

[Examples.UnaryInteraction](../../../Examples/UnaryInteraction.lean) independently
presents an involution `L(L(x))=x` and an idempotent `R(R(x))=R(x)`.
On `Bool × Bool`, set `L(a,b)=(!a,b)` and `R(a,b)=(a,false)`.
Their own laws and interchange are proved, then used to construct the joint
guarded model. The checked interleaving `L R L` at `(true,true)` produces
`(true,false)` through the general comparison. Arbitrary block composition is
also exercised through the general theorem.

Change only `R` to `R'(a,b)=(a,a)`. It remains idempotent, so the same union
presentation still has a guarded model. But `L(R'(false,false))=(true,false)`
and `R'(L(false,false))=(true,true)`. The changed tensor is rejected, and the
old block normalization changes a selected component. The failure is specific
to this interpretation and commutation contract; it is not nonexistence of all
models of the tensor presentation. Retaining the mixed word and using the sum
is a valid repair when commutation is not required. If commutation is required,
this changed operation must be replaced or its semantic contract revised.

| Obligation | Guarded presentation route | Block representation route |
|---|---|---|
| Setup once | Translate unary words/rules; prove `eval_term`; use existing guarded soundness. | Define `split` and block evaluation; prove normalization and block composition. |
| Per theory | Validate its own word equations. | Same equations when admitting the same theory; block storage does not discharge them. |
| Per operation | Supply its function and its occurrences in own laws. | Same function; no separate whole-word proof. |
| Per interaction | Validate each mixed equation when the theory requires it. | Supply the same pairwise interchange; derive all finite reordering. |
| Copy-left maintenance | Own-law model remains, tensor admission fails. | Old normalization fails on a concrete word; sum semantics remains usable. |

These are proof obligations, not measured author hours or evidence of an
asymptotic productivity advantage. The checked family ranges over arbitrary
symbol types and arbitrary finite words; the concrete models use one generator
per side. General multi-arity tensor models, model amalgamation and
conservativity remain with #288/#290. No broad change to the rule engine follows.

## All solutions before hiding

[OpenConstraint](../../../SquareKit/OpenConstraint.lean) specifies a network by
an internal assignment type and a predicate on input, internal assignment and
output. Its behavior is **all** boundary pairs with an extending assignment.
The definitions allow general types; the retained diagnostic networks use only
finite types. Composition retains both internal assignments and their shared
boundary. `behavior_compose` proves an iff with relational composition.
Associativity and wire identity hold at that full semantic relation.

`composeSquare` constructs an ordinary exact commuting square whose semantic
carrier is the entire relation. It does not replace exactness by forward-only
preservation. This reuses the existing square interface while exposing the
existential calculation rather than requesting composition correctness as a
field. Internal equivalences and boundary permutations preserve the specified
behavior. [Examples.OpenConstraint](../../../Examples/OpenConstraint.lean)
checks two flips, rejection of a disagreeing pair, an inconsistent upstream
network, nonidentity internal and boundary renamings, and ambiguity retained
inside a composite with an identity wire.

## Independent equality-wire black box

[WireCorelation](../../../SquareKit/WireCorelation.lean) starts from a different
presentation: two maps of terminal sets into a node set. A coloring assigns
one value to each node; both terminal maps restrict that assignment. The
alternative boundary specification says a terminal coloring is constant on
every fiber of the map from the disjoint union of the terminals to the nodes.
Thus it is specified directly by the kernel partition of the cospan, without
an internal witness in its predicate.

`exact_blackbox` proves that this partition specification is equivalent to
extendability, provided the value type is nonempty. Its converse constructs
an assignment on all nodes; unused nodes receive an arbitrary default value.
The theorem is classical and noncomputable. It is a semantic comparison,
not an algorithm for enumerating or selecting assignments.

`reduce` replaces the nodes by the image of the terminal map. Its copairing
is surjective, proved by `reduce_surjective`. `compatible_reduce` identifies
the same boundary partition, and `behavior_reduce` derives exact preservation.
Composition forms a quotient of the disjoint node sets, identifying each pair
of images of a shared terminal. `descend` constructs a coloring from locally
agreeing colorings; `descend_unique` proves its uniqueness from the two
coprojections. `behavior_compose` uses this quotient construction to derive
exact relational composition. `reduced_composition` then proves agreement of
image-after-pushout corelation composition with the incumbent network route.
None of these statements takes global black-box functoriality as a hypothesis.

Fong's general construction requires finite colimits and an `(E,M)`
factorization system with `M` stable under pushout. Decorated corelations
add a symmetric lax monoidal functor on `C;Mᵒᵖ` (Theorem 5.8); functor
comparisons require the additional preservation and naturality hypotheses
of Proposition 6.1. For finite sets the epi-mono example uses jointly
surjective cospans and image reduction after pushout. Our checked construction
covers equality wires and their boundary relations, including finite cases.
It does not build the general decorated category, its hypergraph structure,
or arbitrary constraint decorations. Those require their own checked
hypotheses. [Decorated Corelations](https://arxiv.org/pdf/1703.09888),
§§1, 3, 5–6.

[Examples.WireCorelation](../../../Examples/WireCorelation.lean) uses two
terminals joined at one Boolean node plus an orphan node. Its behavior is
equality of the terminal values. Composition through both reductions and the
quotient retains exactly that equality and rejects disagreement. With empty
terminals, one orphan node and an **empty value type**, the unreduced network
has no assignment but its reduction has one. This checked failure shows why
nonemptiness matters to this interpretation; deleting internal nodes is not
unconditionally harmless. It does not contradict the categorical construction
of corelations, which does not itself assert this coloring interpretation.

| Obligation | General relation/square route | Equality-wire corelation route |
|---|---|---|
| Setup once | Existential composition, identities, associativity and exact square. | Kernel compatibility, extension to nodes, image reduction and quotient descent. |
| Per component | Supply its complete constraint predicate. | Supply terminal maps; only equality-wire constraints are represented. |
| Per interaction | Identify the common boundary type and its equality. | Glue terminal images in the quotient; descent derives the joint assignment. |
| Change to empty values | Existential semantics still applies and may be empty. | Image reduction can change behavior; the nonempty-domain theorem is unavailable. |
| Change to nonlinear/general constraints | Predicates still express them; prove the relevant local semantics. | Undecorated partitions are insufficient; specify and validate a decorating structure. |

## Stronger observations and direction

The possibility relation loses internal solution information even on finite
networks. `one` permits only `false` internally; `two` permits both Booleans.
They have the same full boundary relation. `one_unambiguous` and
`two_ambiguous` distinguish existence of two different solutions, and
`no_ambiguity_factor` proves that no observer of the possibility relation alone
can recover that distinction. This is an ambiguity predicate, not a general
cardinality theorem. It proves failure for a stronger multiplicity-sensitive
client without selecting arbitrary representatives or erasing that requirement.

Retain existential hiding for possibility clients. Retain the internal witness
space, or supply a richer interpretation, for selected-solution and
multiplicity clients. #361 still owns partiality, selected dependent solution
behavior, genuine context changes and adequacy; this finite counterexample
discharges none of those obligations. #288 owns interaction and model
combination; #290 owns reusable theory transport; #235 retains the comparison
with richer black-box formulations when a consumer supplies the decoration.

Institutions can publish admitted equations and interpretation contracts;
shared meaning can compare the word and block routes. Neither interface
creates a missing mixed law or reconstructs a discarded solution. The
orbifold consumer likewise needs selected maps and gluing data, but these
finite wire and unary results do not provide its higher smooth model. Keep
these as independently motivated comparisons, without forcing every model
into a single maximal interface.

## Validation boundary

All new formal results and cases are imported by `SquareApplications` and are
subject to the normal build and exhaustive proof audit. The primary-paper
statements above are research context, not claimed local formalizations.
The implementation handoff records exact candidate validation and statement
review. This is an informed construction comparison, not a fresh-author trial.
