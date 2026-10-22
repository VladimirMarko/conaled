# Optimization specifications and transport across interpretations

Research for [#110](https://github.com/VladimirMarko/conaled/issues/110),
2026-10-22. Local inspection baseline:
`be36b9b10e3d6088f8814b619844ebf6bf11e9bc`.

The useful common construction is a mathematical specification of admissible
alternatives and their objectives, followed by laws for changes of interpretation.
It need not be computable. Optimizers and cost analyses are realizations of
that specification with separate contracts. Ordinary semantic preservation
supplies neither cost preservation nor preservation of optimal choices.

**Evidence status:** the arguments and numerical cases below are mathematical
research derivations, not new checked Lean theorems. Existing declarations are
identified by file and name. No runtime measurements or new compiler are
reported. Proposed interfaces and integrations remain proposals.

## Specification before selection

Let `P` be a type of programs, `W` a type of workloads, and `K` a preordered
cost type. A workload can include inputs, update sequences, observation points,
and machine parameters. For a fixed reference program `p`, take:

```text
A p : Set P                 admissible alternatives
J   : P → W → K             objective
Opt A J p w = {q | q ∈ A p ∧ ∀ r ∈ A p, J q w ≤ J r w}
```

Semantic equivalence can define `A p`, but a refinement relation or a restricted
search space can also do so. State the choice: all equivalent programs, all
programs in a grammar, and all candidates discovered by a search are different
specifications. For correctness over every input, semantic admissibility must
quantify over every permitted input even when the objective concerns one
workload. Optimizing each `w` separately does not produce a single optimizer
valid uniformly without making `w` available to its choice.

In a complete lattice, define the optimal value by
`V A J p w = sInf {J q w | q ∈ A p}`. It exists even when no minimizer exists.
For nonnegative extended real costs, an empty admissible set has value infinity;
a nonempty set whose only costs are infinity can have minimizers. Keep
nonemptiness, attainment and finite cost distinct. For real-valued costs use
conditional-completeness hypotheses (nonempty cost set and boundedness below),
or extend the codomain; Lean's total `sInf` notation alone supplies no such
hypotheses.

For the mathematical example `A = {1,2,…}` and `J(n) = 1/n`, the infimum is
zero and no minimizer exists. A selector must therefore be partial or accept
an attainment proof. Classical choice can select from nonempty `Opt` without
providing an algorithm. In a partial order, the displayed `Opt` asks for a
least cost, not merely a Pareto-minimal cost: `{(1,2),(2,1)}` under componentwise
order has two nondominated alternatives and no least one. Use a separately
specified Pareto frontier if that is the desired observation.

These definitions can use Mathlib's existing `Set`, `IsLeast`, `IsMinOn`,
`CompleteLattice`, `OrderEmbedding`, and `OrderIso` rather than a new order
hierarchy. Relevant pinned source: [bounds definitions][bounds],
[extrema][extrema], and [complete lattices][lattices]. The particular `Opt`
and transport results in this note are not existing conaled declarations.

## Pullback and optimization transport

For `C : P → Q` and `J : Q → W → K`, define
`C* J p w = J (C p) w`. No enumeration or execution is part of this definition.
For `D : Q → R`:

```text
id* J = J
(D ∘ C)* J = C* (D* J)
```

Both equations follow by application to `p,w` and function composition.
A target requirement `H : Q → Prop` pulls back to `H ∘ C` in the same way.
Neither construction inverts `C` or chooses an optimal program. If workloads
also change, supply `e : Wsource → Wtarget` and use `J (C p) (e w)`;
composite workload maps must be composed too.

A worked two-stage case is a typed arithmetic term `p`, a lowering `C` to an
instruction sequence, and an interpretation `D` of that sequence on a specified
machine model. For the mathematical target objective
`J(m,w) = work of m on w`, the source objective is exactly
`J(D(C(p)),w)`. This is meaningful even if `D` or `J` is noncomputable. Calling
it an operation count instead requires a theorem connecting the machine's work
to an instruction-cost interpretation. The current stack correctness theorem
preserves values; it does not supply that theorem.

Admissibility can be pulled back as a relation:
`A_P(p,q) := A_Q(C p,C q)`. When source admissibility is independently chosen,
prove `A_P(p,q) → A_Q(C p,C q)` instead. Reflection is an additional property;
a compiler that identifies source distinctions need not reflect them.
For equivalence-induced admissibility, this matches the distinction between
`RawMap.induced`, `MapLaws.congr`, and `RawMap.Reflects` in
[CategoryMap.lean](../../SquareKit/CategoryMap.lean).

Here is a sufficient optimality-transport result. Fix `p,w`, write source
admissibles as `A`, target admissibles as `B`, and suppress `w`. Suppose:

1. `C(A) ⊆ B`.
2. `c : P → K`, `J : Q → L`, and `h : K → L` is monotone, with
   `J(C q) = h(c q)` for every `q ∈ A`.
3. Every `t ∈ B` has a `q ∈ A` with `J(C q) ≤ J(t)`.

If `q₀` minimizes `c` on `A`, then `C q₀` minimizes `J` on `B`.
For any `t ∈ B`, choose its witness `q`. Then
`J(C q₀) = h(c q₀) ≤ h(c q) = J(C q) ≤ J(t)`.
The first hypothesis supplies admissibility. No computability or injectivity
is needed. Surjectivity from `A` onto `B` suffices for hypothesis 3, but is
stronger than necessary. Without 3 the same argument establishes optimality
only over compiled source alternatives.

If `h` is also order-reflecting, minimization among image alternatives reflects
back to source minimization. A merely monotone `h` can collapse distinct costs,
so reflected optimality does not follow. Transporting optimal *values* through
`h` requires preservation of the relevant infimum in addition to monotonicity.
For example, on nonnegative reals `h(0)=0` and `h(x)=1` for `x>0` is monotone,
but for `{1/n | n≥1}`, `h(inf)=0` while `inf(h(image))=1`.
An order isomorphism between complete lattices preserves all infima; a general
order embedding need not.

For program composition, a sufficient restricted principle is independent
alternatives `A×B` and composite cost `φ(c(a),d(b))`, with `φ` monotone in each
argument. Component minima then minimize composite cost by two applications
of monotonicity. Dynamic programming needs the analogous sufficient boundary
state and optimal-substructure argument. Shared intermediates, representation
conversions and workload changes can invalidate independence or the displayed
cost decomposition. They belong in the mathematical state, not in a hidden
qualification on a greedy algorithm.

### Failures with all semantics preserved

These are constructed mathematical counterexamples, not measured incidents.
Let two programs both return `0`, with source costs `c(a)=1,c(b)=2`. A compiler
can preserve that result while realizing target costs `J(Ca)=100,J(Cb)=1`.
The semantic square commutes; source optimality does not transport. Even exact
cost preservation on the image is insufficient for global target optimality
if an admissible target implementation outside the image has lower cost.

For local choice, let two implementations of a producer return the same abstract
value in representations `R` and `S`. Producer costs are respectively `1` and
`2`. A consumer accepts `S` at cost `0`; converting `R` to `S` costs `100`.
Choosing the locally least producer gives total `101`, while choosing `S`
gives `2`. All decoders agree. The boundary representation must be retained
in the specification of alternatives for a compositional optimum argument.

## One bounded problem, two interpretations

Consider three matrices over an exact semiring, with shapes `a×b`, `b×c`, and
`c×d`. Admissible alternatives are exactly the two fully parenthesized products
`L=(AB)C` and `R=A(BC)`. Associativity supplies semantic equality for all
matrices of these shapes. This excludes floating-point reassociation without
an additional numerical-error contract.

The reused construction is `Opt` over this same two-element admissible set.
Here are two mathematical interpretations of its objective:

| Interpretation | `J(L)` | `J(R)` | Assumptions |
|---|---:|---:|---|
| Scalar multiplication work | `abc+acd` | `bcd+abd` | Ordinary dense multiplication, unit cost per scalar multiplication; additions deliberately excluded. |
| Intermediate matrix storage | `ac` | `bd` | Materialize the first product, release it after the second; count its scalar slots only, excluding inputs, final output and kernel workspace. |

For the example dimensions `(a,b,c,d)=(2,5,20,5)`, the work costs are
`400` and `550`; the intermediate-storage costs are `40` and `25`.
Thus `Opt` selects `L` for work and `R` for intermediate storage. Both minima
exist because the candidate set is finite and nonempty and both objectives
are natural-valued. This establishes exact optimality only among those two
plans under those objectives, not among all matrix algorithms. No execution
or search procedure is needed for this specification-level result.

Counting peak total memory would require the final output and overlapping
lifetimes; counting allocated bytes needs scalar representation sizes. Counting
bit operations over integers requires intermediate bit lengths and arithmetic
algorithms. Parallel depth uses a schedule and reduction-tree heights, not the
sum of scalar multiplication counts. None of these interpretations follows
from semiring associativity alone. A dynamic-programming realization can use
matrix-chain intervals as states for multiplication work; a memory-aware
realization may also need evaluation order and buffer lifetime in its state.

The matrix case is a constructed bounded example, not an attribution to the
unavailable textbook formalization. The general separation of alternatives
from extraction has an established realization in [equality saturation][eqsat]:
the paper represents equivalent programs and applies a separate profitability
criterion for extraction. Finite saturation or extraction over a discovered
set does not prove optimality over every semantically equivalent program.

## Transporting complexity and resource arguments

Functional equality concerns observations. Resource claims require an evaluation
model as well. A compositional resource semantics can pair observations with
resource observations, keeping primitive costs as parameters. It must account
for structural operations too: duplication, environments, allocation and
conversion are not automatically free. [Danner, Licata and Ramyaa][cost] give
a primary example of compositional complexity recurrence extraction for a
higher-order functional language; it is evidence for a method with a specified
language and cost semantics, not a theorem about our compiler.

A useful upper-bound simulation has this form for related inputs `x,y`:

```text
Ttarget(C p,y) ≤ α · Tsource(p,x) + overhead(y)
sizeSource(x) ≤ g(sizeTarget(y))
```

Assume finite nonnegative costs, fixed `α≥0`, a nondecreasing source bound `F`,
`Tsource(p,x)≤F(sizeSource(x))`, and
`overhead(y)≤H(sizeTarget(y))`. Substitution gives
`Ttarget(C p,y)≤α F(g(sizeTarget(y)))+H(sizeTarget(y))`.
Include encoding, decoding and output materialization in `H` if the claim is
end-to-end. Uniform constants and domination of `F∘g` and `H` by a proposed
target bound yield a Big-O upper bound. This yields neither a matching lower
bound nor a speedup. For two stages with bounds
`T₁≤α₁ T₀+H₁` and `T₂≤α₂ T₁+H₂`, substitution yields
`T₂≤α₂α₁ T₀+α₂ H₁+H₂`, with the size maps substituted into each overhead.
Cost equality is the stronger special case with an exact resource equation.

An asymptotic lower bound needs a reverse simulation or independent target
argument. Multiplicative approximation of an optimum needs two-sided cost
comparisons and candidate coverage, not just an upper-bound simulation.
For instance, if `0<a≤b`, target candidates are exactly the compiled source
candidates, and `a c(q)≤J(Cq)≤b c(q)` uniformly, a source minimizer has target
cost at most `(b/a)` times any target candidate. The proof compares it to the
source preimage of that candidate. Dropping the lower inequality removes that
argument.

Evaluation assumptions have concrete consequences:

- For `let z = expensive x in z+z`, an evaluation rule that shares `z` charges
  `expensive` once; substitution without sharing can charge it twice. A lazy
  evaluator can avoid `expensive x` entirely when the body ignores `z`, while
  a strict evaluator evaluates it. Denotational equality alone distinguishes
  neither work model. Launchbury's [natural semantics for lazy evaluation][lazy]
  makes heap sharing explicit; a new cost interpretation must say what it counts.
- The matrix multiplication count above charges a scalar operation as one unit.
  Exact integer multiplication acts on variable-length operands. Transferring
  that count to bit complexity needs bit-length bounds for intermediates and
  costs for the chosen arithmetic implementation.
- Work and parallel depth combine differently: independent computations add
  work but can combine depth by maximum under enough processors and an explicit
  schedule. Memory concerns live state, not only accumulated allocations. A
  cost vector or family of objectives preserves these distinctions.

Amortized arguments can be transported with a potential simulation. For
transitions `sᵢ→sᵢ₊₁`, suppose
`tᵢ+Φ(sᵢ₊₁)-Φ(sᵢ)≤aᵢ` with nonnegative `Φ`. Summation gives
`Σtᵢ≤Σaᵢ+Φ(s₀)-Φ(sₙ)≤Σaᵢ+Φ(s₀)`.
A backend representation must relate potentials or discharge its own inequality,
including conversion and maintenance. This is a sequence bound; an individual
operation can still be expensive. [Cutler, Licata and Danner][credits]
derive amortized recurrences using a language with credit accounting and a
bounding relation, a precedent for transporting resource proofs under explicit
semantics. Any transferred textbook theorem
needs its actual evaluation relation, size measure, potential and dependencies
inspected before this template can be applied.

## Incremental state: point updates to a sum

Use an exact additive commutative group of scalars and a vector `x` of fixed
length `n`. The observation is `sum x`. Patches are sequences of assignments
`(i,v)` with `i<n`, applied in order, so repeated indices are meaningful.
A backend state contains an indexed vector and a cached total `s`, with
invariant `s=sum x`. For each assignment let `old=x[i]`, set `x[i]=v`, and set
`s=s-old+v`. Removing the old summand and adding the new one proves invariant
preservation. Initialization computes the sum; observation returns `s`.
This is a proposed state case with a mathematical invariant proof, not a new
local implementation or an existing speed theorem.

Under a sequential mutable random-access model with constant-time indexed
reads/writes and unit scalar operations, initialization is `O(n)`, a patch of
length `k` costs `O(k)`, scalar observation costs `O(1)`, and retained state is
`O(n)` scalar slots. Across patches of lengths `k₁,…,kₘ` with one observation
after each patch, total work is `O(n+Σkᵢ+m)`. Recomputing the sum after each
patch costs `O(n+Σkᵢ+mn)` in that same model. The update advantage depends on
this workload; it disappears for `m=0` and can disappear when patches are dense.
A persistent balanced tree changes indexed updates to logarithmic cost;
copying an immutable flat array can require linear work per assignment.
Bit costs and persistent-version retention need separate bounds.

Changing the observation to materialize all prefix sums changes the problem.
In a nontrivial scalar group, assign a different value at index zero of a
nonempty vector. Cancellation implies that every prefix changes, so this
one-entry patch affects all n output entries. Returning an explicit new flat
array then requires linear writes in this worst case. A lazy
or compressed output changes when observation costs occur; it does not prove
the same materialization bound. Patch size alone therefore does not bound
affected computation or observation work. Self-adjusting computation explicitly
separates ordinary evaluation, change propagation and their cost analyses.
Ley-Wild, Acar and Fluet give a translation with extensional consistency,
asymptotic from-scratch cost preservation and trace-distance bounds for change
propagation. Their Figure 1 separates the value squares from the resource
relationships. A relational trace-distance specification does not require an
implementation that finds a minimum-distance choice. This is a close primary
precedent for keeping specification and effective selection separate
[A Cost Semantics for Self-Adjusting Computation, §§1–2][selfadjust].

Backend responsibilities are the state carrier, invariant, initialization,
repair and observation operations, and their local semantic/resource laws.
A compiler can compose those operations, retain intermediate states, and prove
an invariant for each composite, provided its target interface exposes the
necessary operations. It can also introduce sharing by a separately justified
transformation. Composing finite-update functions alone does not establish
physical sharing or retention. For a composite `g ∘ f`, a stateful construction
can keep the states of `f` and `g` plus their boundary value; repair `f`, pass its
output change to `g`, and repair `g`. It needs a valid boundary-change contract
and must charge boundary conversion, maintenance and observation. This is
backend-dependent data composed by generic machinery.

Current [Incremental.Map](../../Applications/Incremental/Core.lean) already
provides executable `run` and `change` operations, and `Compiler.compile_update`
proves correct finite updates for every term of the supported first-order
source. `comp` calls `f.run x` when forming the downstream change.
`Cache` stores the input, output and their equality invariant; it has no
separate internal-state field. `recompute` is a lawful baseline.
[Arithmetic.lean](../../Applications/Incremental/Arithmetic.lean) supplies
proved primitive implementations. These facts support generic correctness,
not the state or resource claims of the proposed sum case. Recursive stateful
search is a later consumer in [#111](https://github.com/VladimirMarko/conaled/issues/111);
[#109](https://github.com/VladimirMarko/conaled/issues/109) owns recursion support,
which this specification-level work does not require.

## Realization contracts in the existing architecture

Keep four observations separate: semantic admissibility, achieved cost, a bound
against the ideal optimum, and a bound only against explored candidates.
For an exact chosen selector `s`, a representation decoder `d`, and a realization
`r`, the equation `d(r p)=s p` fits `Squares.Square`. It includes a tie-breaking
choice. Exact optimality without a chosen tie-breaker instead has contract
`d(r p)∈Opt A J p w`.

This set-valued specification fits `Relational.RelSquare` without changing its
functional `spec` field: the semantic output carrier is `Set P`, `spec(p,w)`
returns `Opt A J p w`, and the output relation is `d(r)∈S`. Restrict the input
carrier to problems with an attainment proof for a total exact selector.
An alternative output relation can retain a full problem record and require
admissibility together with `J(d(r),w)≤α V(p,w)+ε`. Use finite nonnegative
real costs and `α≥1, ε≥0` for this version; extended infinities need explicit
arithmetic conventions. The relation must carry the problem and workload so
it cannot certify a result against an unrelated optimum.

For a sound upper estimator, the relation is `actual≤estimate`; minimizing
estimates alone does not ensure minimizing actual costs. For a candidate set
`E⊆A`, exact extraction proves optimality on `E`. As `inf A≤inf E`, that alone
gives no global approximation factor. A certified lower bound on `inf A` plus
an attained upper bound can provide a gap certificate without finding a global
minimizer.

Relational composition preserves a given relation, but does not automatically
invent arithmetic for approximation factors. With finite nonnegative objectives,
contracts `c₁≤α₁ c₀+ε₁` and `c₂≤α₂ c₁+ε₂`, `α₂≥0`, imply
`c₂≤α₂α₁ c₀+α₂ε₁+ε₂`. Candidate compatibility and semantic refinement must
also compose. Stateful relations require invariants over reachable states.

Reuse [Squares.Square](../../Squares.lean), horizontal/vertical pasting,
[RelRep, RelSquare and witnessSquare](../../SquareKit/Relations.lean), and
`RawMap`/`MapLaws` for categorical interpretations. `witnessSquare` is a
mathematical bridge; its semantic witness is data and it proves no runtime
erasure. These distinctions agree with [ADR 0002](../adr/0002-relations-and-synchronization.md)
and [ADR 0007](../adr/0007-incremental-and-enclosure.md).
Cost objectives generally do not descend to a quotient by ordinary semantic
equality: equivalent programs can have different costs. Keep a cost-sensitive
carrier or a separate objective on raw alternatives; do not demand `MapLaws.congr`
for a cost interpretation under an equivalence that erases its observations.

The pinned Felix [comma construction][felix-comma] packages paired arrows with
a commuting equation. Its [homomorphisms][felix-hom] and [law transport][felix-laws]
separate operations, equivalence and preservation. Local counterparts are
catalogued in [the parity implementation record](felix-parity-implementation.md).
They support reuse of preservation proofs; the cited constructions do not
supply the missing objective, attainment, coverage or cost hypotheses.

## What the AD analogy establishes

Elliott derives AD operations from a derivative specification and changes its
representation to obtain modes [in The Simple Essence of AD][ad]. Its
[errata][ad-errata] correct the cartesian/cocartesian roles in continuation
and opposite constructions and the result type of `onDot`; the analogy must
use those corrected assumptions. Locally,
[Generalized.LinearModel](../../Applications/AD/Generalized.lean) exposes
representation operations and relational laws, and `compile_derivative` and
`modes_agree` connect independently compiled modes to an actual derivative.

The transferable method is specification, laws, representations, then algorithms.
Optimization lacks a general derivative-like chain rule for choosing minima;
the coverage and context hypotheses above explain specific obstructions.
Whether richer representations yield useful compositional optimization
algorithms remains a research question. It is not necessary to answer that
question to accept noncomputable optimum specifications or objective pullback.

## Smallest useful integration and public interface sketches

No supplied Algorithm Design with Haskell development was found in this
checkout: file-name searches for Algorithm/Haskell/Cost/Optimization and content
searches for the textbook title found no declaration collection to inspect.
Its revision, evaluation model, primitive costs, size measures and axiom
dependencies are therefore unknown. No theorem coverage is attributed to it.
Before importing, obtain the snapshot and record those items per selected
theorem, including whether sharing, totality and amortization are modeled.

Start with the order-level definitions and transport arguments above and the
bounded matrix case. The public interface should accept ordinary Lean
functions and predicates directly. This is pseudocode, not compiled Lean:

```text
minimizers (admissible : Set P) (objective : P → K) : Set P
pullObjective (interpret : P → Q) (objective : Q → W → K) : P → W → K
minimizer_transport (admissible-map proof) (monotone cost-map proof)
  (cost agreement) (coverage-or-domination proof) (source minimizer proof)
selection_relation (problem, candidate) := candidate ∈ minimizers ...
```

Demand only a preorder for minimizers, completeness when defining an infimum,
and attainment when selecting. Build a `RelSquare` adapter after these ordinary
lemmas; callers with a textbook equality proof should supply that proof as
admissibility evidence rather than re-encode the argument as compiler syntax.
A cost simulation should similarly accept an existing evaluation/cost theorem
and an input-size relation. Requiring a new bundled categorical instance for
every theorem would increase caller effort without adding a preservation law.

Next, inspect one textbook derivation whose assumptions match the matrix case
or another bounded alternative family. Reuse its semantic equality and cost
lemma separately. Check both cost interpretations, the nonattainment example,
and the failed semantic-only transport example before generalizing. Any Lean
implementation must follow example-driven development, statement review and
the fresh build/axiom audit. This research adds no Lean declarations.

Scoped follow-ups are [#112](https://github.com/VladimirMarko/conaled/issues/112),
an order-level optimization/relational selection integration, and
[#113](https://github.com/VladimirMarko/conaled/issues/113), resource-aware
stateful incremental composition. The latter should first realize the sum case under
an explicit evaluation model, not claim an efficient A* compiler. A future
textbook bridge waits for its declarations, but the mathematical integration
need not wait for it or for recursion support.

[ad]: https://conal.net/papers/essence-of-ad/essence-of-ad-icfp.pdf
[ad-errata]: https://conal.net/papers/essence-of-ad/#errata-and-clarifications
[eqsat]: https://www.cs.cornell.edu/~lerner/papers/popl09.pdf
[cost]: https://arxiv.org/abs/1506.01949
[lazy]: https://launchbury.blog/wp-content/uploads/2019/01/semantics-of-lazy-evaluation.pdf
[selfadjust]: https://software.imdea.org/~rleywild/publications/popl09/popl09.pdf
[bounds]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Bounds/Defs.lean
[extrema]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Filter/Extr.lean
[lattices]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/CompleteLattice/Basic.lean
[felix-comma]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda
[felix-hom]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda
[felix-laws]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda

[credits]: https://arxiv.org/abs/2006.15036
