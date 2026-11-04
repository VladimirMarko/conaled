# Modular guarded definitions of streams

[#284](https://github.com/VladimirMarko/conaled/issues/284) constructs a unique
solution for coordinate-guarded stream equations, then uses a solved definition
inside another equation. The independent meanings are `ones n = 1` and
`sums n = n + 1`. The same solution theorem transports the constructions through
reduction modulo two. No solution operator, finality instance or correctness
of an opaque recursive primitive is assumed.

## Source theorem and selected fragment

Milius, Moss and Schwencke, [*Abstract GSOS Rules and a Modular Treatment of
Recursive Definitions*, v2](https://arxiv.org/pdf/1307.2538v2), Assumption 2.1,
requires binary products/coproducts, a terminal H-coalgebra C and free K-algebras.
Assumption 3.4 adds a GSOS law `K(H × Id) → HM`, with M the free K-monad.
Theorems 3.5 and 3.6 construct completely iterative algebras for HM and MHM.
Theorem 4.8 extends a given completely iterative algebra by the solution of a
guarded recursive program scheme `V → T^(H+V)`; its format requires the
iteratability in Definition 4.5. Theorems 5.14 and 5.23 establish unique
interpreted solutions and extended completely iterative structures for the
specified GSOS-relative and sandwiched formats. Their natural-transformation
and free-algebra hypotheses are substantive. Section 6.2 treats streams and
valid finite circuits: each feedback loop passes through a register. These
results license subsequent recursive definitions using admitted operations;
they do not license arbitrary unguarded functions.

The checked development below is a direct specialization of that method to
strict coordinate dependence, not a formalization of the categorical theorem
or all its recursive scheme formats. It uses types and ordinary functions.
The source's modularity motivates the selected reuse; the Lean proofs construct
the required instance independently.

## Construction and admissibility

[GuardedStreams](../../SquareKit/GuardedStreams.lean) takes `Stream A = Nat → A`.
`Causal F` means output n depends only on inputs through n. `Guarded F` means
it depends only on inputs strictly before n. In particular, coordinate zero of
a guarded body cannot inspect the recursive argument. These are semantic
admissibility predicates with explicit proofs, not a syntactic checker.

The accepted building blocks are a prefix operation `cons`, causal operations,
and their compositions. `cons_guarded`, `causal_comp`,
`guarded_comp_causal` and `causal_comp_guarded` prove closure. A causal context
may surround a guard or be substituted inside it. Authors may admit other
operations by proving the same dependence condition.

`solve F seed n` is defined by well-founded recursion on n. To evaluate F at n,
it supplies a stream whose coordinates i below n are the already constructed
`solve F seed i`; other coordinates contain seed. `solve_fixed` uses guardedness
to show that this finite approximation gives the same output as the complete
stream. `unique` uses strong induction on coordinates to prove that any solution
equals the constructed one. `seed_independent` shows that the arbitrary filler
cannot affect a guarded solution. Thus the construction is inhabited and its
uniqueness assumption is discharged, rather than bundled as an unexplained
model law.

The construction supplies each finite coordinate by terminating Lean recursion.
It does not turn a source recursive program into compiled code, prove a physical
producer emits within a bound, or establish sharing. Evaluating earlier
coordinates repeatedly may duplicate work. Existing
[Progress.Streams](../../Applications/Progress/Streams.lean) distinguishes
operational finite delivery from semantic streams; those contracts remain
separate here.

## Previously defined operations in later equations

The first family is `constantStream a = solve (cons a) a`.
`constantStream_fixed`, `constantStream_eq` and `unique` provide its defining
equation, independent constant meaning and uniqueness. `ones` is its instance
at one. This is a parameterized family of nullary stream operations.

The second scheme is authored using that constructed `ones`:

```text
sums = cons 1 (addLeft ones sums)
```

`addLeft p` performs coordinatewise addition with a supplied stream p. It is
causal for any p, so `sums_guarded` follows by composing its causal law with
`cons_guarded`. `sums` then invokes the same constructed solver. Its definition
does not replace `ones` by its closed formula and does not define sums directly
as n + 1. The later scheme therefore uses the earlier admitted operation;
it is a bounded example of adding a solved constant to the available operations,
not a claim that every new operation extends a general GSOS signature.

Existence and uniqueness need only `Add R` and `One R`. The independent formula
`sums_eq` needs `AddMonoidWithOne R` to interpret natural numbers and their
addition. It proves equality at every coordinate by establishing that the
independent formula satisfies the equation and applying `sums_unique`.
Commutativity, multiplication and cancellation are unnecessary. `ones_eq`
requires only `One R`.

## Interpretation, substitution and failure cases

`map_solution` proves a reusable interpretation theorem. For guarded F and G,
if a coefficient map f satisfies

```text
f ∘ F s = G (f ∘ s)   for every s,
```

then f maps the constructed F-solution to the constructed G-solution. It uses
the source fixed-point theorem and target uniqueness; f need not be injective
or invertible. `ones_map` supplies the first operation's square, and `sums_map`
uses it to discharge the later operation's square. The latter requires an
additive homomorphism preserving one, without an assumed solution-preservation
law.

[Checked applications](../../Examples/GuardedStreams.lean) instantiate that
comparison with `Nat →+ ZMod 2`. `parity_sums` preserves the whole stream, and
`parity_five` uses that theorem to recover coordinate four as one. The original
Nat coordinate is five. `parity_not_injective` prevents interpreting transport
as equality reflection or lossless representation.

The remaining cases expose boundaries and composition:

- coordinate zero and coordinate four use the general sequence formula;
- `replace_ones` uses `solve_congr` to substitute the independently proved
  constant meaning for the solved operation, even with a different filler;
- a successor context outside `cons 0` uses `causal_comp_guarded`, then `unique`
  to recover n + 1;
- two causal successors composed inside a guard use `causal_comp` and
  `guarded_comp_causal`;
- `identity_two_solutions` exhibits distinct zero and one streams solving
  x = x; `identity_not_guarded` rejects its body at coordinate zero.

The last example rules out admitting every causal function as guarded:
identity is causal but does not determine its own solution.

## Existing interfaces and remaining compiler work

Ordinary clients can still use direct recursive definitions or mathematical
sequences. This interface helps when a new body is built from admitted causal
operations: the author supplies the body, its guardedness proof and, when
needed, a candidate meaning or local interpretation square. The library supplies
construction, uniqueness, filler independence and transport. Direct recurrence
proofs remain shorter for some single fixed sequences; no independent author
trial is claimed here.

Current finite indexed constructor/observer laws prove preservation of finite
composites. They do not construct a solution to an infinite recursive equation.
This experiment adds an explicit coordinate-progress condition and a
well-founded construction, with a local square lifted to whole-solution equality.
It does not retrofit those conditions onto ordinary or indexed clients. Existing
parser witness fibers and noncommutative weighted meanings are unchanged.

`ProductStreams.functionFinal` already constructs a final stream coalgebra.
The present proof uses coordinate induction rather than requiring its categorical
machinery from direct clients. Neither finality alone nor the finite laws would
admit x = x. Generalizing this experiment to a different category would require
its own guarded solution construction or the actual source-theorem hypotheses.

[#109](https://github.com/VladimirMarko/conaled/issues/109) retains the source
recursion/compiler interface: a syntax of guarded bodies, compositional
translations, backend admissibility proofs and interpretation squares must still
be built. Its existing finite-fold compiler does not already compile these
infinite definitions. Incremental reuse would additionally require retained
state and change-propagation contracts. #235/#36 own any proposed shared
interface expansion and recovery of existing clients; #146 retains operational
termination/productivity certificates. No infinite parser, memoization or
resource bound follows from this semantic experiment.
