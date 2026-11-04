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
The solver alone does not translate source syntax, prove a physical producer
emits within a bound, or establish sharing. The guarded compiler described below
adds the syntax translation. Evaluating earlier
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

## Direct interfaces and guarded compiler

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

[#302](https://github.com/VladimirMarko/conaled/issues/302) adds the bounded
[guarded compiler](../../SquareKit/GuardedStreamCompiler.lean), inspected and
extended from revision `2525b12052e4c85c57f9050dbf18f7a36ba2ef19`. Its
[checked clients](../../Examples/GuardedStreamCompiler.lean) are imported by the
public entrypoint. The coordinate construction remains the one described above;
this compiler does not formalize the categorical GSOS theorem.

### Source, targets and certificates

`Body Const Param Ref Op Bin` has a single recursive variable, stream parameters,
references to available streams, delay by a named constant, admitted unary causal
operations, and binary pointwise operations. A `Meaning` assigns these labels
independent stream semantics. An environment can be extended with a completed
compiled solution before compiling the next definition. References cannot
introduce mutual recursion through the syntax; there is no binder for another
recursive definition. Stream parameters and references have the same constant
semantics with respect to the current recursive variable, but separate names
record their roles.

`guarded` checks that every recursive occurrence lies below a delay. Parameters
and references are guarded because they do not depend on that variable. A unary
application inherits its child's certificate; a binary node requires both.
`denote_causal` and `denote_guarded` derive semantic dependence from these local
rules. The check is sufficient, not complete: an operation that ignores its
argument could make an unchecked body semantically guarded. The compiler does
not infer that stronger fact. An unguarded identity is rejected at the check and
also fails the independent semantic `Guarded` predicate.

A `Target` provides a code type and one constructor for each source constructor.
`compile` recurses structurally over the finite body and never unfolds a stream.
A separate `Sound` supplies an interpretation of code and constructor-local
laws. It assumes neither a recursive-client primitive nor a fixed-point law.
`compile_sound` establishes body denotation, and `compile_guarded` transfers the
derived certificate to interpreted code. `solution` admits certified bodies and
uses the existing constructed `solve` on that interpretation. `solution_fixed`
proves the source equation. `solution_meaning` recovers any independently given
stream satisfying that equation, using constructed uniqueness. The function
target discharges every constructor law by reduction.

`Interpretation` records constant, parameter, reference, causal-operation and
binary-operation squares between meanings. `bodySquare` uses the existing
`Squares.identity`, `Squares.compose` and `Squares.pair` to build the whole body
square. `denote_interpretation` reads its commuting law, and
`solution_interpretation` lifts that law with `map_solution` across any two sound
targets. The coefficient map can be lossy; invertibility and injectivity are not
hypotheses. No shared preservation interface changed. The old direct APIs and
finite indexed composition contracts retain their statements and assumptions.

### Checked clients and remaining obligations

`compiledOnes_eq` uses `solution_meaning` through `run_meaning` to recover the
constant-one sequence. `compiledOnes_direct` identifies it with the old `ones`.
`compiledSums` uses that constructed stream through a reference. Its compiler
correctness theorem recovers the old `sums` solution and hence n + 1 for every
coordinate, with checked zero and four cases. `compiledTriangular` refers to
compiled sums, with an independent finite summation specification and coordinate
four equal to ten. A separate parameter client and a causal operation outside a
delay exercise the other source constructors.

`model_interpretation` discharges local laws for an additive map preserving one.
The modulo-two client first transports compiled ones, then uses that result to
prove the reference law for compiled sums. It obtains coordinate four as one
through the public interpretation theorem. The existing noninjectivity theorem
is retained. `zero_map_rejected` and `zero_map_body_square_fails` show the precise
failure of a constant-zero interpretation at delay-one and coordinate zero.

Authors supply finite syntax, meanings for parameters and prior references,
causality of admitted unary operations, and a reducing guard certificate. For a
new target they supply constructor implementations and local denotation laws;
for a change of coefficients they supply local interpretation squares. The
compiler derives body correctness, guardedness, a constructed unique semantic
solution, and preservation. A closed-form or independently specified recurrence
still needs its own source-equation proof, as in the sums and triangular cases.

There are three separate termination and progress questions. Syntax translation
terminates by structural recursion. Semantic existence and uniqueness use
strict coordinate dependence and the well-founded solver. These do not give an
operational producer or a bound on delivery of finite observations: admitted
operations are mathematical functions and may be noncomputable, and evaluation
can repeat earlier work. #146 and the existing `Progress.Streams` contracts own
operational delivery certificates. Retained state, repair and change propagation
remain separate work under #109 and generic memoization #263. #235/#36 retain
shared-interface expansion and broader language integration. This fragment adds
no scheduler, unrestricted recursion, arbitrary-category GSOS instance, or runtime
resource bound.
