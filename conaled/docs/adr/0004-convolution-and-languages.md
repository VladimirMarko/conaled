# ADR 0004: Algebraic representations and proof-relevant language derivatives

**Status:** Accepted and implemented.  
**Date:** 2026-10-10.  
**Scope:** `Applications/Convolution/` and `Applications/Languages/`.

## Context

Elliott's 2019 convolution development calculates representations by requiring
their meaning functions to preserve semiring and semimodule operations. Its
central multiplication is a finite sum over decompositions of an input word.
The 2021 language-derivative development makes a further distinction: a
language returns a **type of parse witnesses**. Concatenation and star rules
must preserve those witnesses, including parses of the empty word.

These are tests of the generality of commutative-square design. They are not
additional implementations of the cartesian-closed category interface. The
shared framework must express a useful algebra's operations and local laws
without imposing unrelated categorical structure.

Primary source snapshots used in this translation:

- [Convolution manuscript](https://github.com/conal/convolution-paper/blob/4a466d2344daf78d1edb515d4d6fe23d7bba3e67/convolution.lhs),
  commit `4a466d2344daf78d1edb515d4d6fe23d7bba3e67`.
- [2021 language-derivative repository](https://github.com/conal/paper-2021-language-derivatives/tree/fc7fd2b31f8fedc0ee7f4b59c28aa2810c82b2e4),
  commit `fc7fd2b31f8fedc0ee7f4b59c28aa2810c82b2e4`. We read the full source
  bundle, particularly `Calculus.lagda`, `Symbolic.lagda`, `Automatic.lagda`,
  and the predicate modules. The manuscript entry point alone is insufficient.
- The original Mathlib **v4.19.0** snapshot, `Computability/Language.lean` and
  `Computability/RegularExpressions.lean`, supplies the ordinary declarative
  language algebra and one independently proved Boolean derivative semantics.

## Decision 1: Make finite word convolution executable, and prove its algebra

`Convolution.Series α R` is a function from finite words to coefficients in an
arbitrary `Semiring R`. Coefficient multiplication need not commute. The
implementation consumes one character per recursive call. `convolution_splits`
proves that this recursion equals summing over the explicit `splits` list;
`mem_splits` and `length_splits` characterize that list.

The `Semiring` instance is proved from this implementation. In particular,
`conv_assoc` is a proof of convolution associativity, not a law supplied by the
caller. `derivative_mul` preserves the order of noncommutative multiplication:

    Dₐ(f * g) = scale (f []) (Dₐ g) + (Dₐ f) * g.

`mapCoefficients` is an actual semiring homomorphism. Its multiplication proof
is `map_convolution`. Natural-number coefficients additionally admit
`supportHom : Series α ℕ →+* Language α`. This positivity map is deliberately
restricted to natural numbers: arbitrary rings can cancel nonzero summands,
so forgetting weights would not generally preserve union and concatenation.

**Consequence:** this module handles infinitely supported functions without
requiring infinite sums, because a finite word has finitely many splits. It
does not assume that every monoid has this property. Arbitrary-monoid infinite
convolution and generic weighted Kleene closure require additional hypotheses
and are not implemented here.

## Decision 2: Permit redundant representations; certify normalization separately

`Convolution.Polynomial` is an executable finite association list of words
and coefficients. Addition concatenates lists; multiplication enumerates term
pairs, appends their words, and multiplies their coefficients. The decoder sums
duplicate keys. Zero coefficients and duplicates are allowed.

The implementation proves `monomial_mul`, `denote_mul`, and
`denote_normalize`. Associativity is a semantic law (`mul_assoc_semantics`);
raw association lists do not satisfy it by literal syntactic equality.

`normalizedMulSquare` horizontally pastes normalization onto multiplication.
`languageMulSquare` vertically pastes coefficient forgetting onto polynomial
semantics. Thus both composition operations of the square framework are used
by independently proved, nontrivial implementations.

**Alternative considered:** canonical finite maps or quotienting polynomial
syntax immediately. Association lists keep computation simple and exhibit
why injective decoders and syntactic equality are unnecessary. No complexity
claim is made for this representation or its duplicate-combining pass.

## Decision 3: Keep Boolean recognition and parse witnesses as distinct layers

`Regex.lean` implements smart constructors, normalization, an optimized
derivative, and recognition over the standard six-constructor regular
expression syntax. `derive_correct`, `derivatives_correct`, and
`recognize_correct` hold for every expression and every word. Concatenation
tests nullability; star is handled without a non-nullability restriction.
The proof connects the new optimized derivative to Mathlib's verified
declarative semantics. It does not merely trust an unproved primitive.

`Witnesses.lean` independently implements type-valued languages. It proves
explicit functions in both directions, and both inverse laws, for:

- `nullableConcatIso`;
- `derivativeConcatIso`;
- `nullableStarIso : Star P [] ≃ List (P [])`;
- `derivativeStarIso`, which retains a list of empty parses before the first
  consuming parse.

The last factor matters. The Boolean equation `D(P*) = D(P) · P*` forgets the
possibly many empty parses. Applying that equation unchanged to the type of
parses would discard information.

`Parser.lean` implements a separate indexed symbolic parser with union,
intersection, the universal language, scalar evidence, concatenation, star,
and transport through proved isomorphisms. `Parser.parse` returns
`Decision (P w)`: either a parse witness or a refutation of every such witness.
The computation is total, including when star's operand is nullable. A
successful decision selects one valid parse; it does not enumerate every
ambiguous parse. All semantic transport maps and inverse proofs are in the
code. This proof-relevant parser uses no Mathlib imports.

`ParserBridge.lean` proves `witnessLanguage_correct` and `recognizers_agree`.
For every ordinary regex and word, erasing the proof-relevant parser's result
gives exactly the optimized Boolean result. This is a checked bridge between
two implementations, including nullable stars.

## Decision 4: Model automatic derivatives by productive finite observations

`Machines.lean` uses state coalgebras with a nullable observation and a
transition. `Machine.Correct` contains the two local semantic obligations;
`Machine.run_correct` derives recognition correctness for all finite words.
Intersection machines compose by product state spaces.

The automatic representation is `Trie α n`, an ordinary inductive trie indexed
by its observable depth. `Machine.unfold` is structural recursion on depth.
`snapshot_recognizes` proves its result on every word of length at most that
depth. Longer observations explicitly return `none`.

**Alternative considered:** directly transliterate the coinductive Agda
definitions. The published `Automatic.lagda` contains termination overrides.
We avoid adopting an unchecked termination assumption in Lean. Finite
observations preserve productive computation and admit a fully checked proof.
This is not a claim to implement global memoization, automaton minimization,
or a finite-state bound for all derivative states.

## Integration and verification

`ConvolutionBridge.lean` compiles natural-number polynomials into regular
expressions by dropping zero terms and unioning the remaining words.
`polynomialCompilationSquare`, `polynomialRecognitionSquare`, and
`polynomialSnapshotSquare` compose the semantic stages.

`normalized_product_snapshot` proves the end-to-end theorem for **arbitrary**
input polynomials, words, and sufficient observation depths: normalize a
convolution product, compile it, unfold its derivative machine, and query the
trie; the answer is true exactly when the original weighted convolution has a
nonzero coefficient. The executable example has two distinct contributions
to `"abc"`, with total coefficient `10`.

The original eight modules were checked by Lean 4.19.0; the current toolchain
is recorded in `lean-toolchain`. There are no `sorry`, `admit`,
new axioms, `unsafe` definitions, or termination overrides. Existing Mathlib
proofs are source dependencies, not new assumptions. The packages containing
semantic type indices are marked `noncomputable` where Lean erases universe
data; the actual witness parser and Boolean recognizer remain executable.
