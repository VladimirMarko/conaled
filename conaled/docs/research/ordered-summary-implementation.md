# Ordered summaries and interpreted refinement composition

Implementation for [#185](https://github.com/VladimirMarko/conaled/issues/185),
following the [architecture assessment](data-structure-architecture.md).

[OrderedSummary](../../Applications/Sequences/OrderedSummary.lean) supplies
ordinary interfaces for ordered monoid summaries, optional valid caches, and
List/DList batch clients. It imports no internal-language model. A caller
supplies a measure, operations, a decoder, and the validity/observation laws
used by the particular theorem. No container hierarchy is required.

`summary` is `FreeMonoid.lift`; its append law retains multiplication order.
`Valid` separates representation validity from cache agreement. `append_valid`
requires the actual append observation law only on valid inputs. List and
Batteries.DList instances use their existing append/toList laws. The
`summarySquare` observes a cache through the existing relational interface,
without replacing full sequence meaning by summary equality.

`batch_summary` and `batch_decode` reuse reachable fold fusion. The former
computes a final summary; the latter preserves the entire ordered sequence.
`symmetric_prefix_summary` connects the existing symmetric-prefix observer to
the length specialization. Its equality does not claim an optimized runtime.

## Checked applications and statement review

The expected concrete ordered word is `[true,true,false]`, from two copies of
`(3,true)` followed by `(5,false)`. The independent length expectation is three.
[Ordinary examples](../../Examples/OrderedSummary.lean) connect these results
to cache append preservation, the summary square, both batch realizations and
full observation. Empty caches exercise both empty laws. A wrong cached label
is rejected, reversed label order changes the diagnostic summary, and equal
lengths do not imply equal sequences. These were the intended expectations
before the reusable theorem connections were developed.

The first ordinary case exposed the missing shared connection between valid
cache append and observed ordered summary. Existing free-monoid and DList laws
already supplied the local equations; no replacement monoid or DList proof was
needed. Subsequent full-sequence cases motivated `batch_decode` separately from
summary fusion. Compilation also caught wrapper-instance and dependent-carrier
elaboration errors; those were implementation errors, not changed mathematical
expectations.

| Claims reviewed | Intended meaning, assumptions and case evidence |
|---|---|
| `summary_nil`, `summary_append`, `summary_singleton` | All measures into any monoid, including noncommutative ones; no equality test or commutativity premise. Diagnostic word and duplicate cases exercise order. |
| `cache_valid`, `empty_valid`, `append_valid` and List/DList specializations | Cache agreement is required and preserved, not inferred from arbitrary raw pairs. Representation closure and observation are separate hypotheses. Empty and appended constructed caches inhabit the premise; wrong-label cache fails it. |
| `summarySquare` | Forward preservation from a full sequence relation to summary equality. No injectivity or reflection conclusion. Equal-length distinct sequences witness the limit. |
| `batch_summary`, `batch_decode`, their List/DList applications | Every finite input and valid seed; local laws restricted to reachable valid states. Summary and full observation conclusions remain distinct. Concrete duplicate/order cases exercise both realizations. |
| `summary_length`, `symmetric_prefix_summary`, `diagnostic_value` | Length uses `Multiplicative Nat`; words use `FreeMonoid Bool`. Product multiplication is addition plus ordered concatenation. Prefix output includes the empty prefix. No compactness claim for word summaries. |
| Presheaf `diagram`, natural maps and relation subfunctors | Identity/composition and naturality are checked. Restriction maps label-bearing sequences to first coordinates and diagnostic summaries to length. Cache validity is preserved by summary naturality, not assumed at both stages. |
| Set and presheaf reassociation/evaluation | The original `Internal.Associativity.forward` and `backward` are unchanged. Both intermediate witnesses and all three relations survive evaluation. No semantic-validity constructor is added. |
| Positive/restricted cases and reflection counterexamples | The positive cache has count one and label true. Changing its cached label to false invalidates the fine cache but has the same coarse restriction. Both stages have inhabited examples; the negative statements exclude validity/equality reflection only through this lossy map. |

## The argument reused across settings

[OrderedSummaryPresheaf](../../Examples/OrderedSummaryPresheaf.lean) interprets
one source reassociation proof in Set and a nonconstant presheaf on the existing
walking-arrow category. Fine sequences are lists of `(Nat,Bool)` and coarse
sequences are lists of naturals. Summary restriction forgets the word and keeps
its count. Cache restriction is their product; observations remain natural
numbers. `summaryMap`, `appendMap`, `cacheMap` and the projections expose the
relevant natural operations.

The cached relation states that the intermediate sequence is the represented
sequence and that its stored summary agrees. The next relation computes the
summary; the third observes its count. The plain alternative replaces the
first relation by sequence equality. Stability is checked for all arrows,
including the nonidentity restriction.

`cached_valid` and `plain_valid` apply `Model.sound` to both unchanged source
derivations. Their evaluation theorems use the general `Model.evaluation`
comparison, retaining existential sequence and summary witnesses. `good_coarse`
restricts the interpreted existential predicate itself. The explicit good/bad
cache pair prevents interpreting this preservation as reflection.

Only conjunction/existence reassociation is transported. The free-monoid,
list-induction, cache and naturality proofs remain local realization work.
Existential witnesses in Prop provide no executable witness-selection procedure.
Ordinary clients remain usable without importing this model or its syntax.

## Validation and remaining scope

Targeted builds exercise both new example modules. Acceptance additionally
requires the issue's fresh full source build, exhaustive axiom audit, independent
Standards/Spec review and originator review; candidate-specific evidence is
retained in the orchestration record. The public entrypoint imports the cases,
so the normal source coverage and proof audit include them.

This slice introduces no new architectural decision or shared preservation
family. It uses the existing distinction between relational forward preservation
and reflection. #235 retains ownership of broader setting-interpretation and
author-interface gaps. Resource comparisons belong to #177/#239; no speedup,
constant-time materialization, allocation bound, arbitrary indexed cache update,
branching-history bound or durability follows from these results. Finger-tree
fit remains #178.
