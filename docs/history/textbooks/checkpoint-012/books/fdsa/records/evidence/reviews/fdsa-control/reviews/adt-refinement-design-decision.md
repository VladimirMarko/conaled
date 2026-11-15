# Proposed shared Set/Map design: bounded architecture decision

Recorded 2026-11-02 after root read the complete source/API preflights and
the actual `Relations`, `RelationComposition`, `AbstractFIFO`, and primary
Chapter 6 source. The retained architecture author assessed this exact
proposal and found no duplicated helper or necessary additional framework.
This note does not freeze requirements or begin source implementation.

Use a small `SquareKit/ValidGraphs.lean` module, namespace
`SquareKit.ValidGraphs`, importing `Mathlib.Logic.Relation`. Define one
unbundled, independently universe-parameterized predicate:

```text
validGraph I decode c a := I c ∧ decode c = a.
```

Its two public mathematical bridges are:

1. `Relator.LiftFun (validGraph I decode) (validGraph J decode') impl spec`
   iff `∀ c, I c → J (impl c) ∧ decode' (impl c) = spec (decode c)`.
2. `Relation.Comp (validGraph I decode) (validGraph J decode') c b`
   iff `(I c ∧ J (decode c)) ∧ decode' (decode c) = b`.

The second grouping is definitionally a valid graph for the composite decoder
with the conjunction invariant. Neither result needs common universes,
decidability, default values, surjectivity or a reverse decoder.

Set and Map operation-only records and separate exact seven/six-law packages
retain independent element/key, value and state universes. Set insertion and
deletion preservation consume the first bridge. Map mutation semantic fields
group the updated-key and all unaffected-key equations, avoiding a global
key-decision premise. Correspondence to `Function.update` uses the existing
`Function.eq_update_iff` with a justified local or explicit key decision; its
preservation theorem pairs that equation with the separate invariant law and
consumes the same bridge.

Concrete two-stage examples at Type 0 construct existing
`Relational.existentialSquare` using the same actual middle operation. Existing
`Relational.transportRelations` then consumes the second bridge: its
`compRel` has the same existential definition as `Relation.Comp`. The examples
must establish and subsequently preserve both the true-tag and even-counter
predicates. Observation equality cannot supply the intermediate validity.
They should also expose the distinct necessity of actual middle-operation
agreement with a small counterexample.

This reuses the existing generic composition API. It does not add a generic
refinement record, an ADT signature language, another LiftFun composition
hierarchy or a global universe retrofit. Legacy bundled squares retain their
present common-universe interface; the new domain laws do not inherit that
encoding restriction. No broader architectural parity claim follows.

The case preflight is still being completed. Concrete source list/tree/map/
heap/interval algorithms and their costs remain queued. The initial Chapter 2
prefix stays `c80eec92f5458eccfd1c34c8314d666c2a1e3847`; no ADT dependency is
added to it. Chapter 1 remains active and its session 83124 remains the sole
compiler/checker at `07e480f6ec9958d4975bb90151005b84f2907614`.

The case preflight was subsequently completed and read by root. The resulting
frozen scope is `adt-refinement-requirements.md`; this earlier design assessment
remains source-only. One full Map tag/counter composition specialization is
required, together with independent Set bridge/paired-client connections.
The exact finite third-key case and product/missing-premise values are retained
in the frozen requirements. No new generic infrastructure was added to the plan.
