# Branching graph transport in paired Set interpretations

Issue [#119](https://github.com/VladimirMarko/conaled/issues/119) implements the
first experiment from [the setting contracts](composable-setting-contracts.md).
This is an experimental embedded Lean interface. It selects components of an
external family of models of the existing regular signature. Internal setting
formation remains the separate experiment in #120.

## Public interface and comparisons

[`InterpretationRoutes`](../../SquareKit/Internal/InterpretationRoutes.lean)
uses `Models I F P = I → Interpretation F P`. `Pair` specializes I to Bool;
false is the first component. `pair`, `project` and `swap` expose the two
interpretations without changing `Logic`, its syntax or ordinary callers.
Sorts and symbols live in universe u, carriers in v and the external index in
w. The index does not represent a universe of internal models.

A route `r : J → I` selects models by `reindex M r`. Its syntax translation is
the identity, including typed substitutions and derivations. `Context`, `term`
and `formula` expose interpretation at a component. `context_route`,
`term_route`, `formula_route` and `existential_route` compare interpretation
after selection with selection after interpretation. These comparisons reduce
definitionally; the formula API states them as logical equivalences.
Existential witnesses are the same carrier elements on both sides, in Lean
Prop. There is no truncation beyond the existing formula semantics.

`term_substitution` and `substitution` reuse the existing substitution theorems.
The latter includes relation atoms, equality, conjunction and existential
binders; the existing proof uses `Sub.lift` under the binder. These are
propositional equalities or logical equivalences, not claims that all syntactic
substitution normalizes definitionally. `derivation` reuses `sound` in every
component. `preserve` selects components of an already valid sequent and does
not require its source derivation again. Validity quantifies separately over
each component's environments. A product of environment sets would make the
whole contract vacuous when just one branch has an empty context carrier.

`reindex_id` and `reindex_comp` are definitional equalities. Composition is
precomposition of index functions: first r, then s selects r(s(j)). Their unit
and associativity comparisons reduce to function application. `first_via_swap`
compares π₀ with π₁ after swap by definitional equality of whole models;
`swap_project` handles either Boolean index by cases. `swap_swap` is
propositional equality by function extensionality and Boolean cases. These
strict choices need no carrier equivalence or dependent cast at the selected
first component. They are not replacements for natural isomorphisms in an
arbitrary category.

## Checked uses and statement review

[`BranchingGraphTransport`](../../Examples/BranchingGraphTransport.lean)
retains the following cases through the public entrypoint and axiom audit.
The initial missing connection was between the existing graph derivations and
an API for selection/comparison of models. The graph theorem itself was
already available; no artificial failing native graph proof was needed.

- `first` and `second` interpret the same `Graph.forward` and `Graph.backward`
  through `graph`: f₀(x)=x+1, g₀(y)=2y gives z=2(x+1), while f₁(x)=0, g₁(y)=y
  gives z=0. `swapped_first` transports validity along the explicit
  `first_via_swap` comparison before applying it to an environment.
- `substituted_graph` substitutes into the existential graph formula in a
  larger context. The independently chosen calculation is 3→4→8; the unused
  input 99 checks variable placement. Its proof calls `substitution` and
  `graph`, rather than proving the native graph equation again.
- `empty_graph` interprets the backward derivation with empty input, middle
  and output in one component. `inhabited_beside_empty` still establishes a
  useful graph claim in the other component. `empty_ex` and `inhabited_ex`
  distinguish the closed existential in those same models, without an
  environment containing an element of Empty.
- `projection_does_not_reflect` checks two arrows from (1,1) to (1,Bool)
  with equal first projections but different second values. `both_detect`
  uses `joint_reflection`, whose hypotheses require both arrow equalities.
- `square_comparison` specializes the existing `Graph.horizontal_comparison`
  to either branch. That theorem uses `graphMap_laws.comp`; no square algebra
  or native graph-composition proof is duplicated.

Statement review checked all new claims against these intended meanings.
The interpretation contracts quantify over arbitrary signatures, terms,
formulas, typed contexts and component environments. `preserve` assumes
validity in every original component, stronger than validity in the selected
component but weaker than a derivation. No reverse implication is supplied.
Substitution changes Γ to Δ, and the existential witness extends Δ before
interpreting the lifted substitution. The graph equivalence uses the two
existing derivations in their original directions. The empty existential and
inhabited sibling rule out a hidden inhabitedness requirement or accidental
vacuity across branches. Reflection is restricted to equality of dependent
families of arrows, using both components; it does not assert syntactic
conservativity or reflection of all sequents.

## Validation and limits

The new modules are imported by `SquareApplications.lean`. Validation uses the
focused Lake build, then `direnv exec . ./check.sh` for fresh compilation,
public import coverage and the exhaustive permitted-axiom audit. The immutable
review handoff records the command results and reviewed candidate.

This interface proves component selection for a fixed signature with Set
semantics. It supplies no general regular-functor model transport, higher
identity, geometric syntax, topos classifier, internal setting constructor or
infinite tower. Its index composition laws describe this family of strict
routes; they do not establish closure under internal construction. #121 can
consume the component interface alongside #120's parameterized setting data.
The #107/#108 repair and fresh-theorem protocol is untouched.
