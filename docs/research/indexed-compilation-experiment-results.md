# Indexed compilation experiments

Issues #351–#357 extend the earlier [shared-meaning experiments](shared-meaning-experiment-results.md)
with indexed witnesses, resource modes, native observation clients and dependent
proof/code connections. The authoring trial has its own prospective protocol and
results below. These experiments retain the native interfaces.

## Results and their boundaries

| Issue | Result | Boundary |
|---|---|---|
| #351 | Existing slice adjunctions and canonical comparisons preserve a selected dependent sum through two context changes and an alternative sum representation. | Commutativity alone does not make a base-change comparison invertible. An invertible mate does not establish that an inverse mate is an isomorphism. |
| #352 | A fixed two-mode compiler fragment has a graded-resource meaning, an actual down/up adjunction, two compiler passes and finite big-step evaluation. | Resource degree rejects generic linear copying/discarding, but does not model heap identity or runtime ownership. |
| #353 | Optional shared adapters recover native parser decisions, FIFO state and FRP positioned traces; a second non-parser client exercises reuse. | State equality does not preserve cost. Removing silent events loses positional information. Native APIs remain available. |
| #354 | A sourced effective-topos construction supports multiple selected certificates, dependent payloads, base change and strict solution interpretation. | This is a mathematical report checked against its sources, not a Lean effective-topos provider or operational adequacy theorem. |
| #355 | Independent reference Id/J proofs compile through local rule certificates; the retained higher witness, dependent action and finite-tail case remain connected to native semantics. | No reverse compiler, equality reflection, full scoped-AST port or general equivalence of calculi is proved. |
| #356 | One bounded derivation connects actual native fullG typing, target pack/split quotation and a separate executable code AST through a selected meaning. | Target semantics covers the generated proof image with provenance, not arbitrary fullG proofs. |

The individual reports contain the hypotheses, checked statements, examples and
negative controls:

- [Indexed witness adjunctions](indexed-witness-adjunctions.md).
- [Mode-based adjoint compiler](mode-based-adjoint-compiler.md).
- [Finite observation and execution adapters](finite-observation-execution-adapters.md).
- [Effective-topos multiple certificates](effective-topos-multiple-certificates.md).
- [Identity theory maps](identity-theory-maps.md).
- [Dependent shared-meaning client](dependent-shared-meaning-client.md).

Selection remains part of the contract. For example, #356 preserves the packet
`(6, 6 : Fin 8)` after successor and doubling substitutions. Replacing the second
component with zero gives an inhabited fiber at the same index, but fails the
selected-result contract. #355 retains a chosen higher cell and its dependent
action; its numerical source observation must not be confused with a new
numerical observation after the two object substitutions.

The equality used by these checked comparison theorems is Lean propositional
equality of the indicated values, syntax, arrows or derivations. Native typing
and object-language equality remain separate judgments. Nothing here requires
global decidable equality of an arbitrary mathematical setting.

## Architectural consequences

Existing functors, adjunctions, preservation laws and local rule certificates
supply much of the reusable mathematics. The work that remains at each boundary
is concrete: justify native typing, interpret local operations, connect actual
compiled syntax to executable code, and specify which observations are retained.
A whole-tree preservation theorem reuses those local proofs; it does not discover
or remove them.

This favors optional capabilities whose hypotheses match an actual consumer.
The native calculation can remain shorter for a small client. The adjunction
experiment adds display objects and projection equations; the observation
adapters add packages around short native proofs; the shared-meaning client adds
local typing and quotation laws. Their correctness and composition do not alone
establish that this setup pays for itself in author effort.

The different traditions retain different jobs. Adjoint resource modes constrain
which operations are admissible. Indexed adjunctions compare dependent sums
under changes of context. Institutions compare satisfaction across logical
presentations. Computational squares relate implementation and selected meaning.
Compatible instances can share a meaning comparison without forcing every client
to implement all four interfaces. These results provide no basis for a universal
AST or a repository-wide migration.

## Prospective authoring evidence

The [prospective trial](incremental-dependent-author-trial.md) used two fresh
independent authors after the interfaces and task passed review. Both completed
the common arbitrary-schedule extension without frozen-library changes, and exact
replay passed. Native authoring took approximately 4 min 40 s with five archived
checks; compositional authoring took 4 min 2 s with six. Native source was shorter;
the candidate reused more prepared helpers. No general productivity advantage
follows from that mixed, two-author observation.

The compositional route reused the public whole-proof/code law, but still needed
schedule and dependent substitution connections. The native route constructed
local typing and its own small executable carriers directly. Both retained the
same selected outputs. The trial therefore supports continued availability of
both routes and identifies boundary work to measure in a future client, rather
than establishing a mandate to migrate native clients.

## Remaining owners

| Owner | Remaining question and next useful trigger |
|---|---|
| #289 | A second dependent consumer should determine which indexed interface is worth sharing. Local universes, nontrivial dependent SDT clients and broader semantic coherence remain open. |
| #290 | Wider theory interpretations, selected higher evidence and executable proof translation need actual consumers. The #339 consumer condition still applies; intermediate administrative erasure requires its own coherence theorem. |
| #36 / #290 | A new mode-based compiler consumer should justify additional connectives or named-context elaboration. Runtime ownership needs a stronger observation than degree conservation. |
| #235 | Evaluate recurring boundary work across clients and any future author trials before choosing a broader architectural migration. |
| #200 | The remaining semantic traditions retain their separate hypotheses and intended observations; the adjoint experiments do not replace that research. |

The [semantic-traditions inventory](semantic-traditions-coverage.md) retains
nominal binding, proof-theoretic support, classical realizability, relational
hiding, local universes, probability and quantitative observations with their
promotion conditions. #107 remains paused, #108 unselected and #260 inactive.
