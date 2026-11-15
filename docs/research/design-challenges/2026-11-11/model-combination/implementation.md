# Model combination: independent implementation and use assessment

Retain `combine` and its local `Combination` result contract. The existing uses justify shared recovery and fixed-overlap comparison lemmas. They do not yet justify replacing native operation packages with a generic signature framework. Select a state-changing operation family for the next comparison, and require it to expose recurring transport or law-preservation work that the present observer-only right component never encounters.

This is the implementation/use assessment at source `e80c51d968925be3809ba3acc3259de7041b504b`. Paths below are relative to the pinned source checkout. I inspected source and research notes, confirmed the checkout revision, and performed text searches. I ran no Lean build, proof audit, timing trial, or executable experiment. Mathematical extensions below are paper proposals, not checked declarations. No external theorem is asserted from the papers cited by the research notes; I did not independently inspect those papers for this assessment.

I received the neutral brief and this lens in a fresh task context. I have no known prior implementation involvement or exposure to the other initial reports. The common brief and repository reports influence this assessment. No model diversity was established. I did not read other assessments or coordinate conclusions.

## What builders and callers actually do

`Applications/ModelCombination/ActionObservation.lean:24–51` separates a construction from a result contract. Canonical builders supply native `Monoid M`, `MulAction M X`, the selected points, an arbitrary observer, an equivalence with its inverse equations, and preservation of the point. `combine` retains the action on X definitionally and defines output by composition. Its recovery proofs are discharged inside the constructor. Builders do not supply a joint model or its mixed equation.

`Examples/NativeModelCombination.lean` exposes the remaining obligations:

| Builder or caller | Independent work | Reused work |
|---|---|---|
| `boolean` | `boolFin` with both inverses, `bool_point`, native XOR meaning | `combine`, `action_output`, `mixed`, both recovery laws |
| `listCombined` | Prefix `MulAction`, `listPair` with both inverses, `list_point`, `List.length_append` as `list_native` | Same constructor, action/output comparison, mixed law and recovery |
| `flipped` | A noncanonical point, output and both recovery equivalences; proofs of action and observation recovery; `flipped_overlap` | Universal `no_invariant_alternative` |
| `no_singleton_combination` | Cardinality contradiction for the supplied carriers | Induced `C.overlap` for arbitrary result carrier Z |

The two canonical examples share one operation pattern. Moving from Boolean state to unbounded ordered lists broadens the instances, but does not exercise transport of a right-hand state-changing operation, preservation of a right-side algebraic equation, common operation agreement, or mixed arities. Those are distinct implementation obligations.

The strongest evidence for retention is `no_invariant_alternative` together with `flipped_not_invariant` and `presentations_differ`. Direct `o ∘ e` would establish the canonical output, but the record permits a theorem over every joint carrier satisfying recovery and the same overlap. The flipped constructor is an inhabited alternative with a different raw output, so this generality is consumed rather than merely available. `no_singleton_combination` similarly uses the contract without requiring the canonical representation.

The list callers show another useful boundary: `observation_not_injective` coexists with `right_recovers_order`. An output observation may discard order while the supplied state identification retains it. A replacement that identifies states by equal observations would change the contract and invalidate this distinction.

## Interface depth, coupling and recurring costs

The canonical interface is shallow by design: `combine_out` is definitionally direct composition. Its useful hidden work is cancellation and recovery bookkeeping. `mixed` follows from `mul_smul` alone and adds no independent algebraic hypothesis. Adding a mixed-law field would therefore charge builders for derived evidence. The current fields already derive `out_eq`, `left_reduct`, `right_reduct`, `output`, and `action_output`; these should remain results rather than new inputs.

The alternative-carrier interface has more substance. Its `left_action` ties the ambient `MulAction M Z` instance to the native action on X. Both equivalences and both point equations are necessary to describe the chosen recovery data; deriving their existence from mere observations would be a different promise. `flipped` pays these obligations explicitly. A future reusable constructor for re-presenting a result along an action-preserving equivalence could absorb this work, but there is presently only one inspected noncanonical builder.

Fixed-overlap callers repeat the supplied equivalence and `C.overlap = e` in `action_output` and `output`. Canonical callers close this with `rfl`; the flipped caller proves an extensional equivalence equality. This is visible repetition, but it records mathematically consequential data: changing the overlap changes the combined observation. A helper specializing `action_output` to `combine` could remove the canonical repetition without indexing every result by an overlap equality. Retain the unconstrained result contract for rejection theorems.

The parameters `x0`, `y0` and `d0` are not needed to compose functions. They express the selected constants in this particular common reduct and result signature. `differentConstant` establishes that `d0` is independent of the observation at the state point. Removing these parameters would simplify a different contract; adding `o y0 = d0` would wrongly strengthen this one. For broader reuse, make pointedness a capability only when a real client needs an unpointed variant, rather than retroactively changing these clients.

There is no established implementation defect here. The principal risk is treating this local result contract as evidence for general model amalgamation. It fixes M and D, shares a single state carrier through equivalences, and transports an unconstrained unary observer with codomain D. Generic operation transport would introduce input/output sort indexing, normalization choices, common-operation compatibility, and preservation proofs for side equations. None is exercised by this constructor. Those costs may earn reuse, but the two existing uses do not measure it.

## A further client that could change the decision

Use FIFO state operations as the next operation family, with an independently supplied state-changing right component. The concrete consumer is already visible in `Applications/Sequences/AbstractFIFO.lean`: `Ops`, `step`, `run`, and `client` execute commands then observe the head. `Simulation.run_preserves` and `client_eq` already lift primitive preservation to arbitrary command words. `Applications/Sequences/FIFOExtension.lean` supplies `rotate`, `rotate_related`, `program`, and `observe`, and explicitly retains old targets and clients through `old_target`, `old_compile`, and `old_observe`.

The existing rotation is derived from the FIFO operations, so it is not itself evidence of combining independently supplied models. For the new comparison, freeze an independent right interpretation on Y containing a rotation or other state-changing operation `r : Y → Y`, its required native equations, and an observer. Supply a computable pointed equivalence `e : X ≃ Y` to a list-based FIFO state X. A direct native baseline transports `r` as `e.symm ∘ r ∘ e` and the observer as `o ∘ e`. It then runs a client that interleaves native queue commands and the transported operation. Require exact recovery of each supplied operation and retention of the existing command-only clients. Any desired interaction equation between rotation and queue commands must be proved separately or supplied explicitly; side equations alone do not provide it.

This tests a new boundary because a transported operation returns a shared state, so intermediate cancellation and preservation of its equations matter. Record whether those proofs recur across more than one independent right package. A single new unary-operation example would still leave multi-sort and multi-argument genericity untested.

Preserve the existing relational FIFO case as a negative migration control. `AbstractFIFO.Simulation` takes a relation rather than inverse functions, and `Symmetric.Observation.representation` relates valid raw states to their list meaning. `Simulation.reverse` expressly reverses the relation without supplying an inverse on states. Migrating these clients through exact `Combination` would require extra inverse data their present theorem does not assume. This is a contract mismatch, not evidence that FIFO mathematics or generic amalgamation is impossible. The existing relational route should continue to work under its old premises. ADR 0002 already protects that distinction.

## Smallest useful alternatives and acceptance evidence

1. Keep the current native construction and result contract unchanged. This preserves all inspected clients and costs no migration. Direct composition remains an adequate interface for callers needing only canonical outputs.
2. If further callers repeat canonical comparison setup, add a specialized output/action lemma. If independent alternative-carrier builders recur, test a re-presentation constructor that derives recovery from an action-preserving equivalence. Do not introduce a signature universe merely to hide `rfl`.
3. Compare native transport helpers against a bounded operation/signature construction on the frozen FIFO task. Admit competing formulations even without an incumbent adapter. Require checked recovery of the actual operations, side equations, old clients, and the existing rejection controls. Record new independent input proofs, transport proofs absorbed by the implementation, repair effort, and any changes in definitional computation. Do not infer productivity from line counts.

A generic construction wins this test only if it absorbs recurring law transport while retaining usable native callers and their assumptions. A native helper wins if it provides the same recovery without asking callers to encode operation syntax or reconstruct existing action/FIFO laws. Either can fail: a generic layer can shift transport work into each model encoder, while an observer-only helper can leave every state-changing operation and equation to be transported again.

Before broader migration, replay `boolean_once`, `boolean_twice`, prefix observations, ordered-state recovery, independent result constant, singleton rejection, and the arbitrary-Z invariance rejection, including the flipped presentation. A generic adapter should recover the existing direct interfaces; retaining theorem names with stronger premises is not sufficient. Also replay FIFO old-client preservation and relational representation independence. These are proposed acceptance checks, not checks executed during this assessment.

The remaining uncertainty is practical reuse beyond the examples module. A repository search found the current native combination consumers in `Examples/NativeModelCombination.lean` and its public-entrypoint import, not an additional application builder. The FIFO trial is a plausible next consumer grounded in existing code, not an already requested product feature. No present evidence settles whether its new transport work warrants a generic signature layer.
