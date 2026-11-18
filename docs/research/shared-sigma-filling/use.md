# Independent implementation and use assessment for #627

Adopt a bounded two-stage filling derivation, subject to checked native recovery and replacement of both existing proof bodies. Prefer a local source/target theorem telescope, with a small transparent data record only where it reduces repeated arguments. A category of models, a common interval, and a classifier interface add obligations that this proof does not use.

This recommendation is based on source inspection at the brief's pinned HEAD `9aa0520591e7d107b63f9172a496fe7332b24cb8`. I read the full #627 issue, the shared brief, repository guidance and the files cited below. I have not read the other initial assessments or coordinated conclusions with their authors. I made no repository edits and ran no Lean checks. The proposed fixture and elaboration claims below remain proposals, not checked results.

## Evidence supporting the extraction

`SumFilling.lean:10–27` and `CartesianDependentFilling.lean:123–140` have the same selected algorithm and boundary proof. Each projects the box, fills the first component, retains its `Fills` witness, constructs the second box over that exact section and witness, fills it, and pairs. Cartesian additionally passes its cap term `r`; this is an input carried through every stage, not a different induction or algorithm.

The common uniformity argument is equally concrete. `SumFilling.lean:36–56` and `CartesianDependentFilling.lean:149–169` form a subtype of first sections satisfying the projected boundary. Component uniformity gives equality of the two first sections, `Subtype.ext` identifies the witnessed sections, and `congrArg` transports the dependent second construction. The final step rewrites the second-box substitution theorem and applies second-component uniformity. This is useful proof work to own once, even though the current proofs are short.

Existing primitive inputs already have the needed native implementations:

| Shared responsibility | De Morgan | Cartesian |
|---|---|---|
| First projection and second box | `PartialSums.lean:42–60` | `CartesianDependentFilling.lean:61–79` |
| Pair boundary theorem | `PartialSums.lean:62–76` | `CartesianDependentFilling.lean:81–95` |
| Second-box substitution | `PartialSums.lean:78–101` | `CartesianDependentFilling.lean:97–120` |
| Component operations and laws | `Filling.lean:9–19` | `CartesianFilling.lean`'s `Filling` and `Filling.Lawful` |

These primitives contain the boundary transport details. The extraction can reuse them without moving either model into the other's representation. Neither selected sum algorithm uses reversal or connections.

## Interface and adapter recommendation

For one filling problem, expose the whole box, its first projected box, first-section type and `Fills` predicate, a chosen first section with its proof, a second-box type indexed by the lawful first section, the second-box construction, second filler, pairing, and the pair boundary law. Derive the resulting pair's `Fills` fact from component filling facts. The first-stage proof belongs in the index or arguments because `sigmaSnd` consumes it; hiding it behind a chosen section alone would force each adapter to reconstruct the same transport.

For a single substitution, expose source and target versions of these data, first-box and whole-box substitution, section substitution preserving `Fills`, dependent second-box substitution, dependent second-section substitution, pair substitution, and component uniformity. Derive the first-section subtype equality inside the shared theorem. Use it to reduce the dependent comparison to second-box substitution followed by second-component uniformity. No input may already assert preservation of the selected composite pair. In particular, a field equating the completed second-stage-and-pair function after first filling to the desired output would conceal the argument being extracted.

A source/target telescope does not need identity or composition axioms for arbitrary abstract substitutions to prove this one-step theorem. Native composition cases can use the existing native reindexing operations and their equations. Introduce a global indexed record only if the local telescope demonstrably makes native instantiation worse.

Keep first-box substitution visible as a primitive equation even where the native adapter discharges it by reduction. Likewise, the pairing substitution equation should concern arbitrary component sections, not just selected outputs. The actual `sigmaSnd_reindex` theorem belongs in the adapter as the second-box equation. This makes it possible to inspect whether the generic proof derives the result or merely repackages it.

Build both adapters in terms of the current native operations. Preserve the public signatures of `sigmaFilling`, `sigmaFilling_fills`, `sigmaFilling_uniform`, and `sigmaFilling_lawful`. The native operation definition can stay unchanged while a transparent shared operation has a checked equality to it; both native proof bodies must then invoke the shared derivation. Alternatively, define the native operation through the shared operation if record projections and `let` reduction preserve the original computational expression. Prefer `rfl` recovery when it checks; if it does not, state exact operation equality and explain which reductions changed.

The algorithm needs first-stage boundary correctness, while the current native signature supplies the stronger `F.Lawful`. The shared core can consume only the needed boundary proof. Preserve the native signature so existing callers do not acquire a migration obligation.

## Concrete acceptance fixture

The current examples provide ingredients but do not jointly establish the requested case. `SharedCubicalConstructors.lean:104–117` quantifies over a supplied dependent variable-cap box. Its composition theorem at lines 75–79 concerns classified codes, not composition of the newly shared filling derivation. `CartesianSmallFamilyClassification.lean:72–78` establishes a proper-face fact in a separate gluing example. These are useful retained clients, but another disconnected collection of these facts would leave #627's concrete fixture untested.

A bounded proposed Cartesian fixture is:

1. Use a represented three-dimensional cube, a cap equal to coordinate 0, and the face coordinate 1 = false. Prove the face is inhabited and excludes the generic cube, and the cap differs from both constant endpoints. This avoids satisfying properness with an empty tube.
2. Reuse the Boolean tags and `Fin 1`/`Fin 2` family from `CartesianClassifier.lean:17–38`. Construct actual compatible boxes from an explicit whole section, once with false tag and its unique element, once with true tag and element 1. The family remains genuinely dependent even though each of these two sections selects one branch. Show both outputs, including the nonzero true-branch value, so the second component cannot be silently erased. A single context extended by the tag family would additionally let one section select both branches contextually, but is not required to start the check.
3. Use the cube endomorphism swapping coordinates 0 and 1, followed by the endomorphism swapping coordinates 1 and 2. Both are nonidentity and their composite is nonidentity. The first reindexed cap is coordinate 1, the second is coordinate 2; the face moves from coordinate 1 = false to coordinate 0 = false and stays there. Verify these equations directly at the native box parameters.
4. Prove whole-section filling uniformity for the first substitution, the second on the reindexed box, and their composite through the native theorem that now uses the shared derivation. Connect the successive and direct results using native reindexing composition. Check actual instantiated boxes and their component outputs, not only a theorem universally quantified over boxes whose existence has not been established.

All dimensions in this proposal use only variables and endpoints, so the same substitution patterns can also test the De Morgan adapter while retaining its fixed false cap and native Cofibration. Retain `Examples/CubicalSumFilling.lean` as a direct dependent native client; its current full-face fixture exercises different behavior and should not be weakened to match the new one.

For the concrete finite examples, output agreement outside the face needs a reason. The branches have bijective restrictions and the tag filler is presented/discrete (`CartesianClassifier.lean:26–38`); their existing filling results are the intended route. A full-face boundary theorem alone cannot establish the proposed proper-face interior result. The generic recovery theorem should remain quantified over arbitrary lawful component operations, so the finite fixture does not narrow the mathematical capability to discrete types or unique fillers.

## Concerns and adoption tests

Established acceptance gaps in the baseline are the duplicated proof bodies and the absence of one instantiated dependent proper-face variable-cap filling/composition fixture. I found no native correctness defect.

The main implementation risk is replacing short proofs with a larger adapter whose fields duplicate their reasoning. Compare the final artifacts by responsibility: a shared subtype-congruence argument, two native bindings to existing primitives, and no copied `hfirst`/`k` calculation left in either native proof. Count preparation separately from caller cost. Preparation may grow; native caller obligations should remain unchanged; mathematical capability should retain arbitrary lawful component fillings and each model's full cap/face domain. Line count alone is not a decision rule, but a long transport proof repeated in both adapters would undermine the stated benefit.

Another plausible risk is loss of reduction behavior through opaque wrappers or general transports. Check exact recovery before changing native definitions. Compile the existing classifier recovery clients (`SharedCubicalConstructors.lean:21–41, 48–73`), `Examples/CubicalSumFilling.lean`, and `CartesianClassifier.dependent_sum_substitution`. If recovery is only propositional, preserve the old native operation body and share its laws instead of silently changing clients' computation.

The dependent transport encoding is untested here. Both current uniformity proofs use `backward.isDefEq.respectTransparency false`; this is evidence of elaboration sensitivity, not evidence that abstraction is impossible. A discriminating implementation experiment is to instantiate the shared theorem for both native models before adding any broader framework. Success means the adapters need the existing primitive equations and component laws, with no final selected-pair equality supplied as a premise.

Keep the native pair-boundary and second-box-substitution proofs as model-specific obligations in this task. They have similar source but depend on different cap and face representations; their further extraction is optional and should not be claimed unless done. The endpoint-preserving interval-map obstruction remains exactly as in `SharedCubicalConstructors.no_interval_identification`. Common proof reuse supplies no cross-model map or selected-filler preservation theorem.

The adoption decision should record checked exact recovery, removed proof work, adapter preparation and unchanged ordinary caller obligations. This assessment supplies source evidence and a bounded design; it supplies neither a successful Lean implementation nor an author-productivity measurement.
