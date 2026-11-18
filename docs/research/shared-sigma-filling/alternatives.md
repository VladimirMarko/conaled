# Independent assessment: alternatives and generality for #627

Recommend a small dependent two-stage construction with a local source/target substitution theorem. Keep native filling records and their caller signatures. A global category/context record has no demonstrated benefit for this extraction: the duplicated argument uses one substitution at a time, and native contexts already supply identity/composition behavior. A local record can organize the telescope without committing the library to a general cubical model interface.

This recommends an implementation experiment. No source edits or Lean checks were performed in this assessment.

## Evidence for extraction

`SumFilling.lean:10–16` and `CartesianDependentFilling.lean:119–126` select the first filler, retain its boundary proof, form the second box over precisely that section, fill it, and pair. `SumFilling.lean:36–56` and `CartesianDependentFilling.lean:146–166` repeat the substantive uniformity argument: equality of the subtype of first fillers and boundary proofs, congruence of the dependent continuation, second-box reindexing, and second-filler uniformity. Its mathematical boundary excludes reversal, connections, universes, and classification.

The existing primitive results are suitable adapter inputs: `PartialSums.lean` supplies `OpenBox.sigmaIntro_fills` and `OpenBox.sigmaSnd_reindex`, and Cartesian counterparts precede `sigmaFilling` in `CartesianDependentFilling.lean`. They concern arbitrary first and second sections, independently of the selected Sigma algorithm. Accepting them does not assume compound filling lawfulness.

The commonality concerns complete selected outputs. `Examples/SharedCubicalConstructors.lean` supplies native whole-operation recovery (`Original.sigma_global`, `Target.sigma_global`) and whole-section recovery (`sigma_selected`). Preserve those contracts.

## Smallest useful formulation

Separate a local construction/boundary interface from a source/target transport telescope. A small record can organize repeated data; packaging is secondary to its requirements.

For each fixed native parameter tuple, expose:

- Original and first-box types, first sections, and first projection.
- A first filling operation and its boundary proof.
- Second-box and second-section families indexed by a first section together with its boundary witness.
- The second-box constructor and second filler.
- Pairing, second-component boundary correctness, and primitive pair-boundary correctness.

The shared selected operation evaluates these primitives in order. Its `fills` theorem applies second-component correctness and pair-boundary correctness. The first operation requires only its boundary law here; first-component uniformity is unused. Keep the native `hF : F.Lawful` argument for compatibility while letting the construction adapter use `hF.fills`. The second operation requires no law merely to define the selected result, as both existing `sigmaFilling` signatures demonstrate.

For substitution, specify source and target local data independently, with maps on boxes, first sections, second boxes, second sections, and paired sections. Require first projection to commute with box substitution, first-section boundary proofs to transport, second-box construction to commute with transport, both component selections to commute with transport, and pairing to commute with transport. Derive the compound selected-operation equation. A field equating the entire transported dependent continuation would consume the proof this extraction should share.

A useful mathematical kernel is dependent sequential composition. Put `S = {a // first.Fills a}`. Let `Q s` be second boxes, `T s` their sections, `q : (s : S) → Q s`, `g : (s : S) → Q s → T s`, and `pair : (s : S) → T s → R`. The selected result is `pair s (g s (q s))`. Substitution supplies `smap : S → S'`, `qmap`, `tmap`, and `rmap`, with primitive commuting equations for `q`, `g`, and `pair`. First-component uniformity derives `s' = smap s`; substituting that equality and applying the primitive equations proves the result. This is a paper sketch, not checked Lean code. The surrounding interface must expose first-box projection and its equation rather than rename a final-output equality as first-stage naturality.

This formulation can serve other dependent staged selections without a common interval or global category of filling problems. The one-arrow theorem can accept any suitable transport maps. A model bridge would still need those maps and their primitive laws separately constructed.

## Alternatives and costs

| Formulation | Mathematical benefit | Obligations and limitation |
|---|---|---|
| Local source/target telescope | States what one selected filling and one substitution use; permits distinct representations | Long dependent parameter lists may need a small record or named constructors |
| Global indexed record | Packages families of box problems and composable substitutions | Adds global indices and coherence preparation; useful if another consumer reuses that organization |
| Bare dependent congruence helper | Small and widely reusable | Leaves box substitution and component transport assembly in both native proofs; insufficient alone if it only abstracts `congrArg k hfirst` |
| Weak composition foundation | Broadens admissible filling structure by retaining a cap path | Changes the primitive contract and selected construction; exact recovery needs more than existence of fibrations |

A global record could earn its cost by simplifying adapters or reusing stage data for composition or another constructor. Test that benefit rather than rejecting the record by size. Conversely, an unstructured telescope is not automatically simpler when adapters must restate dependent transport types.

The broader alternative has a concrete semantic difference. Cavallo, Mörtberg and Swan define weak composition with a cap path instead of strict equality at the cap (Definition 2). Their Sigma construction adjusts the second cap using derived strict composition before composing it (Theorem 15). It supports inputs beyond the present strict-cap boundary contract. That correction makes exact selected-operation recovery a question to investigate, not grounds for dismissing the alternative for lacking an adapter. The paper uses an internal theory with function extensionality and uniqueness of identity proofs, and interval/cofibration axioms from Section 2.2. These claims come from the inspected [primary paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol152-csl2020/LIPIcs.CSL.2020.14/LIPIcs.CSL.2020.14.pdf), Sections 2.2–2.4. Its Agda code was not inspected or executed.

For #627, local extraction directly targets preservation of the requested selected algorithms. The broader alternative remains a test of the extraction's stated scope. Retaining strict boundary witnesses here does not establish impossibility of a weaker general foundation.

## Concerns and scope checks

**Established scope restriction:** the subtype step relies on `Fills` being a Lean proposition. `Subtype.ext` identifies witnesses once underlying sections agree. Cartesian `OpenBox.Fills` is explicitly a conjunction of equations (`CartesianFilling.lean:137–139`). State this proof-irrelevant boundary contract. It does not itself generalize to computational boundary evidence or higher cap-path witnesses. This restricts the proposed theorem; both intended instances satisfy that restriction.

**Established native difference:** Cartesian `Filling.fill` quantifies over arbitrary cap sections and arbitrary `Subcontext` (`CartesianFilling.lean:193–205`); the original quantifies over `Cofibration` and fixed-cap boxes (`Filling.lean:9–19`). Local parameters can absorb the difference without weakening either quantifier. A common face type restricted to cofibrations, or a common fixed cap, loses current Cartesian capability.

**Plausible implementation risk:** an abstract record can introduce nondefinitional second-box type alignment where the native proof currently uses reduction. A failed elaboration attempt diagnoses encoding difficulty, not a mathematical obstruction. Initially retain native definitions and prove equality to the generic expression before routing definitions through it.

**Plausible extraction risk:** accepting `uniformContinuation : k' (smap s) = rmap (k s)` as primitive conceals second-box substitution and second-component naturality. A primitive `sigmaSnd_reindex`-shaped law is appropriate because it quantifies over arbitrary lawful first sections without using the second selected filler.

**Established evidence gap:** `Target.sigma_code_comp` checks classification-code substitution, not compound selected-section substitution through the new theorem. The variable-cap example quantifies over a supplied box, and proper-face examples are separate. Retain them, but add a case exercising shared filling derivation with actual box data and both nonidentity substitutions.

No missing native theorem, circular native definition, or mathematical obstruction to bounded extraction was found.

## Discriminating implementation experiment

Implement the local construction and one-arrow theorem first, retaining native `sigmaFilling` definitions. Instantiate both adapters and replace native `sigmaFilling_fills` and `sigmaFilling_uniform` bodies with applications of shared results. Adapters supply primitive second-box reindexing; subtype congruence and subsequent second-stage rewriting belong in the common theorem.

1. State recovery as equality of complete native outputs for arbitrary inputs. Try `rfl`; if transport prevents it, state the actual propositional comparison and check existing reduction clients before changing definitions.
2. Construct a Cartesian box for the Boolean-tagged `Fin 1`/`Fin 2` family with dimension-variable cap and proper face. Apply two explicit nonidentity substitutions and their composite. Check complete selected sections and the dependent second box over the chosen first section. Prove nonidentity and properness so the case cannot silently collapse to identity or total boundary.
3. Instantiate the original adapter under its original cap and Cofibration assumptions, retaining native clients and existing whole-operation classifier recovery.
4. Inspect generic hypotheses: component filling laws and primitive box/pairing laws may occur; whole selected-Sigma lawfulness or preservation may not.
5. Compare preparation and recurring caller obligations separately. If the telescope repeats alignment proofs, package local stage data. Build a global context/category record only when this comparison supplies concrete reuse evidence.

The local design fails this architectural experiment if both adapters still reconstruct the subtype-continuation argument, or exact recovery requires weaker cap, face, or whole-section observations. Excess preparation syntax is a maintenance cost to measure, not proof that shared mathematics is inexpressible.

## Independence and validation limits

I read the shared brief, full issue #627 JSON, applicable guidance, named native modules, existing example source, and the supplied #608 synthesis. I did not read other initial #627 reports, coordinate conclusions with assessors, or modify repository files. Source references were inspected in the checkout identified by the brief as `9aa0520591e7d107b63f9172a496fe7332b24cb8`; unrelated uncommitted Lawvere work was excluded. I performed text inspection and primary-source browsing. No candidate implementation, Lean build, proof audit, or author-effort measurement was executed. Recovery and adapter ergonomics remain experimental questions.
