# Model combination: contract and foundations assessment

Retain the native construction and its local recovery contract. The inspected code establishes the stated action/observation capability, including alternative presentations and the two rejection results. No missing primitive law emerged. Investigate small comparison and transport helpers before adopting a signature framework. The present examples exercise different carriers, actions and observers, but the same operation family; they do not yet expose repeated axiom transport across independent families.

This assessment uses pinned source `e80c51d968925be3809ba3acc3259de7041b504b` in `../source`. References below name declarations and their source lines at that revision. It is a source inspection and mathematical derivation, without a fresh Lean build or new checked proofs.

## Evidence for retaining the contract

`Applications/ModelCombination/ActionObservation.lean:41`, `combine`, constructs the output as `o ∘ e`, with identity left recovery and the supplied pointed equivalence as right recovery. The constructor takes neither a completed joint model nor its final recovery equations. `Combination` at line 24 separately describes admissible presentations on arbitrary `Z` with its supplied native action. This distinction is useful: the constructor is small while the contract supports quantification over presentations other than the chosen construction.

The strongest retention evidence is the combination of `action_output` (line 86) with `no_invariant_alternative` and `flipped` in `Examples/NativeModelCombination.lean:138` and line 150. These demonstrate that observed action values are forced by the supplied overlap in every admissible presentation, even though raw output functions and chosen points can differ. `presentations_differ` at line 171 prevents confusing this result with uniqueness of the record or its raw output function.

The native list consumer is also consequential. `prefix_observation` at example line 91 uses the generic recovery theorem and the independent `List.length_append` consequence. `retains_ordered_state`, `right_recovers_order`, and `observation_not_injective` at lines 108–119 show that full state recovery remains available despite a lossy observer. Replacing the right equivalence with equality of observed lengths would lose an exercised guarantee. Boolean callers at lines 61–78 retain direct native XOR meanings.

## Obligations that already follow

The existing proof bodies settle several apparent missing-law questions:

- `mixed` at application line 81 uses only the native `mul_smul` law. It needs no observer invariance, injectivity, overlap coherence, or extra combined action law.
- `left_reduct` and `right_reduct` at lines 72 and 78 derive complete function recovery from the stored pointwise laws. Function equality follows by extensionality; requiring both versions as fields would duplicate evidence.
- `overlap_point` at line 61 derives preservation of the common point. `out_eq` at line 68 derives forward observation preservation from inverse recovery. Neither needs a new field.
- Equivariance of `left.symm` follows from `left_action` and injectivity of `left`: apply `left` to both sides of `left.symm (m • x) = m • left.symm x`, then cancel. This is a paper derivation, not a newly checked declaration.

Two further consequences are useful candidates for helpers, if callers need them. Both are derivable, so neither should become an input obligation.

First, for combinations `C` on `Z` and `C'` on `Z'` with equal induced overlaps, define `h = C.left.trans C'.left.symm`. This equivalence preserves the chosen point and action. The equality of overlaps gives `C'.right (h z) = C.right z`; `out_eq` then gives `C'.out (h z) = C.out z`. It is unique among functions commuting with the left recovery because `C'.left` is injective. This is uniqueness relative to recovery data, with no claim that the two carriers or records are equal. It follows by cancellation from the existing contract, without an additional coherence field.

Second, for `C.overlap = e`, universal output invariance is equivalent to `∀ m x, o (e (m • x)) = o (e x)`. The forward direction substitutes `C.left.symm x` into invariance and uses `action_output`/`output`; the reverse direction writes any `z` as `C.left.symm (C.left z)` and uses the same theorems. Thus the exact extra obligation for an invariant variant is a property of the unchanged supplied action and observer. Calling invariance a law of a newly added operation would obscure this distinction. Conversely, adding an independent binary operation would introduce operation data and its own laws; its compatibility with the action would remain a separate question.

## Scope boundaries and concerns

No established defect was found in the bounded contract. The following are limits or adoption risks.

**The overlap is supplied structure.** `combine` requires an actual `X ≃ Y` and point equation. `Combination.overlap` shows that such a pointed equivalence is also necessary for any result. Together these give a paper-level necessity/sufficiency characterization of existence for this operation family. They do not discover an equivalence, select one from a proposition, or prove that the supplied observer is computable. The explicit `boolFin` and `listPair` inverses at example lines 22 and 42 are therefore meaningful input evidence, not redundant ceremonies.

**Observation equality is weaker than recovery.** The right map is invertible even when `o` is not. `no_singleton_combination` at example line 132 consequently rejects every candidate joint carrier, using the induced impossible `PUnit ≃ Bool`. A product construction or relational observation contract could answer another useful question but would not preserve this exact recovery requirement. This is a mathematical limit of that requirement, not a representation failure of `combine`.

**Constants remain independent.** `d0` is explicitly retained; no equation relates it to observation of the state point. `differentConstant` and `independent_result_constant` at example lines 81–85 are inhabited counterexamples to adding such a requirement. The duplicated result field and its equality are eliminable bookkeeping in principle, but removing them has no demonstrated client benefit and would change the presentation API. Keep them unless a concrete abstraction benefits from deriving that projection.

**The mixed theorem is deliberately modest.** It applies a function to an existing action equality. It does not establish a new distributive or interaction law, nor provide generic transport of equations with several independently introduced operations. The implementation record already states this boundary. A future generic proposal must demonstrate more than renamed instances of `o ∘ e` and `mul_smul`.

**Equality is fixed here.** The recovery statements use Lean equality of values/functions through explicit equivalences. They do not cover a weaker observation relation, quotient-only recovery, or relevant higher identity witnesses. Nothing in the inspected clients demands those features. Extending this interface globally without stating that scope would be a risk; retaining it as a bounded native interface is consistent with the inspected ADRs 0001, 0002 and 0010.

## Smallest useful alternatives and discriminating work

The cheapest continuation is to retain `combine` and add only a demanded presentation-comparison helper or the invariant-observer characterization above. Their acceptance evidence should reuse `flipped` to show transported comparison without raw equality, retain the noninjective list observer, and retain the singleton and invariance rejections. Such helpers would reduce comparison bookkeeping without imposing new mathematical premises.

Before selecting a broader interface, choose a client whose independent right component has a genuine operation and law. A proposed discriminating family is an independently presented associative binary operation `b : Y → Y → Y`, with no compatibility axiom relating it to the left action. Given the same explicit `e`, its transport is `bX x x' = e.symm (b (e x) (e x'))`. Cancellation transports associativity; the left action remains native. This is a proposed experiment and paper derivation, not existing implementation evidence. The selected point should have only the role specified by that client's theory; making it a unit would add an unjustified law unless requested.

Compare direct transport, a selected reusable transport helper, and a signature formulation on that same client. Record separately the independent input proofs, generated operation laws, recovery/comparison work, and any new interaction requirement. Require recovery of the existing Boolean and ordered-list callers. Include a noncommuting action/operation case to ensure the interface does not silently require compatibility. A successful toy associativity example would show feasibility; evidence for shared architecture requires recurring obligations in the intended client and an observed reduction after accounting for setup and native adapters.

## Evidence and exposure limits

I inspected both complete Lean modules, their consumers located by repository search, the two supplied research records, the language direction, glossary, architectural guidance, and relevant ADRs. Search found the native combination consumers in `Examples/NativeModelCombination.lean` and its public-entrypoint import. This does not prove there are no external clients.

No code was changed, experiments run, issues created, or other lens reports read. No prior involvement is known in this fresh task context; the supplied brief and repository reports shaped the questions. Fresh context does not establish independent assumptions or model diversity. I have made no new external theorem claims: the proposed derivations above are explicit local mathematical arguments. The external amalgamation and sheaf-gluing citations in the repository reports were not independently revalidated here, so their general theorems are not premises of this recommendation. Fresh compilation, a checked comparison helper, and a third-family author comparison remain missing evidence.
