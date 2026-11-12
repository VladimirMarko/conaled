# Idealized targets and observable realizations

Issue [#502](https://github.com/VladimirMarko/conaled/issues/502) compares concrete mathematical interpretations, finite symbolic artifacts, supplied ordinary programs, and bounded observations. The connections have different preservation contracts. They do not form a mandatory hierarchy, and failure of one effective realization does not invalidate the mathematical interpretation.

The public clients are in [Examples/IdealizedTargets.lean](../../Examples/IdealizedTargets.lean). They reuse the source language and compilers from [the oracle-relative study](oracle-relative-computation.md), together with the existing rational interval compiler and real-point enclosure relation.

## Source and computation model

The primary implementation reference is Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`, specifically [PartrecCode.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/PartrecCode.lean) and [Halting.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/Halting.lean). These Apache-2.0 sources define the actual ordinary codes, evaluation, bounded evaluation, computability, and halting obstruction used here. Their SHA-256 hashes are respectively `3cfc059a7603aa3eb528f0cd231f99bceaea91e8a3563a233ad96b4b78def8c6` and `6c67e2a5a150abfebef589ffed73d9ce8876b54b5ae4f748952b1e1f1ea3d2fd`.

The prior oracle study records the historical Turing source and the limits of its modern halting adaptation. This delivery uses its already proved `haltingOracle_not_partrec`; it adds no new historical equivalence or physical uncomputability claim. It selects the noncomputable decision-operation alternative allowed by #502. The exact-real companion below makes a different, explicitly representation-relative observation claim.

## One source, different justified interpretations

`answerThenSucc` is the existing oracle source language's composition of successor with query. Under `haltingOracle`, its independent specification is `n ↦ some (haltingAnswer n + 1)`. `mathematical_interpretation` consumes the general interpretation theorem. `symbolic_preservation` consumes the existing artifact compiler theorem for the concrete list `[1,4,6]`. The finite list names an ideal query; it does not execute the halting operation. `arbitrary_function_interpretation` proves the same artifact correspondence for every supplied mathematical function `Nat → Nat`. This admits an all-functions interpretation without asserting an effective presentation of every such function.

`effectiveProgram` translates the same source with the supplied ordinary successor program as its query implementation. `effective_preservation` uses `toOrdinary_correct` and gives `some (n+2)` for every input. The executable translator receives actual code data. `two_substitutions` exercises composition of concrete realization substitutions under their matched oracle semantics.

For the ideal query itself, `query_realization_rejected` states that no ordinary `Nat.Partrec.Code` realizes `haltingOracle` on all indices. This is a proved obstruction in the specified model, unlike an implementation that merely has not been supplied. Mathematical interpretation and symbolic generation still have their own positive preservation theorems.

## Bounded observations and unknown

[OracleComputation/Observation.lean](../../Applications/OracleComputation/Observation.lean) uses Mathlib `Code.evaln` directly. `some v` reports a result; `none` reports unknown at that bound. Mathlib's bound guards intermediate numeric inputs and decreases in recursive/search cases. It is not a count of abstract-machine steps, and these results assert no execution-time estimate.

`observe_sound`, `observe_mono`, and `observe_complete` reuse `evaln_sound`, `evaln_mono`, and `evaln_complete`. A reported value belongs to actual partial evaluation; increasing the bound preserves that value; and every terminating result is eventually observed. `observe_primrec` retains the primary source's primitive-recursive implementation theorem.

`observeAnswer` forgets the returned value and reports answer one when evaluation of the encoded program at zero succeeds. `observeAnswer_sound` relates that observation to the exact ideal halting answer. Unknown imposes no answer constraint. `observe_divergent` proves that genuinely divergent programs remain unknown at every bound, but a single unknown does not prove divergence.

The public terminating effective program is unknown at bound one and returns two at bound two. Its intermediate successor input explains this difference. `unknown_is_not_divergence` retains both the insufficient-bound result and actual termination. The known divergent program from the oracle study remains unknown at every bound. Neither case permits interpreting unknown as the exact negative halting answer.

## Existence and program-producing converters

`answer_code_exists` gives a constant ordinary program for each individual correct halting answer. The witness is `Code.const (haltingAnswer n)`, whose evaluation is established by `eval_const`. The dependence on the noncomputable answer is visible.

`no_computable_answer_selector` proves that no computable function from indices to ordinary programs can choose programs that return those answers even just at input zero. Composing such a selector with Mathlib's partial-recursive universal evaluator would make the actual halting oracle partial recursive, contradicting the published obstruction. This permits arbitrary extensionally correct selected programs; it does not rely on canonical syntax or an injective encoding of answers.

The public `extraction_separator` places pointwise existence beside failure of uniform effective selection. When a natural answer is already supplied, `supplied_answer_constructor` gives the primitive-recursive constant-program constructor. Thus executable program construction and correctness of the supplied answer remain separate obligations. No use of classical choice is advertised as an executable converter.

## Exact values through rational enclosures

[Intervals/Observation.lean](../../Applications/Intervals/Observation.lean) adds `observeZero`, a total executable function on the existing rational intervals. An interval strictly below or above zero yields `some false`; the singleton zero interval yields `some true`; otherwise it yields `none`. `observeZero_sound` proves every reported decision correct for every exact real point satisfying the existing `ContainsReal` relation. No floating-point rounding or numerical tolerance is introduced.

The interval `[-1,1]` admits both real zero and real one. `no_exact_zero_decoder` proves that no Boolean function of an interval alone can decide zero equality for every admitted point. This is loss of information in the specified representation, independent of computability. It is not a theorem about all representations of real numbers, nor an undecidability claim for exact rational equality.

`observeZero_add` composes the observation with the existing real-point enclosure addition theorem. The public singleton sum case gets a justified nonzero result. `compiledBox` uses the existing typed compiler for `Arithmetic.shared`, on singleton inputs one and two. The independent source value is five. The compiler's enclosure theorem supplies admission, the concrete result is singleton five, and the observer supplies a negative zero decision. These links reuse the original relational compiler rather than replacing its proof with a concrete arithmetic calculation.

The existing cancellation example gives exact point value zero but enclosure `[-2,2]` from `[-1,1] + -[-1,1]`. `dependency_loss` preserves that calculation and its unknown observation. Mathematically exact functions need not have exact-decision observations through every valid enclosure implementation.

The inspected optional exact-arithmetic backend also supplies real-point compilation and bounds for logarithm and square-root atoms. Its existing `compile` is marked noncomputable. This delivery does not relabel it as an executable implementation; the new executable observer uses the existing rational operations. Rational endpoint arithmetic and comparison are exact. Arbitrary Cauchy-name access, exact-real equality algorithms, and their computability limits require a separately stated representation.

## Consequences for interpretation contracts

These clients require #493's proposed interfaces to keep specific admission and observation obligations visible:

- Mathematical source denotation and symbolic artifact correspondence are justified without demanding an ordinary executor for every primitive.
- Ordinary execution consumes a selected program and its correctness theorem. A proposition asserting existence cannot replace that data.
- Bounded positive observation preserves successful results, with unknown explicitly retained. It does not preserve arbitrary exact decisions.
- Enclosure preserves containment. A derived decision requires enough information in the chosen enclosure; composing containment laws does not manufacture an exact decoder.
- Composition requires matching observations and premises, as the existing oracle substitution and interval compiler laws demonstrate.

No general evidence API or fixed hierarchy is adopted, and #489 remains deferred. These proofs establish mathematical connections in Lean's metatheory. They neither assign all native functions an executor nor impose classical data operations on every target setting. A device model, numerical implementation, calibration evidence, or physical applicability would require its own assumptions and realization contract. A theorem about ordinary partial-recursive codes alone proves no physical impossibility.

## Validation scope

The focused build target is `Examples.IdealizedTargets`, covering the new library results and public positive and separating cases. Executable observations additionally have concrete reduction checks and the runtime command `direnv exec . lake env lean --run scripts/test-idealized-targets.lean`; exact committed acceptance requires the repository's full build, exhaustive proof audit, and independent Standards and Spec reviews. The implementation handoff records those outcomes separately from this mathematical account.
