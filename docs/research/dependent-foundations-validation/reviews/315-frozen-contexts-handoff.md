# Frozen source contexts: implementation handoff

Root implemented only `SquareKit/Internal/DependentJudgments/FrozenContexts.lean` in315, then released it to main315 for the existing implementation/review loop. SHA256: `41893bbbb7c1487e844aacb18634bd81299ff2e46745e878647565d5ede873d1`. No root edits remain planned.

## Intended claims and checked uses

`Display` retains a formation derivation for each iterated extension. Its pullback uses existing source `Sub.lift`; its square is a constructed substitution, not a new primitive or an assumed compatibility theorem. `square_projection` derives the commuting square from pairing/projection and associativity. `weakenTerm_square` transports a base term through the entire tail. `Variable.preserved` proves retention of every selected binder. These are source derivations independent of a universal model annotation index.

The `Points`, `OnePath`, `Parallel`, `Homotopy`, `WithQ`, and `Input` construction stages form the actual displayed context `x,y,z,p,p′,h,q,u`. Their reindexing methods retain the dependent B family through the lifted map and convert Id families with the admitted source equations. `Signature` permits a schematic base context; setting it to source empty gives the frozen closed signature. No terminality, unique empty substitution, object Sigma, or equality reflection is assumed.

`Signature.sigma_typed` duplicates x into the y slot by a section and pulls back all later binders. `tau_typed` duplicates x into the remaining z slot and pulls back its later binders. `sigma_y`, `sigma_x`, `sigma_z`, `tau_x`, and `tau_z` establish the displayed assignments. `delta_loop`, `delta_loop′` (Lean spelling `delta_loop'`) and `theta_loop_q` derive their loop types. The five pairs of `sigma_*_retained` and `tau_*_retained` equations preserve p, p′, h, q and u as the corresponding fresh binder data. They do not replace paths or higher witnesses by reflexivity.

These equations use generated judgmental equality. The path and homotopy variables remain object-language data with their source typing. Native proof irrelevance is not an assumption of these source equations; actual observable distinctions depend on the supplied interpretation. Groupoid numeric observations belong to the separate concrete example. The source module alone does not discharge the higher-model gate.

`FrozenMemo.lean`, implemented by maps315, consumes these actual maps in all seven payload/type/substitution equations and fresh reconstruction results, including the dependent action and its transported source. Thus the checked maps are used by the frozen argument, rather than merely supplied as unrelated examples.

## Statement review

Reviewed all new constructions against the frozen memo: parameter order and substitution direction; B over the extended A context; parallel p/p′ and the dependent type of h; retention of q and u; y=x followed by z=x; distinction between object reindexing and raw metavariable substitution. No field requests the final preservation equation. The signature's family premises are the author inputs, not extra context-map assumptions. Each selected binder is covered by the generic preservation theorem and its named specialization. Concrete semantic inhabitation is supplied by the ongoing native/groupoid examples; no standalone model-existence or higher capability claim is made here.

## Validation and implementation evidence

- Direct Lean check of the full module passed, including with a diagnostic `maxHeartbeats=20000` setting. That lower diagnostic setting is not added to source.
- Focused FrozenMemo build passed837jobs, including FrozenContexts (1.9s) and FrozenMemo (1.4s). Log: `/tmp/maps315-frozen-build.log`. Earlier builder checkpoint passed828jobs in `reviews/315-frozen-contexts-build.log`.
- Targeted transitive axiom queries for sigma/tau typing, generic variable preservation, retained h and the final q loop found only `propext`, `Classical.choice`, `Quot.sound`; see `reviews/315-frozen-contexts-axioms.log`. These targeted checks do not replace full candidate acceptance.
- Full build, exhaustive audit, independent Standards/Spec review and candidate verification remain main315/orchestration responsibilities.

A failed direct context-equality proof (`delta_total` by rfl) caused kernel deterministic timeout while expanding the concrete tail. Likewise the first concrete head-variable proof expanded its square unnecessarily. The final code proves `Display.replaceHead` and `head_square` at an abstract tail, then specializes them. This preserves the same source maps and avoids expanding the concrete derivation payloads during comparison. The failed declarations are absent from completed source; this paragraph is an authored diagnostic account, not a reconstructed raw tool log or a performance benchmark. The module uses a noncomputable section for its Type-valued derivation constructions and makes no execution claim.

Missing intermediate oleans during early checks were explained by a concurrent in-progress source failure (`pathSub` name shadowing in DerivedReindexing), subsequently corrected by its owner and rebuilt. No integrity-guard, stale-artifact or Lake corruption claim follows.
