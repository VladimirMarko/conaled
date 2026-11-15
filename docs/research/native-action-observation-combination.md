# Native action and observation combination

[#437](https://github.com/VladimirMarko/conaled/issues/437) constructs the
bounded action/observation case from the [#431 paper
assessment](restricted-model-combination.md). The implementation is
[ActionObservation.lean](../../Applications/ModelCombination/ActionObservation.lean),
with independently specified inputs and checked callers in
[NativeModelCombination.lean](../../Examples/NativeModelCombination.lean).
Inspected published base: `3601424ed036751053ac34463092cce01cad2d4f`.

The [contract](native-model-combination-contract.md) froze both uses before the
interface. Native Boolean and list meanings were then checked before writing
the construction. Those meanings already follow from native definitions; the
new obligation was connecting them to exact joint recovery and the rejecting
cases, not reproving their possibility through a generic signature language.

## Construction and exact recovery

Inputs are M with its existing monoid operations, a native MulAction M X and
point x0, independent Y/y0 and D/d0, an observer o:Y→D, and supplied e:X≃Y
with e(x0)=y0. `combine` uses X as its state carrier and retains M, its action,
x0, D and d0. It constructs `out := o ∘ e`, identity left recovery, and right
recovery e. Cancellation proves right recovery. Neither the combined model,
its final recovery equations nor its mixed law is an input.

`Combination` records the result and its recovery contract. It also admits
alternative joint carriers Z: actual equivalences Z≃X and Z≃Y, preserved
points and result constant, preserved action through the left identification,
and observation recovery through the right identification. This is a result
contract, not a generic model-signature hierarchy. Its generality is used to
state the negative cases over every putative compatible presentation.

`left_reduct` and `right_reduct` recover the complete action and observation
functions. `overlap` composes the recovery equivalences and `overlap_point`
proves preservation of the common point. `mixed` derives the action/observation
composition law from `mul_smul`; the observer has no new algebraic premise.
`output` and `action_output` force the observed values through any fixed supplied
overlap, which is the comparison used for alternative presentations.

Equality is Lean equality of functions and values through explicit equivalences.
It is neither type equality X=Y nor equality of independently encoded records.
The independent universe levels of M, X, Y, D and Z are retained. Both inverse
maps are supplied data; no representative selection, quotient or classical
choice extracts them. The constructor is computable from computable inputs;
it does not prove arbitrary input operations computable. No observer injectivity,
invariance or equation o(y0)=d0 is assumed.

## Native callers and rejections

The first caller uses Mathlib's `Multiplicative Bool` and Boolean-ring XOR
addition, with the standard action type-tag instance. Its state is Bool; the
independent observer domain is Fin 2. An explicit equivalence checks both
inverses and preserves false/zero. The constructed output after true is true;
a second true action returns false using the universal mixed law. A valid
variant chooses result constant true while the point observes false, rejecting
an unintended constant-observation premise.

The second caller uses `FreeMonoid Nat` under append and its prefix action on
List Nat. The independent observer lives on List Nat×PUnit and returns length.
Prefix [8,9] on state [4] retains state [8,9,4] and observes 3. Complete right
recovery still retains list order even though length is noninjective. This is
an unbounded-state, noncommutative-action use of the same construction;
`List.length_append` remains the local observer theorem.

The singleton/two-element case supplies a valid native singleton action and
Boolean observer. `no_singleton_combination` rejects any `Combination` because
its two recovery equivalences would produce an impossible PUnit≃Bool. This
rejects invertible recovery of these supplied components, not separate
satisfiability or a weaker lossy pairing.

`no_invariant_alternative` quantifies over any joint carrier and any result
satisfying the same public contract and Boolean/Fin 2 overlap. Its observation
after true at the recovered false state is true, while the initial observation
is false. A separately constructed flipped presentation has the same overlap,
point true, and a different raw output function; it satisfies the contract and
also consumes this rejection. The conclusion therefore does not rely on
requiring the canonical record encoding or raw function to be unique.

## Statement review

| Declarations | Reviewed mathematical content |
|---|---|
| `Combination`, `combine`, `combine_overlap`, `combine_out` | Actual output and all recovery witnesses are constructed from components/e/point proof. No final model or law is an input. Fixed M/action/D retain their native operations. |
| `overlap`, `overlap_point`, `out_eq`, `left_reduct`, `right_reduct` | Invertible maps recover full functions, points and result constant; observation need not be injective. |
| `mixed`, `output`, `action_output` | Mixed associativity follows from action laws. Fixed overlap forces observations in every valid joint presentation; invariance is absent. |
| `boolFin`, `boolObserve`, `bool_point`, `bool_native`, Boolean construction/recovery/once/twice | Different carriers, explicit inverse equations, actual XOR meaning, and generic-law connections. |
| `differentConstant`, `independent_result_constant` | Inhabited positive construction with unequal point observation and result constant. |
| List action, `listPair`, `lengthObserve`, native equations, `listCombined`, prefix and recovery callers | Ordered list meaning fixed before interface; existing append monoid/action laws and local length law reused. Noninjectivity does not collapse recovered state. |
| Singleton action, `singleton_overlap_impossible`, `no_singleton_combination` | Side components are valid; a putative result of the same public contract induces the contradictory equivalence. |
| `no_invariant_alternative`, `boolean_not_invariant` | Same retained action, observer and supplied overlap, universally quantified alternative Z; concrete true/false witness. |
| `flipped`, `flipped_overlap`, `flipped_not_invariant`, `presentations_differ` | Actual alternative satisfies all recovery fields and same overlap, while raw output differs; generic rejection still applies. |

## Reuse, setup and remaining obligations

Direct native `o ∘ e` already gives the canonical output and cancellation
already gives recovery. `combine_out` preserves that exact comparison. The
result contract adds explicit recovery bookkeeping and supports statements
about alternative carriers. Both uses reuse that bookkeeping, the induced
pointed overlap and the mixed/output-forcing theorems. Each still supplies its
own equivalence, inverse proofs and point equation. The Boolean case needs its
explicit encoding; the list case needs its prefix action and length theorem.

These two uses do not justify a generic signature framework: the direct
function interface remains sufficient for this operation family. No author
trial, timing measurement or productivity ranking was performed. The report
compares mathematical obligations and actual API use, not line counts.

Current `RepresentationExtension.Models.expand` constructs product/quotient
extensions for every admitted old model and proves `reduct_expand`. Here the
observer is independently supplied, and combination is conditional on the
pointed overlap. Current synchronization constructs agreeing representations
through `Comma.Exact`; it does not promise invertible recovery of both entire
input carriers. Institution connections carry model/reduct/evidence maps for
supplied settings; they do not construct this joint model. No adapter to those
interfaces, selected diagonal construction, or resource-additive certificate
is needed or claimed.

#288 retains broader model-combination research and automatic overlap discovery;
#290 retains any theory-publication/calculus bridge; #235 retains shared-interface
or architecture adoption. Syntactic conservativity, general signature-amalgamation
functors, spatial sheaf gluing and arbitrary interaction-law synthesis remain
outside this completed bounded construction. No new implementation of those
obligations is scheduled by this result.

## Source and validation boundary

The primary versions from #431 were inspected again on 2026-11-11:
Schröder et al., [author-hosted CASL PDF](https://www.cs.ox.ac.uk/people/bartek.klin/papers/tcs05.pdf),
§2 pp. 7–8 defines signature-pushout/model-pullback amalgamation; §5 Example 4
shows why implicit subsort sharing can fail. Diaconescu–Stefaneas,
[TCS 379 (2007), 210–230](https://www.imar.ro/~diacon/PDF/ks_tcs.pdf), §2.3/§2.5,
describes named first-order signatures and model amalgamation. These are
published general accounts; the new Lean result is only the explicit native
action/observation construction. It does not formalize their full syntax or
amalgamation theorem. [Stacks tag 00AK](https://stacks.math.columbia.edu/tag/00AK)
requires spatial cover and cocycle data for sheaf gluing, which are absent here.

Downloaded PDF SHA-256 values are respectively
`62ba17b4dd5c278227790be559ba9c8c451b508796e664efed7bb4bee84ca46f`
and `8a85bd2836d61de75eef219541f0fa272b6b17e01bd2d8238d13ab3d5de63f47`.
The accepted paper report remains historical evidence with a link to this
implementation. No claim of full general amalgamation is promoted to Lean.

Focused validation checks both new modules with `autoImplicit false` and
`warningAsError true`. The public entrypoint imports the caller before module
documentation. Final guarded full build, exhaustive audit, exact candidate
verification and independent Standards/Spec reviews belong to the enclosing
orchestration; their receipts remain distinct from this author statement review.
