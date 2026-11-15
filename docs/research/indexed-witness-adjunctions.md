# Indexed witnesses from existing adjunctions

Issue [#351](https://github.com/VladimirMarko/conaled/issues/351), under
[#289](https://github.com/VladimirMarko/conaled/issues/289), extends the existing
slice adjunctions with selected dependent-sum clients. It does not introduce
another generic adjunction interface or require dependent products for sums.

## Independent contract and checked client

For a context `γ`, indices `I γ`, and values `P γ i`, the specification is
`Selected γ = Σ i : I γ, P γ i`. Its truth observation is
`Nonempty (Selected γ)`. Selection includes the actual index and value; neither
an existence proof nor equality of existence propositions supplies that data.

[IndexedSumFamilies](../../SquareKit/IndexedSumFamilies.lean) specifies those
families before defining their slice realization. The index display is
`Σ γ, I γ → Γ`; the value display is `Σ a : (Σ γ, I γ), P a.1 a.2 → Σ γ, I γ`.
Reindexing uses Mathlib's chosen categorical pullbacks. The native specification
does not depend on their representation.

The [checked example](../../Examples/IndexedWitnessAdjunctions.lean) uses
`I n = Fin (n + 2)` and `P n i = Fin (n + i.val + 1)`. Substitution along
`σ n = n + 1`, then `τ n = 2 * n`, at context `2` reaches context `5`.
The selected index is `3 : Fin 7`, and the selected value is `8 : Fin 9`.
`categorical_result` proves preservation of the complete dependent value through
both actual sum/base-change isomorphisms. The general `twice_base` theorem also
retains the new context. This is not merely two calculations of existence.

The obligation exposed by this example was the connection between native
selected pairs and the already constructed categorical comparison. No new
adjunction existence theorem was needed. `encode_value`, `transport_value`, and
`reindex_value` discharge the representation bookkeeping; `twice_value` combines
them. The categorical result calls this general theorem, while `native_result`
records the independently computed expected index and value.

## Reuse and capabilities

| Required operation | Existing data used | What is not required |
|---|---|---|
| Substitution | `Over.pullback`, from chosen pullbacks | Neither a dependent sum nor a dependent product right adjoint to substitution |
| Dependent sum | `Over.map g ⊣ Over.pullback g` | No `Π`, exponentiability, or local cartesian closure |
| Dependent product | `Over.pullback f ⊣ R`, as in `ExponentiablePullback` and `SheafDependentProduct` | Not requested by this sum client |
| Invertible sum/base-change comparison | `DependentBaseChange.leftComparison h`, with `h : IsPullback ...` | Commutativity alone does not suffice |
| Change of chosen sums | `Adjunction.leftAdjointUniq`, with both actual adjunctions | Equality of representations is not presumed |

The imports include the older dependent-product development because
`DependentBaseChange` houses both comparisons. The new sum declarations have no
hypothesis supplying a product right adjoint. A module import is not a semantic
capability requirement.

[IndexedSumBaseChange](../../SquareKit/IndexedSumBaseChange.lean) adds the forward
comparison for any commuting square and proves it is the existing
`leftComparison` when the square is a pullback. The generalized-point theorem
`selected` is valid in every category with pullbacks, for every parameter object
and compatible pair of arrows. Type-valued fibers instantiate that result's
value and base equations without collapsing witnesses.

[IndexedSumChoices](../../SquareKit/IndexedSumChoices.lean) extends the existing
`AdjointComparison` namespace with the dual left-adjoint transposition law.
`withSumChoices` transports the existing comparison through canonical
left-adjoint uniqueness. `choices_agree` states the commuting equation for
changing both sums before or after base change.

The alternative sum carrier is `PUnit × X.left`. Its adjunction is transported
from the original map/pullback adjunction through the explicit tagging natural
isomorphism. `canonical_tagging` identifies the resulting canonical uniqueness
comparison with tag insertion. `taggedFirst_value` uses `choices_agree` to show
that changing both sums before base change retains the original index and fiber
value. This tests a different carrier, not just a second name for an unchanged
functor. It does not claim arbitrary choices are definitionally equal.

The previously constructed right-adjoint comparisons remain available for
clients that request products. `SheafDependentProduct.baseChange_comparison`
uses `AdjointComparison.mate` for both choices, and
`ExponentiablePullback.squareAdjunction` constructs a product after pullback.
This experiment reuses the corresponding sum infrastructure without duplicating
those product proofs.

## Failure controls

`no_selection_reconstruction` proves that no function from `Nonempty Bool` can
recover both selected Boolean inputs. Proof irrelevance makes their truth
observations identical; their values remain distinct. This rules out preserving
selection through that erasure, not choosing some inhabitant classically.

`NonPullback` uses a commuting square with upper-left corner `Empty` and the
other three corners `Unit`. Its sum comparison has empty domain and inhabited
codomain, so `not_invertible` rejects it. `not_pullback` independently refutes
the universal property using the pair of identity arrows from `Unit`.

The same example also checks the warning about mates: `invertibleMate` is the
mate of that failed sum comparison under the actual map/pullback adjunctions.
Every component lies over `Empty`, so it is invertible. Applying the inverse
mate equivalence recovers the noninvertible comparison. Thus even an actual
invertible original transformation does not justify declaring its mate
invertible. The older product base-change proof instead uses an iterated-mate
identification with conjugation of a proved isomorphism; that stronger argument
remains necessary.

## Obligation comparison and limits

Native families make this particular calculation short: substitution is
precomposition, and the selected pair's two projections compute directly. The
categorical route introduces display objects, pullback encodings, and equations
connecting projections to their native values. Those setup obligations are real.

Once connected, the client reuses naturality and invertibility of the existing
sum comparison, actual adjunctions, generic reindexing of arrows, and canonical
comparison between different sum representations. It does not re-prove the
universal property or naturality for each selected value. The second
substitution and tagged representation exercise that reuse. No author trial
was run, so this is an accounting of obligations, not measured productivity.

Statement review checked the quantifier scopes in `selected`, the full dependent
value equality in `twice_value`, and the explicit pullback and adjunction
hypotheses in `withSumChoices`. The finite client satisfies the hypotheses with
actual canonical pullbacks and a transported adjunction. The negative controls
separate commutativity from the pullback property and truth from selection.
Lean equality is used for host values and arrows here. No claim is made about
arbitrary higher identities, local universes, mode-based compiler syntax, or
all mathematical settings.

All declarations are reachable from `SquareApplications`; the normal candidate
build and exhaustive proof audit cover them. The remaining architectural
question under #289 is which additional consumers justify a common indexed
interface beyond these existing functors, adjunctions, and canonical maps.
