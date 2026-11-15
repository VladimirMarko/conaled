# Practical construction transport (#461)

The two practical clients support useful composition through their existing
preservation theorems. Neither needs all-input diagonal representation.
The experiment adds checked compositions and a selected-feedback adapter,
retains both native clients, and gives a separating counterexample to replacing
representation with a fixed-value equation. It also adds two sufficient
alternatives to surjective code maps for #444's actual representation contract.

## Contract and source boundary

The [contracts](construction-transport-contracts.md) were frozen in commit
`b51827cb`, before new formal code. The [primary-source comparison](construction-transport-alternatives.md)
was committed as `8ece4a67` before the experiment. These build on accepted
revision `924542a1cdab7a3637a14fb9c61945b41fea77e4`, including #444.
The compiler sources, `AssemblyCutFold`, `SelectedFeedback`, `UniformOperations`,
and #109's scope were inspected at that revision. Existing source files and
statements remain unchanged, apart from public-entrypoint imports of new examples.

The new modules are [ConstructionTransport](../../Examples/ConstructionTransport.lean),
[DiagonalCoverage](../../SquareKit/DiagonalCoverage.lean), and its
[checked cases](../../Examples/DiagonalCoverage.lean). They are integrated
experiments, subject to the normal build and proof audit. The examples use
native APIs; no replacement universal recursion interface was introduced.

## Finite compilation and resource observations

`Fold.native` consumes the existing `squares_counted`: every finite integer
list produces the sum of its squares and cost `1 + 3 * length`. `visits`
retains the existing exact source execution length. `recovery` recovers this
unchanged contract through the identity observation map.

`scale 2` and `scale 3` are additive resource maps; both differ from the identity
at one. `composed_transitions` uses `Resources.reweight_run` on the executed
square-body transitions, including their visit charge. `compiled_reweighted_run`
also accounts for the compiled seed, using `reweight_bind`. `composed_result`
then identifies the observed pair as the original value and six times its cost.
The concrete `[2,-1,3]` case is `(14,60)` after reweighting, recovering `(14,10)`
before reweighting. These claims concern a specified charge model, not host
execution speed or allocation.

No new list induction was required. The caller supplies an additive observation
map and, for a numerical result, simplifies its action on the old cost theorem.
The existing fusion client still proves equality after erasing costs, while the
checked `[1,2]` executions cost six and seven. Thus a denotation square cannot
be used as a cost-preservation certificate. The scalar-sound but fold-unsound
backend in `RecursiveCompilation.bad_fold_law` also remains checked unchanged.

## Guarded feedback and quotient observations

`Feedback.native` consumes the existing compiler theorem equating the compiled
stream with the independent triangular recurrence. `selected` uses
`FunctionFeedback.guardedWitness`; its selected state equals that same compiled
stream (`selected_compiled`). `selected_native` reuses the compiler's fixed-point
equation and guarded uniqueness. It does not establish another recurrence by
induction. `every_selected` proves equality of the observed stream for every
admitted witness using `guarded_trace_unique`.

`quotient_chain` composes the constructor-preserving interpretations
`Nat → ZMod 4 → ZMod 2`. Each map loses information, with checked collisions at
four and two. `selected_quotient` carries the retained witness's observed stream
through the chain. `chain_parity` and `quotient_direct` recover the existing
direct parity interpretation. The natural stream is retained before the map;
noninjectivity rules out general recovery from the parity observation.

The author supplies zero/one/addition preservation and parameter/reference
compatibility to the existing `run_interpretation`. No additional solver,
coordinate induction, or code-coverage hypothesis is needed. The selected
feedback adapter adds a `Unit` input and stores the stream as output and state;
these are explicit packaging costs, not a demonstrated reduction in author time.
Guardedness supplies existence and uniqueness. A witness equation alone supplies
neither. The existing rejection of naked recursion and the zero coefficient map
remain in `GuardedStreamCompiler`'s checked examples. No asynchronous scheduler,
external-delivery claim, wall-clock bound, or continuous-time integrator follows.

## Coverage without surjectivity

`Map.Extension f s` asks for the selected representation equation only at target
inputs outside `f.code`'s image. On image inputs the original evaluation and
step laws already prove that equation. `selectedExtension` combines those two
parts, retaining exactly `f.code s.code`. `extension_witness` preserves its
value. `extension_comp` composes two such certificates; the code and witness
of sequential and composed transport agree. The certificate is relative to
one selected source row, not all possible representatives.

`imageMap` instead restricts target codes to the subtype carrying an image
witness. `selectedImage` reuses the original surjective transport theorem on
that restricted domain. It makes no assertion about omitted target inputs.

The unchanged `partialPresentation` counterexample fails `Extension`, but has
a selected image-restricted representative. A constant-true evaluator on
`Unit → Bool` gives an inhabited positive extension despite nonsurjectivity;
a second map to `Option Bool` exercises composition with another omitted input.
These are sufficient conditions. We have not proved a weakest coverage law,
a decision procedure for certificates, or an extension of arbitrary target
semantics. The extra certificate explicitly requires new target-side evidence.

## Why a single fixed-point interface was not adopted

`no_xor_representation` is a checked separation. With evaluator
`e a b = xor a b` and identity step, the value of `e false false` satisfies its
fixed-point equation. Neither Boolean row represents the diagonal at every
input. Thus there is no `Selected e id`, despite that fixed value. This rejects
the proposed automatic adapter from a selected fixed value to diagonal
representation for the same evaluator. It does not rule out other common
interfaces or deliberate encodings with extra hypotheses.

The list client uses finite execution and additive observations. The stream
client uses guarded unique solutions and constructor interpretation. #444 uses
a selected code representing an entire diagonal. `AssemblyCutFold` additionally
retains one partial-recursive program uniformly over its context realizer and
proves tracking through cut observations. A collection of independently chosen
programs would weaken that theorem. The new coverage results are total semantic
results and make no claim to supply computability. `UniformOperation` likewise
needs naturality, with an existing checked obstruction to arbitrary equivariant
choice. Those native obligations remain visible.

## Decisions and residual ownership

| Consumer or proposal | Decision | Obligations and proof reuse |
|---|---|---|
| Finite counted compiler | Adopt native route and composed resource observations | Additive laws transport executed observations through `reweight_run`; existing soundness/fusion/cost theorems remain public. No diagonal adapter or new induction. |
| Guarded triangular stream | Adopt native interpretation and selected-witness adapter | Constructor laws and guarded uniqueness transport the same stream. No surjective coefficient map is required. |
| Diagonal target coverage | Adopt bounded extension and image-restriction helpers | Off-image evidence or restricted input type replaces surjectivity; code and witness are retained. Callers still supply representation evidence. |
| Fixed-value equation as diagonal representation | Reject this proposal | XOR counterexample satisfies the former and has no instance of the latter. |
| General categorical recursion interface | Investigate under #235 and #109 | Compare adjoint folds and guarded trace on clients needing their additional laws. This experiment establishes no migration benefit or author-productivity advantage. |
| Computable recursion, new source syntax and incremental recursion | Defer to #109 | Preserve uniform code, partial evaluation, tracking, retained state and termination obligations. No new syntax or tracking result is delivered here. |
| Interpretation assistance | Input to #462 | The image/extension split supplies concrete obligations and a rejected case; synthesis and usefulness on independent tasks remain untested. |

#235 owns the unresolved shared-interface comparison and any later author trial.
#109 owns recursion/compiler extensions. Existing native APIs already remove the
recurring global proof work in these selected clients. The new work demonstrates
composition and exposes certificate obligations; it does not establish that a
universal wrapper would improve them. Parent reconciliation and any further
implementation tickets belong to the coordinating wave.

## Validation and statement review

Focused builds of both example modules pass, including their native imports.
The first attempt exposed a reversed application of uniqueness; the correction
uses the existing compiled solution equation. No intended client expectation
was changed. Full exact-candidate build, exhaustive proof audit and independent
Standards/Spec review are coordinated separately before acceptance.

Statement review checked universal list inputs, seed and visit costs, stream
coordinate equality, the retained selected state, quotient collisions, and the
order of both composed maps. Coverage quantifies over all omitted target inputs
for one selected row; the image-restricted result quantifies only over its
subtype. The inhabited positive cases satisfy those premises. The XOR theorem
asserts absence of a representation for that concrete evaluator, rather than
absence of fixed points or impossibility of every common framework.
