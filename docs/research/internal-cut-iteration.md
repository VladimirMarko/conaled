# Tracked cut iteration and extension-selected fixed points

[#387](https://github.com/VladimirMarko/conaled/issues/387) constructs the P3
iteration objects and conditional selection theorem in the assembly category.
The finite-cut algebra is initial, the finite/full-cut coalgebra is final,
and their structure maps have tracked inverses. The resulting strict algebra
with successor has a separate initiality theorem. A uniformly complete strict
algebra admits a tracked, context-dependent selected fixed point, with algebra
transport and parameter-substitution laws.

[P4 now constructs completeness of the intended uniformly realizable family](internal-complete-certificate-family.md).
The P3 selection theorem retains its general all-context completeness hypothesis.
The original lifted-natural examples below were conditional; P4 adds instances
using constructed completeness. P5's selected certificate comparison remains open,
so #371 is not complete.

## Source and model boundary

Van Oosten and Simpson describe the finite/full-cut assembly presentation in
§3, pp.266–268, of [*Axioms and (counter)examples in synthetic domain theory*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf).
Theorems 1.4–1.5 distinguish initiality for the lifting endofunctor from initiality
among strict monad algebras equipped with a successor. Definition 1.11 and
Theorem 1.13, p.244, use unique extension to select a fixed point. The development
below establishes the needed assembly constructions directly. It does not
import the paper's internal effective-topos principles as axioms.

Carriers lie in `Type u`; realizers are natural numbers and tracking applies
to every realizer of every input. Arrow equality compares carrier functions,
not program indices or runtimes. `ULift` places the cut carriers in the same
universe as their clients. No effective topos, universe classifier, exponential
object, or general local cartesian closure is assumed here.

## Cut objects and program transformations

[AssemblyCuts](../../SquareKit/AssemblyCuts.lean) defines `Cut e n` by

```
∀ k, (eval e k).Dom ↔ k < n
```

and `FullCut e` by termination at every input. The iteration object has carrier
`ULift Nat` with all indices realizing its finite cut. The final object has
carrier `ULift (Option Nat)`: `some n` denotes the finite cut and `none` denotes
infinity. In the *lift* of either object, outer `none` instead denotes undefined
computation. These two uses of `Option` must not be conflated.

The realizer relation constrains domains only. It neither fixes returned labels
nor supplies a finite bound. `cutCode` compiles canonical cuts computably in
the length, using one fixed recursive template. `shiftCode` removes the first
observation. Inclusion reuses the same realizer; zero and infinity use an empty
cut and a total program respectively. This is not a proof identifying the
finite-cut object with the encoded natural-number assembly or with an initial
chain colimit.

[AssemblyCutPrograms](../../SquareKit/AssemblyCutPrograms.lean) and
[AssemblyCutStructure](../../SquareKit/AssemblyCutStructure.lean) construct
roll/unroll trackers. Roll waits for the lifted input, then prepends a positive
observation to its returned cut. Unroll returns code which first waits for
membership of zero and then returns the shifted index. Both compositions are
identities, for finite cuts and for finite/full cuts. Successor commutes with
inclusion and fixes infinity.

## Initiality, finality, and strict algebras

[AssemblyCutFold](../../SquareKit/AssemblyCutFold.lean) constructs a single
recursive fold program on `(context realizer, cut index)`. Its recursive call
is delayed behind the cut's first observation. At the empty cut that delayed
program realizes bottom, so the algebra tracker must still return. At a
successor cut, induction proves the recursive result realizes the preceding
fold value. Mathlib's code recursion theorem supplies this program; it is a
tracking tool, not the selected-fixed-point theorem.

The underlying finite recursion specifies the expected values independently
of tracking. The proof establishes tracking without reading a cut's hidden
length. [AssemblyCutInitial](../../SquareKit/AssemblyCutInitial.lean) then proves
uniqueness and packages `cutAlgebra_initial` as Mathlib's `IsInitial` in the
endofunctor algebra category. The initial mediator into the final object's
roll algebra is exactly the constructed inclusion.

[AssemblyCutUnfold](../../SquareKit/AssemblyCutUnfold.lean) constructs the final
mediator's tracker. It emits a program whose observation at `k` performs `k+1`
successful coalgebra unfoldings. A partial-realization invariant relates these
programs to the independently defined finite observations. Descending
observations determine a finite length or infinity; the tracker does not
decide which. [AssemblyCutFinalValues](../../SquareKit/AssemblyCutFinalValues.lean)
proves the carrier equations and uniqueness, and
[AssemblyCutFinal](../../SquareKit/AssemblyCutFinal.lean) combines them with the
actual tracked mediator in `cutCoalgebra_final`, a Mathlib `IsTerminal` result.

[AssemblyCutStrict](../../SquareKit/AssemblyCutStrict.lean) derives the strict
map `ρ = σ ∘ μ ∘ L(σ⁻¹)` from P2's monad. On carriers, `σ` sends bottom to zero
and a defined `n` to `n+1`, while `ρ` sends bottom to zero and a defined `n` to
`n`. The latter satisfies the monad-algebra laws. `strict_successor_initial`
proves unique strict-algebra morphisms commuting with the chosen successor.
This differs from the preceding endofunctor initiality theorem.

[AssemblyLiftStrength](../../SquareKit/AssemblyLiftStrength.lean) retains a
context realizer while waiting for partial data. Together with the uniform
fold it supplies `strictIteration : Γ × I → X` for every admitted
context-dependent endomap `Γ × X → X`. Separate per-parameter choices of
tracking programs are not used.

## Uniform completeness and selection

[AssemblyCutComplete](../../SquareKit/AssemblyCutComplete.lean) defines
`CutComplete X` by bijectivity, for **every** assembly context Γ, of restriction

```
Hom(Γ × F, X) → Hom(Γ × I, X).
```

`cutExtend` extracts its unique tracked extension. Extension uniqueness proves
that extending iteration commutes with successor. Evaluation at infinity then
gives `cutSelected : Γ → X`, and `cutSelected_fixed` proves its fixed-point law.
The result is an admitted arrow of parameters, not just a family of external
solutions. `cutSelected_transport` preserves the selected result along a strict
algebra morphism intertwining the endomaps. `cutSelected_substitution` proves
compatibility with any tracked change of parameters. The corresponding
iteration and extension laws are available separately.

`cutSelected_identity` illustrates the distinction between selection and an
arbitrary solution: identity iteration selects the algebra's bottom. It does
not prove all identity fixed points equal. P4 now connects the all-context
contract to a tracked exponential restriction isomorphism.

## Checked cases and remaining work

[InternalIteration](../../Examples/InternalIteration.lean) checks empty and
length-three cuts, a length-three program returning label 99, a full program
which realizes no finite cut, finite unfolding through inclusion, and perpetual
unfolding to infinity. Context-dependent iteration retains selected 17; a
successor parameter change retains 18. Algebra transport and substitution are
exercised as full-arrow equations as well as selected-value instances.

The terminal assembly is proved uniformly complete and given a strict algebra,
so the conditional theorem has an actual inhabited instance. The lifted-natural
selection examples in the original P3 module remain conditional; P4 adds concrete
instances using its completeness theorem. They
separate identity's selected bottom from the distinct fixed point `some 17`.
The Boolean control proves impossibility of the **combined** complete and strict
algebra hypotheses admitting negation. It neither claims Boolean incompleteness
nor rejects computable negation as an assembly arrow.

P4 now supplies concrete all-context completeness for naturals and their lift,
function assemblies, the exponential comparison and the uniformly tracked
certificate family. P5 still owes that family's algebra, its internal countdown
functional and its selected-solution comparison. Native external clients retain
their existing contracts. This milestone establishes neither operational
countdown adequacy nor a productivity advantage.
