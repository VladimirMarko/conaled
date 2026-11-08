# Internal selected certificate solver

[#389](https://github.com/VladimirMarko/conaled/issues/389) constructs the P5
provider in the assembly slice developed for [#371](https://github.com/VladimirMarko/conaled/issues/371).
Its countdown is an admitted internal arrow. Selection comes from extension
along finite cuts into full cuts, evaluated at infinity. The resulting partial
state equals the independently specified external selected solution, including
its chosen value and entire trace. No external fixed-point operation defines
the internal solver.

## Setting and equality

The concrete provider uses `Assembly.{0}`. An object has a small carrier and
an inhabited natural-number realizability relation. A morphism carries one
partial-recursive tracker valid for every realizer of every input. Contexts are
arbitrary assemblies; neither a coding of their carriers nor arbitrary external
maps are assumed. Hom equality is equality of underlying functions. Internal
partial-natural values are `Option Nat`; their realizers are program indices,
and `none` is realized by divergence. Equality of certificate states means
pointwise equality of `Part (Cert n k)`, including each value and trace.

The common complete state object is
`D = function (encoded Nat) (programLift (encoded Nat))`.
It contains uniformly tracked partial-natural sequences. The bounded fiber
`boundedSequences n` requires every defined value at coordinate `k` to be
less than `n+k+1`. P4 identifies this with the independently stated uniformly
realizable subspace of the native external certificate states. The all-states
external client remains unchanged. Its diagonal nonuniform state is still
excluded from the internal family.

## Constructed algebra and countdown

[AssemblySequenceAlgebra](../../SquareKit/AssemblySequenceAlgebra.lean) constructs
`sequenceFlatten : L D → D` using lifting strength, lifted evaluation,
monad multiplication and currying. At coordinate `k` it sends outer bottom to
bottom and `some q` to `q k`. Thus generating a coordinate does not wait for
the outer partial sequence. The unit and associativity laws are checked against
the P2 monad, as are bounded-fiber algebras, their strict inclusions and the
strict value-shift maps. Outer bottom and a defined bottom sequence have the
same flattened result; they are distinct inputs to the algebra.

[AssemblyCountdown](../../SquareKit/AssemblyCountdown.lean) builds the arrow
from tracked finite control, evaluation, predecessor and lifted successor:

```
g(enabled, seed, q)(k) =
  if enabled then
    if k = 0 then some seed else map succ (q(k-1))
  else q(k)
```

Both branches supply partial values as data. Producing a program for an
unselected coordinate does not execute that partial computation. Bounds are
preserved when `seed ≤ capacity`. `countdown_forget_step` identifies this
arrow with the original external `runStep`, on full records.

## Selection and uniform membership

The finite iteration theorem computes coordinate `k` after `fuel` steps as
`some (seed+k)` exactly when enabled and `k < fuel`, and bottom otherwise.
[AssemblyCutWait](../../SquareKit/AssemblyCutWait.lean) then supplies a tracked
observation of a finite/full cut: emit a program which runs the cut realizer
at input `k`, discards its returned label, and returns `k`. A full cut succeeds
at every coordinate; no length or termination oracle is used.

[AssemblyCountdownExtension](../../SquareKit/AssemblyCountdownExtension.lean)
adds the seed under the lift and handles the enabled flag. This constructs a
tracked arrow `Γ × F → D` whose finite restriction is the strict iteration.
Extension uniqueness identifies it with `cutExtend`. Evaluating at infinity
therefore proves `countdown_selected`; this is not an assumed classifier or
completeness field.

[AssemblyCountdownFamily](../../SquareKit/AssemblyCountdownFamily.lean) proves
membership of every finite iterate and uses P4's `bounded_extension` to retain
the context-dependent bound at infinity. Selection factors to a tracked
section of the actual varying family. It also agrees with selection inside
each fixed fiber, by strict-inclusion transport. There is no ordinary algebra
on the total varying family with an arbitrarily chosen bottom capacity.

[InternalCertificateSolver](../../Examples/InternalCertificateSolver.lean)
proves `solver_external_solution` and `solver_uniform`. The former equates the
internal result with the unchanged external cpo solution; the latter proves
that the chosen external state has a uniform realizer. `contextualSolver`
composes the selected family section with P4's tracked comparison isomorphism.

## Transport and controls

`countdown_shift_square` is a local equation between the countdown and the
strict sequence-shift algebra map. `boundedCountdown_selected_shift` applies
P3's `cutSelected_transport` to that equation. The two successive parameter
changes in `solver_two_shifts` compose these local transport results before
observing a closed-form answer. `solver_substitution` uses P3's all-context
substitution theorem; repeated substitution and varying-family reindexing are
also checked. No extra slice-completeness assumption is added.

[InternalCertificateControls](../../Examples/InternalCertificateControls.lean)
checks the following consequences:

- Starting at capacity 1 and seed 0, the proper changes `(capacity + 1, value + 0)`
  and then `(capacity + 2, value + 1)` yield value 3 and trace `[2,1,0]` at coordinate 2.
- Seeds 0 and 1 have equal termination domains but distinct full selected records.
- Disabled countdown is the identity; its selected solution is bottom, although
  identity also has defined fixed points.
- Fuel 2 at coordinate 2 is unknown, while the selected enabled answer is defined.
- Cut programs may return label 99; the observation discards that label.
- The unique-certificate client is recovered by a declared partial observation,
  with a uniform program for its coordinates and equality to its external solution.

The unique observation waits for a successful input and returns the older
specification's value `n` with its canonical trace. It is not an equivalence
between certificate types. Erasing a successful value to its domain would not
preserve the varying client's selected result.

## Source and acceptance boundary

Van Oosten and Simpson, [*Axioms and (counter)examples in synthetic domain theory*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf),
APAL 104 (2000), 233–278, provide the finite/full-cut construction (§3,
pp.266–268) and the extension-based selected solution (Definition 1.11 and
Theorem 1.13, p.244). The pinned PDF SHA-256 is
`066a36aa48fc38b5105637e8b77ef0b34de9e61751010492b922946b1ce9c2e2`.
P5 instantiates the already checked P3 construction with the actual P4
complete objects. It does not import a theorem about the entire effective
topos into assemblies by renaming its hypotheses.

| #371 acceptance obligation | Checked evidence |
|---|---|
| Concrete category, admissible maps and chosen lift | [P0 model inventory](internal-sdt-prerequisites.md), `Assembly`, `AssemblyLift` |
| Admissible partial-map classification and tracking boundary | [P1 classifier](assembly-partial-map-classifier.md), accepted #385 |
| Lifting monad and slice comparison | [P2 monad](assembly-lifting-monad.md), accepted #386 |
| Initial/final cuts, strict iteration, all-context selection/transport | [P3 iteration](internal-cut-iteration.md), accepted #387 |
| Constructed completeness, exponentials/retracts, varying uniform family | [P4 family](internal-complete-certificate-family.md), accepted #388 |
| Actual algebra, countdown, uniform selected comparison and two changes | P5 modules and cases linked above |
| Boolean restriction | `InternalIteration.boolean_not_complete_strict`: impossible combined complete-plus-strict-algebra hypotheses admitting negation; no blanket Boolean-incompleteness claim |
| Selected erasure and finite-fuel boundary | Equal-domain/distinct-record and unknown-versus-defined controls above |

This supplies the bounded assembly provider requested by #371, subject to
independent acceptance of P5 with its prerequisite evidence. It does not claim
a full effective-topos implementation, completeness of all assemblies, or a
selected solver for nonuniform external states.

Executable countdown adequacy remains separate. A next operational result
would have to specify a machine and its evaluation relation, connect its
program semantics to these trackers, and prove the desired observation
correspondence. Existence of trackers and finite-iterate equations alone do
not provide that theorem, a divergence decision procedure, or a productivity
measurement. #107 remains paused, #108 unselected, and #260 inactive.
