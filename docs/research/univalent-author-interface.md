# Bounded univalent package interface

Issue [#534](https://github.com/VladimirMarko/conaled/issues/534) tests whether
an author-facing interface reduces repeated admission and transport plumbing
without discarding the native construction. The interface and public calibration
are implemented here. The independent task, acceptance oracle and author trial
are not yet completed. No usability conclusion follows from the calibration.

## Admission and retained mathematics

`Examples.CubicalAuthorTransport.Change S T` contains a map between the decoders
of the existing `constantLocal terminal S` and `constantLocal terminal T` codes,
and the supplied `HomotopyEquivalence` of that map. This admits the discrete
carrier fragment of [#530](cubical-structure-identity.md). A model builder can
supply any genuine native equivalence in that fragment. `ofEquiv` is the
convenience constructor for a host equivalence; arbitrary supplied witnesses
are not replaced with its isomorphism construction.

The carrier code, smallness, decoder isomorphism, filling and lawful-filling
requirements are provided by the existing constant-code construction. They have
not disappeared from the mathematical assumptions. Extending admission to
other native families would require a new contract; this interface does not
assume that arbitrary native paths are discrete.

A caller supplies a `StatePackage`, which retains a selected state, transition,
dependent invariant, initial-validity witness and preservation witness.
`transport` decodes the result of actual selected package filling along the
exact `uaCode` of the supplied map and equivalence. `nativeSection` exposes that
complete native result; `universePath` exposes the actual ua path. The selected
witness remains accessible as `equivalence`.

`packageIdentity` provides #530's fixed-equivalence correspondence between a
whole native package path and the explicit preservation record. `path` consumes
that preservation evidence. `path_recovery` recovers every native path in this
specified family, and `native_recovery` recovers the complete filled section.
The proof fields use the existing discrete `PLift` proposition fragment. These
results do not classify all carrier paths or erase arbitrary higher witnesses.

## Composition and reversal

`trans` uses the existing generic contraction-of-composite-fibers theorem on
the actual composed map. It retains the resulting native witness rather than
converting the composed map into a host equivalence and rebuilding a witness.
`transport_trans` compares the decoded complete packages with successive
transport. Its equality is not an equality of independently selected universe
paths or native sections. The underlying public native composition comparisons
from [#528](compositional-univalence.md) remain available to both trial arms.

`reverse` uses [#554](selected-native-inverses.md)'s selected center map and its
proved inverse-equivalence construction. `carrier_reverse` identifies its
discrete carrier observation with the inverse carrier equivalence;
`transport_roundtrip` recovers the entire decoded package. This is a concrete
consumer of the new general inverse construction, not an isomorphism-only
replacement for it.

## Public calibration and statement review

`Examples.CubicalAuthorTransportCalibration` exercises the already public
three-state machine and its `Phase` presentation. Its first transition is
observed as ready, the invariant admits ready and excludes failed, and the
whole native section is recovered through the facade. The wrong presentation
fixes the initial state but sends its transition to failed; the facade's native
package path is rejected using the existing independent preservation failure.

A repeated integer-successor transport gives initial state 2, takes state 4
to 6, admits 2 and excludes 3 under the transported invariant. The repeated
transport theorem is used alongside an explicit independently calculated
package observation. A reverse machine transport recovers its full original
package. All these examples are public calibration and must be excluded from
fresh author-task evidence.

Statement review checked that admission retains the exact supplied native map
and contraction, composition uses the actual composed map, and reversal uses
the original fiber center. Recovery statements retain full sections or full
packages as named; decoded equality is not claimed to imply equality of native
universe paths. The positive and rejecting calibration cases instantiate the
same public facade. The scope is the admitted discrete proof-bearing package,
not unrestricted structure identity, executable evaluation or source conversion.

## Independent trial requirements

Freeze the interface and its source/dependency/compiler identity before trial
execution. An independent task preparer must supply a new dependent-package
argument and a variation involving repeated transport or a changed dependent
field, together with a checked oracle that retains native witnesses and
independent observations. That preparer and the interface builder cannot author
either submission. Fresh authors must receive the same mathematical task,
calibration and accepted baseline APIs; only the facade arm receives this
proposed convenience interface.

The frozen protocol must also specify permitted assistance and helper work,
source access, attempt retention, defect handling and measurement. A correctness
defect stops the affected cohort. Repairs start a separately identified cohort;
they do not overwrite failures. Preserve unsuccessful submissions and assisted
attempts with their actual scope. Record available token telemetry and missing
telemetry honestly. Laptop wall duration is a sanity check with host conditions,
not a performance ranking. Report builder effort, caller effort, proof reuse,
correctness and semantic coverage separately.

Independent Standards and Spec review of the interface and protocol precedes
fresh author execution. Submission replay and review of the eventual conclusion
are separate completion requirements. The current checked calibration does not
satisfy those requirements or justify a broader frontend adoption.
