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

## Trial protocol draft before independent task preparation

This protocol is not released to authors. Freeze remains incomplete until an
independent preparer has produced and checked the task and oracle, and both
review axes have accepted the complete protocol and interface candidate.

The interface-builder role belongs to the coordinating root agent. The task
preparer and the two fresh author roles must be different agents, with neither
author inheriting the builder's or preparer's conversation. The author
assignments use empty-history forks. Reusing a reviewer as the independent task
preparer is permissible only if that reviewer did not implement this facade or
attempt the selected task. Reviewers and task preparers cannot subsequently
serve as fresh authors for that cohort.

The preparer chooses a new task within the documented discrete proof-bearing
package fragment and records why it differs mathematically from the public
Boolean, integer, Fin3/Phase and constructor examples. Merely renaming their
states is insufficient. The task must have an independent target construction,
a meaningful dependent invariant, a complete native package path over the
specified exact equivalence, and observations that would fail for a wrong
presentation. Its variation must require repeated transport or a changed
dependent field. The private oracle must check native path endpoints and
recovery, complete decoded packages, independent observations, and the rejecting
case. The preparer proves its own feasibility solution privately before freeze;
that solution is excluded from both author environments.

Both arms receive identical task statements, expected declaration interfaces,
public calibration links and validation commands. The direct arm may use all
generic APIs accepted at the chosen baseline, including #528, #530, #533 and
#554. The facade arm additionally may import the proposed facade. Both may
write generic helpers, with their effort and retained helper code recorded.
No baseline API is withheld to manufacture a facade advantage. Source access
is limited by instruction to the frozen repository and the arm's own task
bundle; private oracle, other submission and orchestration scratch directories
are excluded. This is a cooperative experiment, not a security sandbox.

The preparer assigns a common acceptance interface to both submissions so the
same oracle can replay them unchanged except for the submission module import.
It records source-level goal coverage separately from whether an author's proof
actually uses the native transport APIs. A proof of an unrelated expected
answer does not satisfy the native-witness requirement. Authors must not replace
a requested original equivalence by a newly reconstructed `ofIso` witness.

Before release, the coordinator records the full candidate commit, facade and
baseline source hashes, task and oracle hashes, dependency manifest and checked
revisions, Lean toolchain, commands, model metadata actually supplied by the
agent environment, and start conditions. Unavailable metadata is marked
unavailable. The same single-CPU serialized build wrapper is used for both arms;
shared pinned dependency artifacts are permitted, with separate project build
outputs and submissions. Cache state and host interruptions are recorded rather
than silently interpreted as author performance.

An initial attempt ends when the author reports a complete submission or a
specific mathematical/interface blocker. Elaboration fixes, ordinary library
search and self-written helpers remain part of that attempt. The coordinator
may relay clarifications from the independent preparer; every such exchange is
recorded and provided to both arms when applicable. New proof hints or repairs
from other agents start a separately labeled assisted attempt after preserving
the initial submission. Missing metadata or slow host execution does not turn
a mathematically incomplete submission into a passing one.

There is no inherited 24,000-token ceiling. Record actual per-attempt usage when
available, distinguishing builder, preparer, reviewer and author activity.
Check wall duration at hourly intervals solely to detect stalled tooling or
host suspension; continue substantive work when those explain elapsed time.
Neither wall duration nor token count alone determines the keep/refine/reject
recommendation. Record author-reported blockers, required helpers, unsuccessful
proof attempts, assistance and model-builder repairs alongside verified scope.

A correctness defect in the frozen facade or oracle stops the affected cohort.
Preserve its evidence, fix and review the defect, then identify a new cohort
with new hashes. Task changes are never retroactively applied to make an
original submission pass. A shared infrastructure outage pauses execution and
is reported separately; changing mathematical source or acceptance goals is
not an infrastructure repair.

Replay each frozen submission against the common private oracle in its isolated
checkout, then run the repository's applicable integrated candidate build and
exhaustive audit. Independent final review checks the submitted proofs, native
witnesses, observations, role separation, preserved failures and conclusion.
Publish the task, feasibility solution, oracle, submissions and attempt record
with the final research report so the evidence can be inspected. A successful
bounded trial supports only its tested fragment and author conditions.
