# #534 independent Spec review of the pre-release checkpoint

Spec outcome: **Passed for the interface/protocol checkpoint**. Zero findings. This outcome does not complete #534, establish author usability, or supply a keep/refine/reject conclusion. Fresh-author execution, retained submissions, replay, integrated artifact audit and independent final assessment remain required.

Base and merge base: `2c540b64e5b0f93bd63aee0321cbbdfdb531be89`.
Candidate: `a5c17c25e9753f5dcb1d3be2119a8d4bd747ef24`.
Diff: `git diff 2c540b64e5b0f93bd63aee0321cbbdfdb531be89...a5c17c25e9753f5dcb1d3be2119a8d4bd747ef24`.

All nine paths in `scope.json` and `integration-candidate-01.json` were reviewed without exclusions. The receipt has status `ok`; the isolated checkout is clean. The three task commits are `3a460d54`, `9062580a`, and `a5c17c25`. Requirements are the complete supplied `requirements-current.json`, including the owner clarification that #530 is satisfied, with `requirements-full.json` retained as the earlier issue version. The caller explicitly limited current acceptance to the pre-release checkpoint.

This reviewer did not implement the candidate, read the other review, edit source, or rerun Lean builds. The review used the code-review and EDD statement-review guidance, architectural/language direction, the #528/#530 contracts, and #429's trial controls. The reviewer inspected the private task preparation, both feasibility solutions, common oracle, interface replays and failed-attempt evidence. Having seen those solutions, this reviewer is ineligible as a fresh author.

## Interface and mathematical statements

`Change S T` preserves the supplied map and `HomotopyEquivalence` record for the documented constant-code discrete fragment. The optional `ofEquiv` constructor is separate from admission of arbitrary supplied witnesses. `line`, `universePath`, `nativeSection`, `transport`, and `packageIdentity` use the original map and equivalence through the accepted native APIs. The implementation does not replace an arbitrary supplied equivalence with an `ofIso` witness.

The admission documentation identifies the underlying carrier code, smallness, decoder isomorphism, filling and lawful-filling requirements. `StatePackage` retains selected state, transition, invariant and both dependent proof fields. Its native proof fields are the accepted discrete PLift proposition fragment. The claims do not extend to arbitrary higher dependent data or unrestricted structure identity.

`native_recovery` concerns the full filled section. `path_recovery` concerns the full native package path under the fixed-equivalence correspondence. `transport_eq` and `transport_of_preserves` concern decoded complete records. Inspection of the unchanged `CubicalStructuredState` definitions confirms that the native family and selected filling are retained and that the recovery laws use the admitted discrete presentation, rather than host proof irrelevance for arbitrary paths.

Composition uses the actual composite map and generic composite-fiber contraction. Reversal uses the original selected inverse and its proved native equivalence. `transport_trans` and `transport_roundtrip` prove decoded package equalities; they do not assert equality of independently selected universe paths or sections. The report preserves that distinction and keeps #528's native composition comparisons available to both author arms. Existing direct native clients are unchanged.

Calibration connects the facade to complete native section recovery, independent finite-state observations, a wrong-presentation rejection, repeated integer transport and reverse transport. These cases are labeled public calibration throughout and are excluded from fresh-task evidence. The admitted inputs are inhabited and the rejection exercises a real preservation failure.

## Independent task, oracle and feasibility

The paired-journal task is a new argument over arbitrary finite Nat lists. Reversal conjugates append-one into prepend-one. Its directly specified targets do not call transport or conjugation. The main invariant is equal lengths; the variation changes the dependent field to equal totals. The two journal pairs separate the predicates in both directions, and the nonempty transition observation distinguishes prepend from append. These states lie outside the initial orbit intentionally: a reachable-trace-only test would not establish the complete invariant field.

`NativePath E p q` fixes the original arbitrary `E`, its actual admitted line and presentation, and complete endpoints. The common named declaration interface requires both paths, actual selected filled sections, section recovery, complete decoded packages, exact connections to the native transport results, and path recovery. It permits generic helpers equally in both arms. The variation satisfies the issue's explicit alternative of a changed dependent field; no repeated-transport trial result is inferred from it.

The private oracle checks full record equalities, universal initial/transition/invariant observations, the separating states, both path endpoints, both section decodings and recoveries, and native path recovery. Its explicit admitted witness rules out an empty equivalence premise. The negative target preserves initial state and transition but changes the invariant to True. The private rejection proof extracts invariant preservation and contradicts it at journals `([0],[])`; this establishes absence of the native package path, rather than treating failed elaboration as rejection.

Both private solutions use native transport APIs and remain polymorphic in E. The facade solution uses facade paths, native sections and decoded transport. Its path-recovery proof falls back to baseline `uaStructureIdentity(...).symm_apply_apply`, which both arms are permitted to use. The recorded timeout of direct `Change.path_recovery` applications at the common baseline-typed boundary is a real preparation limitation. It is retained in the report, logs and archive and is not presented as fresh-author burden, mathematical incorrectness, or evidence of a facade advantage. A future author who encounters this boundary must have their actual effort and any assistance recorded under the protocol.

The two private oracle bodies are byte-identical after the first import line. The public declaration checker's two private replays likewise differ from the public checker only in that import. The incomplete future author workspace is not incorrectly counted as compiling before `AuthorSubmission` exists.

## Freeze, fairness and evidence retention

The manifest pins the accepted baseline, facade bytes, public task, private oracle/solutions, protocol, toolchain and dependency files. This review recomputed all listed source, protocol, public, calibration and private-artifact hashes, the archive hash and every listed archived file hash, with no mismatches. Replay-file, command and successful-log hashes also match. The external candidate receipt binds the manifest itself and avoids a circular containing-commit hash.

Both arms receive identical public task files, baseline calibration and validation instructions. Every accepted generic baseline API remains allowed in the direct arm, including native composition and structured-package laws. Facade implementation/docstrings/calibration are the declared extra exposure for the facade arm. Excluding aggregate `SquareApplications` from the direct arm prevents accidental facade import while preserving specific baseline imports. Private solutions, oracle, preparation material and the other submission are withheld from both authors. The report accurately describes cooperative access instructions rather than an operating-system security boundary.

Builder, independent preparer, protocol integrator and solution-exposed reviewers are excluded from fresh-author roles. Empty-history sessions, separate project outputs, equal warm-cache policy and the serialized pinned command wrapper are specified. Exact author identities, available model metadata, start conditions and the final reviewed candidate are release-record obligations; they are not fabricated as completed observations.

The protocol retains unsuccessful submissions and compiler logs before editing, permits ordinary search and self-authored helpers, shares clarifications, and separates later proof assistance into a labeled assisted attempt. Correctness defects stop the affected cohort and require separately identified repair/review. Mathematical task changes cannot retroactively turn a failure into a pass. Preparation repairs and the integrator's setup/hash-convention failures remain available separately from future author work.

Measurement rules separate author burden, model-builder work, preparation, repairs, proof reuse and semantic coverage. They record available tokens and missing telemetry without an inherited hard ceiling, account for host interruptions and queue waits, and prohibit ranking by wall duration alone. Hourly checks are sanity checks. Completion/blocker stopping rules preserve partial evidence. Final publication and independent assessment must retain these distinctions and the known fallback.

## Validation and remaining release work

`integration-check-01.log` records successful compilation, clean integrity and PASS for all 3,421 modules with the exhaustive axiom union `propext`, `Classical.choice`, and `Quot.sound`. The inspected `.lake/verification.json` records this exact candidate, Lean 4.35.0, incremental mode and completion at `2026-11-15T12:15:33.810808+00:00`.

`integration-replay-02.log` and its checked identity record establish successful replay of the unchanged private fixture, mathematics, native/facade solutions, oracle and public interface checks against the integrated output at default heartbeat limits. Named axiom checks retain only the three permitted axioms. These focused private checks are separate from the integrated exhaustive audit. The first replay's missing external-directory toolchain file and the earlier normalized-versus-raw digest assertion are retained setup failures; neither altered Lean source or mathematical observations.

Before author exposure, the coordinator still must obtain the other independent passing axis and attach both reviews, exact candidate/manifest, current verification and actual session metadata to the release record. Immediate candidate verification remains coordinator-owned. Those are the documented release steps, not unresolved source findings. Later trial results and a keep/refine/reject recommendation remain outstanding #534 acceptance work.

Final disposition: **Spec Passed for the pre-release interface/protocol checkpoint**, zero findings, worst issue none. Candidate `a5c17c25e9753f5dcb1d3be2119a8d4bd747ef24`; base `2c540b64e5b0f93bd63aee0321cbbdfdb531be89`. No usability or full-issue completion conclusion is authorized by this review.
