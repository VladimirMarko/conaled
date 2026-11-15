# Journal transport task preparation

Preparation is independent of the facade builder. The preparer is agent
`/root/motion539_standards_round2`; neither the builder nor this preparer may
serve as a fresh author. No author trial or usability measurement was run.
This evidence is private until final trial publication, except the separate
`public/` bundle, which still requires coordinator freeze and independent review.

## Mathematical novelty and contract

The new carrier is a pair of finite natural-number journals, with arbitrary
entries and lengths. The source transition appends entry 1 to both journals.
Reversing each list changes the transition to prepend. This is an unbounded
history-dependent construction; it is neither a renamed finite state machine
nor integer-successor/parity transport. The independent targets define their
operations and predicates directly, without calling conjugation or transport.

The main invariant is equality of lengths. The variation changes the dependent
field to equality of totals while keeping operations fixed. `([2,3],[5])`
separates the two predicates in one direction; `([2],[3])` separates them in
the other. The transition at the first pair distinguishes prepend from append.
The negative target preserves the correct operational fields but replaces the
invariant with True. The rejected native path therefore tests dependent-field
preservation rather than merely an initial-state or transition mismatch.

Both constructions retain initial validity and step preservation. Initial
inputs exist (empty journals), and the original native-equivalence parameter
has an explicit admitted instance in the private oracle. Thus the task is not
vacuous. The scope is #530's discrete proof-bearing state-package fragment,
not arbitrary higher dependent data or source conversion.

The common API is a set of named declarations in `JournalTrial.Author`, each
parameterized by the original `E : HomotopyEquivalence nativeMap`. Native path
types use exactly `admittedLine nativeMap E`, hence the actual uaCode containing
that E. The task permits no substitution of a freshly reconstructed ofIso
witness. The private forward carrier calculation observes the specified map;
it does not replace the contraction record in the universe path or filler.

The public `ExpectedInterface.lean` checks the same declaration names and types
for both arms. The private oracle checks complete decoded packages, universal
initial/step/invariant observations, separating concrete pairs, source
endpoint decoding, both native path endpoints, final decoding of each submitted
section, entire native section recovery, native path recovery and rejection.
The two replay copies differ only in their first import. Native body equalities
are not inferred from a few host observations. The private feasibility proof
connects each construction through accepted native APIs.

## Preflight corrections retained before freeze

`feasibility-01.log` records an overly transformed sum-preservation proof, an
invalid field name `section`, and a timeout in the initial acceptance-record
experiment. The proof was corrected without changing the expected invariant;
`section` was replaced by a legal name.

Attempts 02 through 04 explored that extra record containing native paths.
Increasing heartbeats, changing transparency and spelling carrier parameters
explicitly did not make the record elaborate. The increased limit was a failed
diagnostic experiment; the final source uses the default heartbeat limit.
Archived sources are retained in `attempt-02`, `attempt-03`, `staged-04` and
`staged-05`. The common interface now uses named declarations instead of
introducing an additional dependent record. Mathematical targets, native
contracts and rejection conditions were not weakened.

Attempt 05 established native feasibility at the default heartbeat limit, then
exposed facade path-boundary inference timeouts. Attempt 06 retained those
failures after making endpoint arguments explicit. Attempt 07 established the
facade path definitions with explicit simplification at the type boundary,
while its path-recovery applications still timed out. Attempt 08 checks a
locally typed path at that recovery boundary. These are preparer diagnostics,
not author attempts or evidence that either arm is easier.

No worker534 source was edited. The private checkout starts at
`4473f02225d84cdb99694a284e1898157c2e790c`, with its own copied project outputs.
Pinned external dependency outputs are shared through a symlink. All Lean
commands are serialized with `/tmp/conaled-wave-20261115/build.lock`, pinned to
CPU 0 at nice 10, and run through `direnv exec /home/vlad/Code/conaled`.
The check wrapper and raw logs are retained. This is warm-cache focused
feasibility; final integrated candidate validation and review remain separate.

## Exposure and review

Release only the files under `public/` to the authors after review and freeze.
They contain task data, target definitions and an interface checker, but no
transport solution. Keep the entire checkout, private oracle, feasibility
solutions, attempt archives and protocol notes excluded from both author
workspaces. Future authors must use empty-history sessions and must not have
served as preparer, builder or reviewers with access to solutions.

`protocol-notes.md` provides a precise replacement for calibration exposure:
both arms receive the same mathematical calibration and accepted baseline
examples; only the facade arm also receives the proposed facade and its
facade-only calibration. All accepted generic baseline APIs and self-written
helpers remain permitted in both arms. The coordinator agreed to this
clarification before release. No broad usability or portability conclusion is
supported by preparation.

The explicit boundary conversions are recorded as preparer/interface-integration
effort. They must not be charged to future author sessions or presented as
observed author burden. `feasibility-08.log` also records two oracle-only
elaboration issues: concrete predicate decisions required unfolding the fixed
target definitions, and the admitted witness needed its Presheaf namespace
opened. Attempt 09 repairs those elaboration issues without changing any
expected result. Error-recovery `sorry` diagnostics in failed compiler output
are not admitted source proofs; no successful source uses placeholders.

Attempt 09 passed the private native oracle. Its facade check still timed out
when applying `Change.path_recovery` directly to a path exposed with the common
baseline `NativePath` type, including after introducing a locally typed path.
Attempt 10 retains facade path construction, section transport/recovery and
complete decoded transport, but uses the accepted baseline
`uaStructureIdentity(...).symm_apply_apply` for the exact native-path recovery
identity. This is permitted baseline reuse in the facade arm. It establishes
no mathematical correctness defect in the facade and is not an author-trial
outcome. The precise preparation limitation is automatic elaboration across
that facade-to-baseline recovery boundary, not the existence of the recovery
law or feasibility of the required native contract.

The separating journal pairs lie outside the selected initial orbit. This is
intentional: identical behavior on reachable empty-start traces would not
validate equality of the complete invariant field at all states. The private
oracle checks the universal records and these independent field observations.

## Successful focused validation

`check-private.sh` exited 0 for `feasibility-10.log`. It compiled the common
fixture, independent mathematical lemmas, native feasibility solution, native
oracle, facade feasibility solution and facade oracle. The oracle bodies are
byte-identical after their first import line. Both are checked at the default
heartbeat limit. Each solution is polymorphic in the supplied E; each oracle
also instantiates a genuine admitted E to show that the input contract is
inhabited.

The logged transitive axiom queries for native paths, section recovery, complete
decoded targets, rejection and oracle conclusions contain only `propext`,
`Classical.choice` and `Quot.sound`. These are focused named-declaration checks,
not the repository's exhaustive integrated audit. The public interface checker
is replayed separately against both feasibility modules. Final integrated
candidate acceptance and independent Standards/Spec review remain required
before author release.

`source-manifest.json` records the exact development commit/tree, relevant
baseline and facade source hashes, public bundle and private proof/oracle
hashes, dependency manifest, actual dependency revisions and command wrapper.
The coordinator must associate the reviewed bundle with the final freeze
candidate; this preparation record does not itself freeze or approve a trial.

The first public-interface replay failed because its anonymous data declarations
were implicitly computable while the specified native objects are noncomputable.
`interface-attempt-01/` retains that checker. The final checker explicitly opens
a noncomputable section, matching the task's mathematical contract; no expected
type or equation changed. `interface-check-02.log` records the corrected replay.
