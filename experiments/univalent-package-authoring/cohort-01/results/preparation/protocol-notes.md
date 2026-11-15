# Protocol details for the coordinator

No author trial has run. The preparer is `/root/motion539_standards_round2`,
independent of the facade builder, and must not serve as either author. The
preparer has privately constructed both a baseline solution and a facade
solution to establish feasibility, not author-burden evidence.

Release only `task.md`, `TrialTask.lean` and `ExpectedInterface.lean` from this directory, after independent
review and a final freeze. Do not release feasibility proofs, private oracle,
preparer logs, this report or private solution imports to either author. Publish
all retained preparation evidence after the trial. Freeze task hashes together
with the actual final source candidate and reviewed protocol; this preparation
uses development revision 4473f02225d84cdb99694a284e1898157c2e790c.

Both authors expose the identical named declarations specified in `task.md`
and `ExpectedInterface.lean`, each parameterized by the original native
equivalence. The common oracle imports the submission and references those
names directly. Only the import path varies between the two private
feasibility replays. Inspect proof dependencies as well as compiling: each
answer must connect to native transport APIs and retain the exact supplied E,
not merely prove independent target facts. The named equalities enforce that
connection; final source review remains necessary.

The variation changes the dependent field; it does not require repeated
transport. That satisfies the issue's explicit disjunction. The source and
target packages keep both proofs, and the negative case retains the operational
fields while changing the invariant. Keep those distinctions in the final
scope report; do not describe this as unrestricted dependent data or higher
structure identity.

Generic baseline APIs must remain available to the direct arm. Public facade
calibration itself imports the facade, so exposure instructions should distinguish
common baseline calibration from facade-only calibration. Otherwise the rule
that only the facade arm receives the interface conflicts with an instruction
to give both arms all calibration source. Give both the same baseline examples;
give facade documentation and facade-only examples only to that arm and record
that difference as part of interface exposure.

Use the same independent project-output cache policy in both author workspaces.
Preparation copied the worker's build output with reflink-capable copy and shared
pinned dependency artifacts through a symlink. This is a warm-cache feasibility
check, not a fresh full-project acceptance run. All Lean calls use the required
shared flock, CPU 0, nice 10 and root direnv shell. Final integrated check/audit
and independent reviews remain coordinator-owned.

Proposed replacement for the report's calibration-exposure sentences:

> Both arms receive the same mathematical calibration statements and accepted
> baseline generic examples. The facade arm additionally receives the proposed
> facade documentation, implementation and facade-only calibration. The direct
> arm does not read or import those facade materials. Record these exposure
> bundles by path and hash before author release; the direct arm retains all
> accepted generic baseline APIs and may write helpers.

The coordinator agreed to this clarification before author release. It changes
exposure wording, not the mathematical task or acceptance obligations.
