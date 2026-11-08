# #358 dispatch setup review

Final outcome: **Passed**. Shared smoke completion and final handoff checks are recorded below. No source, closure, hash, instruction or budget findings. This is a bounded setup review; the mathematical freeze and runner implementation reviews remain unchanged.

Reviewed preparation/freeze receipts and public-verification.json under trial358/setup, both handoff manifests, RUNNING.md, native smoke archives and runner timing receipts. Independently recomputed every manifest-listed file hash, every prepared project-artifact hash, each preparation-record hash and each final manifest hash. Compared every exported local module with immutable candidate `2838b20125fc4253f55eb1feb45f069f604175df`. All comparisons passed. Native has 18 public files and 6 modules; shared has 21 files and 9 modules. The added shared modules are Local, Selector and Lowering.

Native manifest SHA-256: `08faf6b4cac1ce522fa7f81198f5f6e0c418f1fa9d56d0466ec9ea99718add65`.
Shared manifest SHA-256: `de11f396b5fee2be8a264cde2e2c0cdb6856dcb6b7571156f2e44b7bea76eafd`.

Protocol, task, oracle, checker, reviewed runner and RUNNING.md are byte-identical across arms. The arm-specific access notes match the respective frozen closures. Prepared application solutions and research reports are absent from those closures. The donor/candidate is the approved freeze SHA, with pinned copied dependencies and private project artifacts. Both handoffs have fresh empty Git repositories, not exported project history: git log reports unborn branches. Root confirms these were created by the existing environment_index.py utility for Nix flake filtering, with staged public files and no remotes/commits.

RUNNING.md routes checks through the reviewed runner and preserves the unchanged attempt wrapper. Its timing instructions include reading, editing, checking and reporting, subtract only recorded lock waits/external suspension, and retain per-stage protocol caps. A/B/C/repair remain 20/20/35/15 active minutes and 15/15/25/10 attempts. Memory limits are described as Linux child high-water RSS, not aggregate concurrent memory. The common lock and invocation are identical for both arms.

Native real-runner smoke receipts show finished success (exit 0, lean-passed) and intentional failure (exit 1, lean-failed). Both wrapper records verify public inputs before and after and name the approved native manifest. Their timing intervals enclose the corresponding checker intervals. Setup attempts were moved to external evidence: native has no attempt sources. Shared had only RunnerTrue.lean while its smoke was running; no author has been allocated or exposed according to the coordinator.

The initially pending shared-smoke gate is now resolved by the final inspection below. Fresh fork-none authors must separately confirm no fixture/task/solution exposure and record available configuration; author eligibility is still a coordinator dispatch obligation.


Final inspection after both shared commands completed: native and shared real-runner summaries each contain RunnerTrue/lean-passed/exit 0 and RunnerFalse/lean-failed/exit 1. Every wrapper receipt verifies public inputs before and after, names its approved manifest hash, and agrees with the finished timing receipt exit status. Runner wall/check intervals enclose wrapper execution. Both existing utility smoke summaries independently show success exit 0 and deliberate failure exit 1. Recomputed every listed public-file hash in both handoffs; all still match. Both attempts directories are completely empty after setup evidence export.

The setup gate passes with zero findings. This approves dispatch using these frozen handoffs after the coordinator allocates eligible fresh fork-none authors, excludes fixture/review agents and records actual configuration or unavailable metadata. Eligibility remains a dispatch check rather than an existing author-result claim. No trial results or issue completion are approved.
