# C03-RANDOM-RUN-ELAB-002 corrective successor

Candidate `e15c4c1c2e6cfce76f7ca6372fc3c62e49d40ba7`, tree `962d235134282736f47653c8c22177b07d8443f1`, parent `b059af864122a6b09912ba0db8095f422f8991bf`.
Branch `work/fdsa-ch03-random-selection`; worktree clean.
Commit: `fix(selection): normalize finite run branch proofs (#174)`.
This is an uncompiled successor, with root as the sole compiler owner.

## Actual failure retained

The complete second focused check at the parent closed with actual recorder/native exit 1:
owned 39520, terminal tool chunk `26714d`, root complete closure `c662b4`.
Its full outer log is 12,839 bytes, SHA-256
`e76898a357e67981bf7ddadfb4b3169c85c21421d280ff953c3f6ae8fa11725e`.
Author full-log/closure read: `17773b`.
All 14 files of that failed attempt and all 32 pre-existing author records were
rehash-verified unchanged. The original first failure is retained as well.
C03-RANDOM-RUN-ELAB-002 continues the existing correction record; it starts no new review loop.

## Exact bounded change

Only `Applications/Resources/RandomSelectionRun.lean` changed, with 5 insertions
and 4 deletions. Its new SHA-256 is `23de5dcdde20559ebe581fef8d77679dbe07219b7d88825032aaeb872fad4718`
and its Git blob is `4af2a079ad55005657eeac2eaf4d3dd2a3a3ac11`.
Only the bodies of `run_cons` and private `run_support_bounds` changed:

- Name and use the equation supplied by the split to simplify the remaining ordinary match.
- Normalize child-length and source-cost hypotheses by `List.length_cons`; state
  the equivalent triangular product majorant as `tail.length * (tail.length + 1)`.
  Remove the predecessor equality that this normalized arithmetic no longer needs.
- Use direct `simp` for the terminal product inequality, as required by the actual linter diagnostic.

All 30 run-module declaration headers and all other 28 declaration blocks are
byte-identical. Every execution definition body, sampler, selected child,
source-call cost, trace, import and global option is unchanged. All six private
bound conclusions and their public corollaries retain their sharp constants,
including the triangular upper bound and same-execution `W <= T <= 9W + 2`.
The three other source files and all 20 example claims/bodies are unchanged.
The detailed case and statement assessment is in `precommit-assessment.json`.

## Full inventory and next check

The original scope remains 60 public names and exactly two authored private
helpers, `equal_lookup` and `run_support_bounds`, across four files. The fixed
whole-task base remains `2da5708478a1d943a9214b5b386ec2db16cd9eca`.
The unchanged `Statements60-candidate04.lean` is explicitly rebound to this
candidate in `candidate.json`; its SHA-256 remains
`be10e6e4ef44817ccae42f34d55c156d0b49378f0a24f98dfe961000adf22bd3`.
It contains all 60 distinct explicit-`@` public targets and has not been executed
by this author. No probability extension or obligation deletion was introduced.

Root's requested next focused command, through the qualified existing environment:

```text
lake build Applications.Resources.RandomSelectionRun Examples.RandomSelectionRun
```

Actual stage, staged whitespace check and local commit all exited 0 in tool
chunk `85fb72`. No Lean/Lake, type inspection, environment or cache operation
was performed by the author. This successor still needs actual compilation and
all applicable whole-candidate/type/audit/independent-review/acceptance gates.

## Hold

All source and own provenance are held pending root's next actual terminal or
explicit assignment. Never poll the closed historical session 39520.
