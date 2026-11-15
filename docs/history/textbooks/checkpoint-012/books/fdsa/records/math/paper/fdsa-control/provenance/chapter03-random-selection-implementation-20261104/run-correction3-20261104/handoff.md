# C03-RANDOM-RUN-ELAB-003 examples correction

Candidate `93ddb900a9ae01e721883c5b8a409eb37129a3f8`, tree `c27494e7b86079be43a9051c780231c09a3bd779`, parent `e15c4c1c2e6cfce76f7ca6372fc3c62e49d40ba7`.
Branch `work/fdsa-ch03-random-selection`; worktree clean.
Commit: `fix(selection): reduce finite random execution examples (#174)`.
This successor is uncompiled; root remains the sole compiler owner.

## Actual result and recovery state

The complete third focus at the parent closed with actual recorder/native exit 1:
owned 98660, terminal `6eb519`, root complete closure `c43370`.
Its full log records that the finite core built successfully in 15 seconds,
then the examples failed. The whole pair and Chapter 3 have not passed.
The complete 11,688-byte log (SHA-256
`7b59e0f21c41e05fc58935b786915bf0107e250415638599e816bd8bf329dd90`)
and closure were read in `1d80bd`.

Checkpoint0125 was verified, uploaded, exposed and posthash-checked before this
release. All three bound checkpoint0125 records, all 14 failed-attempt records,
and all 42 pre-existing author records remain unchanged.

## Exact bounded correction

Only `Examples/RandomSelectionRun.lean` changed: 4 insertions and 3 deletions.
New source SHA-256: `76504fe5fa77c581b8a7e3c9f3e0247c8a927adee8b308f84be6167e0ea20e0f`.
Git blob: `ca900f902acde3c091e67f90108c2adb03b321cb`.

- `invalid_singleton` and `two_key_execution` now apply the pinned library's
  actual `PMF.pure_map` equation before reducing `prepend`. The public PMF map
  of a pure continuation retains exactly the same output, trace and additive cost.
- `duplicate_execution` exhausts both occurrence indices with `fin_cases`.
  Both lookups yield `x`; costs remain 12 and 13 as required by `12 + i.val`.
  Unneeded generic arithmetic simp arguments are removed.

The exact passed finite core and both first-step files are byte-identical.
All 12 example headers and nine other example blocks are unchanged. Therefore
all 60 public and two authored private statement headers, every execution
definition, all imports/options, and all 20 expected example statements are
preserved. No value-uniform sampling, changed expected result, omitted index,
weaker cost/trace claim, or probability extension was introduced.
Detailed unchanged expectations and theorem connections are recorded in
`precommit-assessment.json`.

## Inventory and next check

The unchanged `Statements60-candidate04.lean` is rebound to this exact successor
by `candidate.json`, with SHA-256
`be10e6e4ef44817ccae42f34d55c156d0b49378f0a24f98dfe961000adf22bd3`.
Its 60 distinct explicit-`@` targets match the full public inventory. The two
private helpers remain `equal_lookup` and `run_support_bounds`. The fixed
whole-task base remains `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

Requested next root-only focus, through the qualified environment:

```text
lake build Applications.Resources.RandomSelectionRun Examples.RandomSelectionRun
```

Actual stage, staged whitespace check and local commit all exited 0 in `b2007d`.
Author source/header/inventory/evidence comparisons exited 0 in `c48a74`.
No compiler, type-program, environment or cache operation was performed here.
The successor still requires root's actual focus and all applicable complete
candidate/type/audit/independent-review/immediate-verification gates.

## Hold

Source and own provenance are held pending root's next actual terminal or
explicit assignment. The historical closed session 98660 must not be polled.
