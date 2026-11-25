# Same Spec axis — eligibility of the existing fresh verification route

Recorded: 2026-11-25T06:06:28.073171+00:00. This is a bounded authority clarification by the existing `/root/requirements_review147/spec147` successor of `/root/parser_review/spec`. It does not change the source assessment, any released report, original finding IDs, historical reading limits or acceptance state.

## Conclusion

**The supported native `./check.sh --fresh --candidate a5a917db8717977371b8d76d93f166389c9eec9b` route is eligible under the unchanged requirements, with the checker's original defaults and no caller resource/compiler override.** This conclusion permits a documented verification mode; it is not evidence that this candidate or any whole run passed. SP-V001 remains open.

This interpretation rests on the requirements' express referral to repository development instructions, the documented candidate/fresh modes, and the unchanged original checker. It does not create an exception to the prohibitions on added CPU/thread/memory/time caps, compiler overrides, artifact injection or reduced mathematical claims.

## Authority and precise resource boundary

Requirements lines 28–30 retain the repository's development instructions and separately identified pinned native adapter. The cumulative restrictions at 1203–1208, 1489–1496, 3338–3344, 5517–5519, 10821–10826, 10838–10842, 14106 and 17279–17284 preserve the exact-candidate whole/audit/verification/comparison/review obligations and prohibit introducing resource caps or compiler-setting overrides. No literal `--fresh` or `--jobs` flag spelling appears in the requirements. The ordinary word “fresh” does appear in other contexts; absence of the flags alone is not authorization.

Review-loop lines 87–95 explicitly accommodate fresh verification through the candidate wrapper and retain direct `check.sh` as an alternative in a stable isolated checkout. Development lines 84–90 and 122–135 document selecting the build mode, recording it, and later verifying that recorded mode. Lines 170–195 describe the independent fresh route. START_HERE154 line 78 names the direct candidate route without restricting it to default mode. The development table's ordinary incremental route remains the normal proof-edit route; using the existing whole-source reference mode does not narrow its required source or audit coverage.

Crucially, the complete 16,215-byte `scripts/check.py` is byte-identical in original B `bc95f503ccbf043136c6699992388f750270e8e6`, incorporated M `ec4949a94ed70084d70f5b273fb0cc6dca8b2647`, C154 and C155. Its SHA256 is `4c95900fb68b4efe792d143f2847472291ba5a3f13fc477a7815808be2186694`. The original code already sets `args.jobs = args.jobs or min(4, os.cpu_count() or 1)` at line 177 and uses that value for the scheduler at lines 26–65.

Thus the eligible invocation retains the original built-in maximum of up to four concurrent compiler processes. **It must not be called unbounded or unlimited.** It adds no caller `--jobs` value, changes no compiler setting and imposes no new CPU/memory/time or per-Lean-thread limit. The generic documentation's optional `--jobs N` and `LEAN` override facilities are not authorized for this task; the stricter cumulative restrictions remain controlling. The source inspection did not query the host CPU count or alter the scheduler.

The native adapter and runtime also match their secured154 counterparts byte-exactly. Their existing environment construction removes caller selectors and `LEAN_NUM_THREADS` and retains the authorized pinned tool dispatch. This clarification does not authorize modifying that adapter, replacing its environment, supplying a caller `LEAN`/`LEAN_PATH` override, adding limits or changing pins. The fresh checker's own temporary-output import path is its existing documented implementation, not permission to inject project artifacts.

## What the supported mode does and does not establish

The unchanged checker retains clean candidate/dependency identity checks, compiler pin verification, source policy, import coverage and layout preflight. It rejects omitted integrated sources and computes the same local dependency graph. Fresh mode then creates an empty private temporary project-output directory, compiles every inventoried project module in dependency order, and runs the same `ProofAudit` against those outputs. A failed compilation prevents the dependent work and audit from being accepted; the ordinary exception path returns failure. The compiler subprocess calls add no timeout or resource-limit option.

Fresh mode uses the documented external dependency paths but does not reuse existing project outputs. It bypasses Lake's retained-output guard and build decisions because it compiles into its own empty output directory. That difference must remain explicit: fresh success would be reference-mode evidence, not a claim that the retained Lake artifact guard ran. The temporary outputs are removed; they do not populate Lake traces, incremental cache or an integrity record for copied artifacts. No failed whole155 outputs may be reused or injected into this route.

Only after actual successful compilation, audit and matching post-run candidate/dependency/compiler identity does the unchanged checker write a success record with mode `fresh`. The existing immediate nonrepairing verification is then:

```sh
./check.sh --verify-candidate a5a917db8717977371b8d76d93f166389c9eec9b
```

That command is to use the same supported native route and stable candidate. It omits `--fresh`, `--clean` and `--jobs`; `check.py` uses the recorded mode and rejects those verify-time flags. It does not compile, repair outputs or rerun the audit. Supported final comparison and the same original independent axes remain necessary. None of these are new gates created by this clarification.

## Current outcome boundary

Root's latest supplied observation, 2026-11-25 at 05:52:12 UTC, reports an internal `Examples.FiniteUniverseLoops` Lean exit 137 while whole155 still has no outer child-exit/final receipt. The cause remains unestablished. I did not read the active whole log and do not infer the outer result, OOM, timeout or any other cause. Root's stated sequence is to preserve the actual outer terminal before considering a new independently owned clean candidate workspace; this clarification does not start that work or authorize concurrent compiler ownership.

SP-D001/SP-D002/SP-C001 retain their existing dispositions. **SP-V001 remains OPEN** for actual whole/aggregate terminal evidence, exhaustive applicable source/module/product-origin/transitive-axiom audit, immediate nonrepairing verification, supported final comparison and same-loop reconciliation. All older UNKNOWN outcomes, null bindings, recovery limitations and nonfatal ellipsis limits remain unchanged. No current failure is accepted or erased. No compiler/checker, native command or verification was executed by this axis; no project source, configuration, products or released reports were modified.

## Exact evidence and reading ranges

Repository files below were read from immutable C155. `check.sh`, `scripts/check.py`, development and review-loop bytes were independently verified unchanged from M/C154; the entire checker was additionally verified unchanged from original B. Packet paths below are relative to the secured154 packet. This is a targeted authority reading, not a new full read of the cumulative requirements or a new audit of the entire native toolchain.

| Evidence | Bytes | SHA256 | Fresh reading |
|---|---:|---|---|
| `check.sh` | 74 | `d4a16262232c26dd48191217c1113cbbeda7dbc8ea0826505ca1bf767d0f8acd` | 1–4, complete |
| `scripts/check.py` | 16,215 | `4c95900fb68b4efe792d143f2847472291ba5a3f13fc477a7815808be2186694` | 1–329, complete |
| `docs/development.md` | 21,541 | `e21fd90793a89acc8837f8624adf0e01ac93efebc6e641c9f6277389398e18bf` | 76–96 and 113–202 |
| `docs/agents/review-loop.md` | 16,277 | `c369ed734ff8b61c2a2745fc3cd5839f496654e1625b1a4ceaa6a04abb2ba80f` | 75–101; prior full same-axis reading retained |
| `current/control/requirements.md` | 2,238,214 | `3e686f9f28a413c75dd98ccf4f9764badd613e623f08467fc760adae734728d0` | 24–34; 1198–1212; 1484–1500; 3336–3347; 5512–5522; 10815–10846; 14100–14110; 17277–17290 |
| `START_HERE.md` | 10,810 | `32fbd2ea753cd69a46f10eac154a16cc2b9915a998eb953a4b9ca5648fb1ab54` | 68–86 |
| `operations/native/native_profile.py` | 12,032 | `a3891ea20145d0cd9fed82c07b95276d79fe611eb141c27e8a9a600b62355ea4` | 179–235; static symbol search elsewhere |
| `operations/native/lib/runtime.py` | 6,267 | `cafe22ddc9a0de09a7dad5ef70fbd1c0b752217281cafed6bd71b7601d9413ad` | 1–147, complete |
| `operations/native/NOTICE.md` | 1,966 | `0622bfa90322c467122bcb2bd9b6f361a69dd9c9e274722fbce9ee699c321510` | 1–33, complete |
| `operations/native/PINS.json` | 10,133 | `854746c88e7ab68f1f81ff6749842b9549dea7d51591952d5987c68a81c668f6` | selected project_files/toolchain/lean_commit/lake_version/verification_scope fields only |

The four previously released preparation and installed-follow-up files were independently hash-checked unchanged. No additional semantic review axis or permission request is introduced. The same Spec handle yields its slot after this clarification.
