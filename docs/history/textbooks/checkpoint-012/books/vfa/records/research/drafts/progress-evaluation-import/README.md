# Local #1022: complete Evaluation import check

**Passed on the single authorized invocation**, 2026-11-02: exit 0, no timeout,
and no diagnostics. Baseline candidate is
`bed44c16cee3e1eff6a4175bad9a7ed50651b927`. This is focused evidence for the
Evaluation header change, not downstream validation or candidate/chapter
acceptance. No main/candidate source, setup, cache, configuration, or primary
process was changed.

## Exact change and setup

The complete staged `Applications/Progress/Evaluation.lean` has this header:

```lean
import Applications.Optimization.Relations
import Lean.Elab.Tactic.Omega
```

Only the original `import Mathlib.Tactic` line was replaced. Every other byte,
including all definitions, statements, proofs, comments, and namespace commands,
is preserved. Reversing that one replacement reproduces the original file.

The staged setup is byte-identical to Evaluation's actual completed candidate
setup, with all **3,125 artifact mappings**, module name
`Applications.Progress.Evaluation`, package `compilingWithSquares`,
`isModule: false`, empty options/plugins/dynlibs, and **no imports override**.
No mapping was added, removed, or changed. Optimization.Relations uses its
existing completed candidate `.olean`; Omega has no package mapping and resolves
through the pinned compiler distribution normally.

Thirty-four protected file identities were checked before launch and after
completion. These include original main/candidate source, candidate setup/trace,
the mapped relation artifact, twelve Omega/Frontend distribution artifacts,
both checkouts' environment/dependency configuration, direct dependency sources,
completed candidate outputs, and the prior Finite correction's manifest. None
changed. Both checkout HEADs also remained at the baseline. Full identities are
in `inputs.json` and `postcheck-evidence.json`.

## Reproduced invocation and observed result

The retained harness consists of `prepare.py`, `run-check.py`, and `postcheck.py`,
adapted in this new directory without changing the previous Finite evidence.
Only `run-check.py` invokes Lean, and it refuses a second launch after its
exclusive `STARTED.json` marker exists. No retry or additional compiler ran.

Evaluation's own completed trace supplied its exact executable, `LEAN_PATH`, and
argument vector. Original `-o`, `-i`, `-c`, `--setup`, and `--json` flags were
preserved, redirecting only the source/setup/output paths into this directory.
The trace and original command are retained in `Evaluation.original.trace.json`
and `original-command.txt`. `STARTED.json` and `result.json` contain the complete
executed argument vector, working directory, and environment additions.

The runner used the main checkout's pinned Nix shell, the original executable
`/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, the original candidate
`LEAN_PATH`, and `LEAN_NUM_THREADS=1`. The command was bounded by
`timeout --signal=TERM --kill-after=5s 180s nix develop --command ...`, covering the
whole Nix/Lean invocation. Its separate process session scoped any timeout to
this check; no timeout occurred. No build or cache fetch was invoked.

| Observation | Result |
| --- | --- |
| Start / finish UTC | 2026-11-02 07:01:44.029240 / 07:03:47.755442 |
| Elapsed / exit | 123.724885 seconds / 0 |
| Timeout | No |
| Diagnostics | Empty, zero bytes |
| Emitted module | `Applications.Progress.Evaluation` |
| Emitted direct imports, in order | `Applications.Optimization.Relations`; `Lean.Elab.Tactic.Omega` |
| Protected identities changed | None of 34 |
| Main/candidate HEADs changed | Neither |

The `.ilean` header lists exactly those two imports, with all per-import flags
false. C initializer declarations also name those two modules and Init.
`postcheck-evidence.json` preserves the exact metadata and generated artifact
identities. The three generated outputs were removed after extraction and
hashing; the staging `out/` directory is absent. Nothing was installed in a
project cache.

## Exact identities and acceptance boundary

| File | Bytes | SHA256 |
| --- | ---: | --- |
| Original Evaluation source | 5871 | `8882235188cd0e293f3433d220b677f160b539f4829f899ed2a911c655ca059f` |
| Staged Evaluation source | 5879 | `3be90be15e37dd6f0fc12ef43e60ea2d4a1caf85b6de7471c4aeeb0a7696233d` |
| Actual and staged setup | 2330064 | `146742d662b389d4c9721e06500e45e7bdc8a6fb039bd03af19298ef7986bdc3` |
| Result | 2735 | `da2952ad1b6d8db112f6c535ba7a42dad9f926f3d0e9a9b9ea716e139bca68c4` |
| Postcheck evidence | 10028 | `9cfac0f41ee989df4585312389713d12697528b030d60b97badbdb8853c23cf1` |
| Generated `.olean` (removed) | 384056 | `bab3ccab4e0f7330aae9b5ed6ad756df4235f68b0a82fbcd58aa0e479dc9eb6f` |
| Generated `.ilean` (removed) | 13350 | `23197c1ef4ba1aff9bccb6aeed06d2d42a265589c152a69e5d58e48cb116ea5e` |
| Generated `.c` (removed) | 30467 | `4087386ef3a1fb1038cef5166420dfc3842447c45ad787e601188f60e0d0de74` |

`SHA256SUMS` covers every retained file in this directory except itself. The
read-only proposal and its source/provider reasoning remain separately preserved.
This successful check establishes that the complete unchanged mathematical body
elaborates with the proposed header under the recorded setup. It does not check
the clients affected by changing inherited imports. Root owns any integration,
the full affected-client gate, independent Standards/Spec review, exhaustive
audit, required regression, final candidate verification, and checkpoint upload.
The distinct elapsed times and static import counts are not a controlled speedup
measurement. This directory is frozen; no further compiler attempt is authorized.
