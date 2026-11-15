# Pinned Lake and Lean concurrency controls

Inspected 2026-11-02 for the unchanged Lean 4.35.0 / Lake 5.0.0-src+eb6cafb
environment. This note changes no repository source, tool, pin or acceptance
gate. It addresses the documented shared-memory pressure in
`validation-performance.md`.

## Primary evidence

- Installed `lake --help` exposes no `-j`/`--jobs` option. Its `BuildConfig` in
  `src/lean/lake/Lake/Build/Context.lean` also has no build-worker limit field.
- The exact compiler commit is
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Its [runtime source](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/runtime/object.cpp)
  defines `get_lean_num_threads`: it reads `LEAN_NUM_THREADS` when present and
  otherwise uses hardware concurrency. `lean_init_task_manager` passes that
  result to `lean_init_task_manager_using`, which constructs the task manager
  with that standard-worker count. The fetched source SHA-256 is
  `1dba3476a698ab05f8f0a56c323487755790675046e90219218cb9727658ead4`.
- Pinned `Lake/Build/Job/Monad.lean` defines ordinary asynchronous jobs using
  `BaseIO.asTask` at the default task priority. `Lake/Util/Proc.lean` calls
  `IO.Process.output`. Pinned `Init/System/IO.lean` implements that operation
  by spawning a child, reading stderr synchronously, waiting for the child,
  and collecting stdout on a dedicated task.

Thus `LEAN_NUM_THREADS=1` is an actual supported runtime scheduler control;
it is not an invented Lake CLI option. Dedicated I/O tasks and waits can use
additional OS threads. A one-worker setting is not a claim that the process has
one OS thread, nor an independently proved hard cap on every possible subprocess
under all Lake extensions. Actual compiler-child concurrency should be observed
when first using it for a complete incremental build.

## Acceptance route

The README's routine committed-candidate route is:

```
nix develop --command env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD
nix develop --command ./check.sh --verify-candidate HEAD
```

The first command retains source policy, public coverage, clean candidate and
dependency identity checks, pinned compiler checks, stock Lake input tracking,
before/after output-integrity guards, and the exhaustive proof audit. It changes
only a documented runtime scheduling input. Successful normal Lake outputs are
then available for later candidates. No output is copied into Lake behind its
tracking mechanism.

The README reserves required fresh mode for build/toolchain/dependency changes
or suspected stale outputs, and describes periodic fresh checks separately.
Chapter 1 changes mathematics and documentation, not those tooling inputs. Its
saved acceptance requirements ask for applicable project verification, not a
specific fresh mode. A complete guarded incremental candidate check therefore
remains the documented applicable gate; incomplete earlier fresh attempts do not
count toward acceptance.

`./check.sh --fresh --jobs 1 --candidate HEAD` remains the explicit, supported
strict single-compiler alternative when fresh mode is needed. Its private
outputs are deleted, so it does not populate the normal incremental cache.
