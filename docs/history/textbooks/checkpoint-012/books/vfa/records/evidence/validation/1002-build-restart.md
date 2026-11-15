# Candidate validation restart for memory pressure

2026-11-02 approximately 03:07 UTC. This is an environment adjustment, not a
successful validation record or a source correction.

The isolated checkout `/workspace/scratch/0c54f2db1fdf/vfa-validation` initially
ran the required guarded command on commit
`142adf21f0dc3c5f26658d5f4a5854bd8fd8f2ec` with `LEAN_NUM_THREADS=4`.
Its log is `1002-candidate-142adf2.log`. It had made genuine compilation progress
but was spending substantial time paging imports under the environment limit.

Read-only diagnostics of this task's workers showed hundreds of thousands of
major page faults per worker, while the aggregate cgroup reported:

```text
memory.max     8589934592
memory.current 8589672448
memory.swap.current 0
memory.events: max 20440239, oom 0, oom_kill 0
cpu.max        800000 100000
```

Only this task's validation process group (44063, confirmed from its exact
launcher command) received SIGINT. Its execution session completed with status
130; the retained log ends in KeyboardInterrupt. No proof failure or integrity
rejection had been reported. The process tree was checked to have fully stopped
before changing the checkout. Completed cache artifacts were not removed or
altered manually.

The clean isolated checkout was then advanced to the reviewed corrected commit
`cba657b43ed57e15962858713b819058e7d3c3ca`. The restarted command is:

```bash
export PATH=/root/.nix-profile/bin:$PATH
export NIX_CONFIG='build-users-group =
experimental-features = nix-command flakes'
export LEAN_NUM_THREADS=1
nix develop --command ./check.sh --candidate HEAD \
  > /workspace/scratch/0c54f2db1fdf/work-state/validation/1002-candidate-cba657b.log 2>&1
```

The existing guarded incremental acceptance procedure is unchanged. Its initial
guard hashed 414 artifacts and invalidated 815 modules with missing traces from
the still-incomplete first build. This is expected unfinished/cold evidence;
no unexpected output mismatch was observed at restart. The command still builds
all 953 integrated project modules and must complete the exhaustive proof audit.
The subsequent regression and final candidate-verification gates remain required.

`LEAN_NUM_THREADS` controls Lean's task pool and Lake build parallelism. The
[Lean concurrency reference](https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/)
and [Lake maintainer explanation](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Lake.20parallel.20builds.html)
describe this environment setting. No toolchain, dependency, project source,
integrity guard, audit policy, or resource limit was changed.
