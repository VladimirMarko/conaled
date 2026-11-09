# Preserved natural-number checker experiment

This experimental #137 slice reproduces the selected checkpoint-233 parser and
source-agreement closure, then checks an independent doubling endpoint and a
successor consumer. The [report](../../docs/research/certified-nat-checker-preview.md)
records the boundary and unfinished broader inspection. Original source stays
inside the immutable archive; `selection.json` specifies its exact members,
hashes, imports and compilation order. `CheckerClient.lean` is new conaled code.

From a clean committed checkout, with a new output path outside the repository:

```sh
direnv exec . python3 experiments/certified-nat-checker/test-reproduce.py
flock /tmp/conaled-369-orchestration/build.lock \
  direnv exec . python3 experiments/certified-nat-checker/reproduce.py \
  --out /tmp/checker-137-fresh
```

The lock path above is this workstream's shared lock; independent installations
should use their own shared build lock. No previous worktree, Downloads file,
prepared ADWH objects, Mathlib cache or network download is needed once the pinned
Lean toolchain is installed. Compiler libraries are trusted toolchain inputs.
`--prepare-only` checks extraction, import order and inverse correspondence
without compiling; its receipt always has `complete=false`.

The runner refuses existing output directories and requires tracked validation
inputs and a clean candidate before compilation. It rebuilds 20 archived modules,
`Squares`, the new client and the existing `ClosureAudit` tool. The audit covers
all 22 mathematical/client modules, including private/generated safe roots;
the audit tool itself is metaprogramming infrastructure. It reuses the bounded
command executor from `relative-graph/reproduce-acceptance.py` and the source
policy from `scripts/check.py`. It does not run the archived gate scripts.

Each compiler process has a 120-second deadline, one thread and an 8-GiB virtual
address cap. The whole compilation sequence has a 20-minute deadline. Output is
capped at 1 MiB per command. Linux runs restrict CPU affinity to one available
CPU. Initial investigation showed Lean startup failing under a 4-GiB virtual
cap before elaboration; increasing that cap does not imply comparable resident
memory consumption. Failed runs retain their logs and an incomplete receipt.

`provenance.json` contains candidate, compiler/input identities, before/after
checks, staged source hashes, fresh output hashes, time and maximum child RSS.
`logs/commands.json` contains exact commands and exit codes. These are ordinary
local validation records, not a proof of executable-binary correctness or a
replacement for independent review. No native checker, queens numeral workload,
or modified kernel runs. Normal main-repository `check.sh` does not import this
isolated experiment; its fresh reproduction and audit are separate requirements.

## Reflected first-row comparison

Select the comparison profile to reproduce the corrected reflection and exact
masked-source route:

```sh
flock /tmp/conaled-369-orchestration/build.lock \
  direnv exec . python3 experiments/certified-nat-checker/reproduce.py \
  --selection comparison --out /tmp/checker-137-comparison-fresh
```

`selection-comparison.json` contains the complete 27-module source-comparison
closure plus the two archived parser/endpoint modules needed by the already
accepted `CheckerClient`. It therefore extracts 29 archived modules, then adds
`Squares`, `CheckerClient` and `ReflectionClient`. All 32 mathematical/client
modules are audited. No archived CLI or native numerical workload is executed.
The default `checker` selection retains the original 20-module profile.

Preparation also replays the three proof corrections from the failed reflection
predecessor, checking every intermediate hash and the exact corrected bytes.
The [route disposition](../../docs/research/cqueens-preview-disposition.md)
distinguishes this source reproduction from supplied runtime evidence, failed
complete kernel selections and the missing strong-CSP generated input.
