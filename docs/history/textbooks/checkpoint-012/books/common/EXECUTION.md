# Current native command settings

**Read this before executing the native command examples in the frozen setup
document or kit.** The user's current instruction in `REQUIREMENTS.md` removes
agent-imposed resource caps. Fixed `--threads 1` examples in `docs/RESUME.md` and
the native kit are superseded for this integration. Do not copy them on resume.

This file is the single current owner of the resource arguments and native
launcher prefix. `docs/RESUME.md` at the checkpoint root still owns recovery,
environment selection, prerequisites, exact pins and the setup budget. Its bytes
are frozen by the package policy. Keep that record, the kit, policy and guards
unchanged; apply the current user exception through the commands here.

## Setup arguments

From the verified checkpoint root, use actual absolute external paths. Reuse an
existing matching runtime instead of reinstalling merely to obtain a new receipt.
Follow the frozen setup document's prerequisites and pin checks.

```sh
CONALED_KIT="$(pwd -P)/support/native-kit"
CONALED_NATIVE_STATE="/absolute/path/to/conaled-native-state"
CONALED_PROJECT="/absolute/path/to/selected/conaled"
CONALED_SETUP_THREADS="$(python3 -B -c 'import os; print(os.cpu_count() or 1)')"

python3 -B "$CONALED_KIT/conaled_native.py" verify
python3 -B "$CONALED_KIT/conaled_native.py" --state "$CONALED_NATIVE_STATE" \
  setup --project "$CONALED_PROJECT" --threads "$CONALED_SETUP_THREADS"
```

The immutable kit requires a positive setup thread argument. Use the detected
host CPU count for that setup-only parameter. It is not the full-build setting.
The ten-minute setup/troubleshooting budget is not a full-build deadline.

## Project commands

After the actual repository workflow has prepared a clean isolated candidate,
select its path as `CONALED_PROJECT`. Run its own gate and final verification:

```sh
python3 -B "$CONALED_KIT/conaled_native.py" --state "$CONALED_NATIVE_STATE" \
  run --project "$CONALED_PROJECT" -- \
  env -u LEAN_NUM_THREADS PYTHONDONTWRITEBYTECODE=1 ./check.sh --candidate HEAD

python3 -B "$CONALED_KIT/conaled_native.py" --state "$CONALED_NATIVE_STATE" \
  run --project "$CONALED_PROJECT" -- \
  env -u LEAN_NUM_THREADS PYTHONDONTWRITEBYTECODE=1 ./check.sh --verify-candidate HEAD
```

The launcher injects `LEAN_NUM_THREADS=1` before executing its child. `env -u`
removes it after that assignment, allowing ordinary hardware-based defaults.
Use the same `run ... -- env -u LEAN_NUM_THREADS PYTHONDONTWRITEBYTECODE=1` prefix
for focused `lake build ACTUAL_MODULE` or `python3 -B scripts/review_snapshot.py`
commands. Supply no replacement numeric thread setting, compiler-process ceiling,
memory/CPU-time limit, affinity pinning, priority reduction or full-run deadline.
Preserve host/platform controls, exact inputs, source checks, public coverage,
integrity guards and the exhaustive audit. The current checkout's README owns
fresh-mode triggers; changing resource settings alone is not such a trigger.

The launcher receipt describes its pre-child environment and will still say
`lean_threads: 1`. Preserve it unchanged. Record the exact argv and the effective
environment of the child that execs the checker, so that metadata cannot be
mistaken for an active cap. A completed setup or focused build is not a full gate.

`VALIDATION-HANDOFF.md` owns the gate procedure and receiving fallback;
`STATUS.md` and `REVIEW.json` own the actual outcome. After a wipe, the root
durability rules require the latest verified archive before project work.
