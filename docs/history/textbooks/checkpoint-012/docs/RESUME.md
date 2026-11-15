# Resume and setup

The blocking input/save rules are in [DURABILITY.md](DURABILITY.md). First make the
minimal existence check. Missing/wiped/incomplete input means stop and request the
latest durable archive; do not begin installation or reconstruct code from chat.

## Recover source without installing Lean

From the verified extracted checkpoint root:

```sh
python3 -B tools/checkpoint.py --root . verify --deep
python3 -B tools/checkpoint.py --root . restore-source --to /absolute/new/source-recovery
```

Use a genuinely new destination outside the checkpoint. The restore recreates the
common bare repository and three detached candidate worktrees without running Lean.
Use `--all-saved-worktrees` only when those additional source views are needed.
Read `source/refs.json` and the book STATE before choosing a branch; preserve all
refs and draft streams. Never reset or discard newly found edits. After a wiped
session, `adopt-input` records the verified attached archive as described in
CHECKPOINTS; no unavailable old upload receipt is a recovery prerequisite.

## Authorized setup routes and pinned inputs

The user's clarification on 2026-11-13 makes **Nix optional** for this work.
Preserve the selected checkout's pinned compiler and dependency inputs. Its
`AGENTS.md`, skills and README still govern implementation, review and checks;
the exception changes environment provisioning, not those obligations. Issue
and specification tracking is local and must travel in the checkpoint.

Use an existing matching environment when available. The checkout's Nix/direnv
route remains usable. The embedded `support/native-kit/` is also an authorized
route when its exact project pins match the selected checkout. It is the same
299-file kit reattached by the user, not another package that must be recovered.
The kit stays immutable; [support/README.md](../support/README.md) explains its
current use and the historical status of its internal documentation.

Read the actual selected checkout's AGENTS and README environment/build sections
before setup. Use the current source/ref and local integration records to select
the checkout; the old guidance snapshot under `reference/conaled/` does not select
today's source base. Check available disk space and host prerequisites first.

## Native route

From the verified extracted checkpoint root, set actual absolute external paths
in place of the two placeholders below. The state directory must be outside both
the checkpoint and project source, and contain no whitespace or colon. Keep one
active compiler owner and separate writable outputs for concurrent checkouts.

```sh
CONALED_KIT="$(pwd -P)/support/native-kit"
CONALED_NATIVE_STATE="/absolute/new/conaled-native-state"
CONALED_PROJECT="/absolute/path/to/selected/conaled"

python3 -B "$CONALED_KIT/conaled_native.py" verify
python3 -B "$CONALED_KIT/conaled_native.py" --state "$CONALED_NATIVE_STATE" \
  setup --project "$CONALED_PROJECT" --threads 1
```

The kit requires Linux x86-64/glibc, Python 3.11+, a host C compiler, Git, curl
and zstd as specified in its README. Its `setup` checks the exact bytes of
`lean-toolchain` and `lake-manifest.json` **before acquiring the compiler**. It
authenticates the official release, verifies/acquires the nine exact clean
dependency revisions, prepares an isolated profile, hydrates the cache and runs
smoke checks. An existing complete official distribution can be supplied with
`--toolchain /absolute/path/to/lean-4.35.0-linux` to the same setup command.
Do not rerun full setup simply to obtain another receipt when matching setup
evidence and inputs are already available.

For existing matching state, check it before reuse:

```sh
python3 -B "$CONALED_KIT/conaled_native.py" --state "$CONALED_NATIVE_STATE" \
  doctor --project "$CONALED_PROJECT" --full
```

Any pin, dependency, release or kit identity mismatch stops that route. Do not
change expected hashes, edit manifests, reset dirty dependencies, run `lake update`
or substitute a reduced compiler slice to make setup pass. A later intentional
source-pin change requires an explicit compatibility assessment; today's match
does not authorize this kit for every future revision.

Run the selected checkout's own commands through the launcher. For example,
these are the current candidate acceptance commands, to use only after the
implementation/review workflow has prepared a clean isolated candidate:

```sh
python3 -B "$CONALED_KIT/conaled_native.py" --state "$CONALED_NATIVE_STATE" \
  run --project "$CONALED_PROJECT" --threads 1 -- ./check.sh --candidate HEAD
python3 -B "$CONALED_KIT/conaled_native.py" --state "$CONALED_NATIVE_STATE" \
  run --project "$CONALED_PROJECT" --threads 1 -- ./check.sh --verify-candidate HEAD
```

The same `run ... --` prefix can launch `python3 scripts/review_snapshot.py ...`
with the actual scope manifest and snapshot arguments required by the checkout's
review-loop instructions, or a focused `lake build ACTUAL_MODULE_TARGET` during
development. Wrap the whole command; do not replace the current checker with an
old kit-era checker or inject a caller `LEAN_PATH`. The current checkout's README
owns fresh-mode triggers and checker flags. Kit smoke tests and historical kit
validation records grant no project acceptance. Its dated `docs/PROJECTS.md`
does not impose obsolete gate sequences on the new integration.

## Ten-minute setup budget

Spend at most ten minutes on setup/troubleshooting per recovered session unless
the user explicitly authorizes more. Choose one documented pinned route and at
most one retry addressing a concrete reported failure. If that budget or a real
resource limit blocks execution, record the exact blocker once, preserve the
source, and return to useful paper mathematics or source/statement review. Keep
new formal work explicitly uncompiled. An upload blocker instead stops project
work under DURABILITY; it is not permission to keep accumulating paper work.

Keep installation state, downloads, dependency caches and build outputs outside
the checkpoint. Retain a compact exact input/command/outcome record, including
failed or incomplete attempts. The native kit is a small setup artifact, not an
offline copy of the multi-gigabyte toolchain and dependency caches. Full setup
requires the storage allowance documented in its README; do not delete proof
evidence or other work to create space.

Do not run historical environment experiments, poll old session IDs, repeatedly
clean caches, install alternative upload infrastructure or update dependencies to
make a command pass. Preserve a short error/identity record. For a suspected Lake
integrity recurrence, follow the actual checkout's incident guidance and report
pending actions honestly; retain the guard and bounded setup budget.

Setup smoke/focused success is not full-candidate acceptance. See WORKFLOW for
normal/fresh triggers and exact-candidate gates. See CHECKPOINTS to make useful
recovery, setup findings or mathematics durable before another extended phase.
