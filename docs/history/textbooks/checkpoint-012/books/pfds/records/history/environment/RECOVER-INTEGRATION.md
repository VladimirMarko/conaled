# Recover the common PFDS integration candidate

This is the current recovery entry point after checkpoint 044. Read
`session/STATUS.md` first. The full book/thesis union is unfinished; Chapter 2
is the earliest unaccepted chapter. Setup, focused builds and controller tests
are not chapter acceptance. Historical partial execution handles never survive
recovery, and a lost terminal result remains incomplete.

## Restore sources and the supplied environment

The compact checkpoint preserves all task source commits, pending review bases,
local tickets, requirements, reviews and validation evidence. Its Git bundle
requires the unchanged public upstream commit
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. The included `restore.py` obtains that
exact commit from the original public repository, or accepts
`--base-repository /path/to/local/conaled` for offline source restoration. This
omits the large unchanged upstream archive from frequent checkpoints. It does
not change any tracked project source or require a previous numbered checkpoint.
Compiler/dependency caches and research manuscript PDFs remain excluded.

Set `PFDS_ROOT` to the restored directory containing `conaled/` and `session/`.
The exact supplied kit archive is included under `session/environment/`:

```sh
PFDS_ROOT=/absolute/path/to/restored/pfds
PFDS_KIT_PARENT="$(dirname "$PFDS_ROOT")"
PFDS_KIT="$PFDS_KIT_PARENT/conaled-native-kit-4.35.0"
PFDS_NATIVE_STATE="$PFDS_ROOT/native-state"
test ! -e "$PFDS_KIT"
tar --no-same-owner -xzf \
  "$PFDS_ROOT/session/environment/conaled-unified-native-kit-lean-4.35.0-2026-11-03.tar.gz" \
  -C "$PFDS_KIT_PARENT"
python3 "$PFDS_KIT/conaled_native.py" verify
python3 "$PFDS_KIT/conaled_native.py" --state "$PFDS_NATIVE_STATE" \
  setup --project "$PFDS_ROOT/conaled"
python3 "$PFDS_KIT/conaled_native.py" --state "$PFDS_NATIVE_STATE" doctor --full
```

Run each command only after its predecessor succeeds. If the sibling kit
already exists, verify that exact existing kit instead of extracting over it;
otherwise use a different fresh recovery parent. The native state path must
contain no whitespace or colon. Read the kit's README and recovery guidance
for disk allowances and documented offline inputs. Preserve source pins and
expected hashes on failure. The exact kit archive SHA-256 is
`45edfb844068f93b26ea5469572473f8c07e5a63e2bc294eed6de543cb3d5bf2`;
its `SHA256SUMS` SHA-256 is
`72ba31d697b09e71cd21edbf6a46340f1fef6380585df86eb0320e1b05b737b6`.

`unified-native-setup-045.md` and its JSON/log/retained evidence describe the
actual first recovery: nine clean dependency pins, 9,031 cache files and ten
successful expected smoke outcomes. A new recovery needs its own setup
evidence. The 47+8 doctor checks are bounded runtime checks, not a complete
fresh distribution attestation or proof audit.

## Exact candidate and private project outputs

Only the fixed integration candidate below is supported by the new scope:

```sh
git -C "$PFDS_ROOT/conaled" worktree add --detach \
  "$PFDS_ROOT/validation-pfds-integration" \
  3cf3de4fbc24c1a144353ae64b13b72f5ead54a5
mkdir -p "$PFDS_ROOT/validation-pfds-integration/.lake/build"
ln -s "$PFDS_ROOT/conaled/.lake/packages" \
  "$PFDS_ROOT/validation-pfds-integration/.lake/packages"
git -C "$PFDS_ROOT/validation-pfds-integration" status --porcelain=v1
```

Use these creation commands only for an absent checkout; inspect an existing
checkout instead. The checkout, `.lake` and `.lake/build` must be real private
directories. Only the exact pinned dependency store is shared under the
preserved PFDS serial-writer discipline. No other compiler, cache writer, setup
process or dependency mutation may run during recorded validation. The general
kit's project-scoped `setup/deps/doctor` rejects shared package layouts; for
this PFDS-specific arrangement use runtime-only doctor and the controller's
separate exact dependency checks. Do not weaken the kit's guards.

The legacy default still binds `import-correction-r3` to
`901f734161920a76f3b399a575805b9a1d31e971` through its historical native launcher.
Focus still binds `signed-potential` and its explicit focus-only correction
option. `--scope integration` is rejected for focus. No arbitrary full path or
candidate is accepted. Historical prerequisite records cannot verify integration.

## Recorded full gate and immediate verification

The changed controller must have both independent operational outcomes and an
exact delivered-identity receipt before its first real integration gate.
Consult the current operational review record, not an older approved revision.
After that approval, use a new unused run ID:

```sh
python3 "$PFDS_ROOT/session/validation/run-native-validation.py" \
  full integration-3cf-fresh-r1-045 --scope integration --fresh
```

The actual stock command is `./check.sh --candidate HEAD --fresh --jobs 1`.
The controller imports the unchanged pinned kit, calls its
`environment(native-state, 1)` API and launches the stock checker directly in
its own process group. This is the same environment selection used by kit
`run`, without nesting another session whose child could escape controller
cleanup. The record accurately names this provider and actual argv.

All modes hold both legacy full/focus cooperative locks. The controller records
queued, start and final source/dependency/runtime/controller identities, actual
terminal exit, complete log hash and the stock verification record. Its
`acceptance` field always remains false. New files are exclusive. Full evidence
is scoped to its exact candidate/checkout/runtime and its exact stock mode;
verify rejects wrong-scope, partial, failed, changed or mismatched evidence.
Only volatile doctor `free_bytes` is omitted from frozen-input equality.

Evidence appears under `session/validation/RUN_ID.json`, `.log` and, only on
successful full validation, `.verification.json`. A failed or interrupted run
is evidence of its own outcome; never reuse its name or infer a pass from a
partial log. If the execution service loses a handle, retain the original
partial record and add a separate observation record. Do not fabricate an exit.

After actual full success and applicable independent review reconciliation,
immediately before acceptance run:

```sh
python3 "$PFDS_ROOT/session/validation/run-native-validation.py" \
  verify integration-3cf-verify-r1-045 --scope integration \
  --full-record integration-3cf-fresh-r1-045
```

Verify does not receive `--fresh` or `--jobs`: the matching full record owns
that mode. Each separate acceptance action needs immediate matching verification.
Fresh outputs are temporary and removed by the stock checker. If ordinary
outputs are required for negative-audit regression, run a distinct guarded
incremental full gate with a new ID and no `--fresh`, preserve both full records,
and verify against the record matching the current live stock record. Do not
copy or rewrite a verification file to avoid revalidation.

## Formal review and dependency ordering

The common-candidate scope matrix is
`session/reviews/common-integration-scope-matrix-045.md` with exact identities
in its accompanying validation JSON. It covers nine pending scopes, their
original full bases, complete enlarged diffs, ownership boundaries and every
retained finding. Both independent formal axes must cover that full scope.
Identical historical analysis can be retained with an explicit identity/context
check; old Blocked outcomes are not approvals of the new candidate/runtime.

One actual common-candidate full/audit record can support separate scope
decisions only on that same exact candidate. Preserve separately applicable
stock regressions, dependency-ordered acceptance, source/statement coverage,
complete reviews, immediate verification and exact delivery. The historical
901 root/checker suite results are not automatic approvals under a new runtime.
Chapter 3 algorithm work follows actual Chapter 2 acceptance. The book PDF must
be reattached for additional unavailable source inspection; its historical
Library identifier does not authorize retrieval from another conversation.
