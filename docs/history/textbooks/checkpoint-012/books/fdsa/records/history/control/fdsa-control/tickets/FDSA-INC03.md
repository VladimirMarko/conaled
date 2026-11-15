# FDSA-INC03 — New-host recovery storage prerequisite

State: **Resolved by the workspace reset; source restoration and native setup passed.**
Recorded 4 November 2026. This is local tracking, not a GitHub issue.

## Resolution on the reset host

The new preflight had about 59.54 GiB available. The newly supplied 0081 matched
its exact size/hash and all 1,284 payload entries. The unchanged supplied restore
script exited 0 after 50 refs, five worktrees, saved HEAD/status checks and git
fsck. Native setup then verified the unchanged kit/compiler/dependencies and
completed hydration plus smoke tests with exit 0 at 03:53:20 UTC. Three preceding
HTTP429 cache failures are retained; no storage guard or validation gate was
bypassed. Evidence is in provenance/recovery-20261104-restored/ and
provenance/unified-native-recovery-20261104-qualified/.

This resolves only the host storage prerequisite. Foundation f17cc6b still needs
a newly recorded full gate, both review continuations and immediate verification.
No mathematical coverage item is closed by recovery or environment setup.

## Original incident, retained

At 02:20:48 UTC the workspace statvfs reported available_bytes=0 and
raw_free_bytes=2178961408. The initial workspace held about 14 MB of task files,
principally the supplied checkpoint; no task-owned cache could free the required
space. A small bounded evidence write succeeded, but does not satisfy the
compiler installation guard or the full active-checkout storage allowance.
The reported /dev/shm capacity was also below the 5 GiB prerequisite and is
not an approved alternate task installation location. No such route was used.

The supplied archive matches its exact size/hash. All 1,266 payload entries and
298 kit entries pass in-memory checks. Git pack objects were inspected read-only
to obtain exact repository instructions; no restoration or git fsck ran here.
The user reports prior successful complete recovery of this exact checkpoint.

Required remedy: an authorized workspace with sufficient available storage,
normally approximately 12–16 GiB for one fresh active checkout plus additional
space for any independent cache/build copies. Then use the unchanged supplied
restore script and qualified native kit. Retain one Lean thread initially;
memory/CPU probes here do not qualify higher compiler concurrency.

Next formal acceptance remains exact foundation f17cc6b. Its full attempt1 has
unknown terminal outcome and no known live process. Start a newly named full
recorded gate after environment recovery, continue both existing independent
review axes, verify immediately before integration, and checkpoint acceptance.
Chapter1 stays accepted. No ticket or coverage item is closed by this incident.

Evidence: ../provenance/recovery-20261104-host-preflight/host.json,
inspection.json, user-steering.md and README.md. Existing INC01/INC02 records
and their historical resolutions are unchanged.
