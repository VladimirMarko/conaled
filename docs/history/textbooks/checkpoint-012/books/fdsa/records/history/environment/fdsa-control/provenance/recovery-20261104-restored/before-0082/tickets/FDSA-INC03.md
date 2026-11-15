# FDSA-INC03 — New-host recovery storage prerequisite

State: **Blocked by current host resources; no restoration/install/build run.**
Recorded 4 November 2026. This is local tracking, not a GitHub issue.

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
