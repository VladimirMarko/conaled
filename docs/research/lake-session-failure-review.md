# Lake failures after the incremental acceptance change

Review date: 2026-10-30. This local evidence review supports the temporary
integrity guard and the remaining investigation in #222.

The logs contain **six earlier task contexts** with the same GraphEmission
failure seen in #256 and #268: #185, #240, #242, #249, #259 and #252. Five of
those earlier contexts retain binaries that are byte-for-byte identical to the
binary preserved in #256. #259 has the same diagnostic and metadata pattern,
but this review did not find a separately preserved binary for it. These are
repeated encounters with inconsistent cached outputs, not evidence of eight
independent corruption events. No second cache-consistency failure mechanism
was established by this search.

## Cutoff and coverage

Commit `9a3db79ff7bba61f6004f2c5f2f82ba5c5013202` (#223), committed at
**2026-10-28 23:43:20 UTC**, replaced mandatory fresh acceptance with stock
Lake incremental acceptance and weekly fresh checks. Its changes to `README.md`,
`AGENTS.md` and `scripts/check.py` establish the policy boundary. The session
subsequently reports integration into local master at 23:52:53 UTC ([policy
session, line 1927][policy]). The search uses the earlier commit timestamp to
avoid losing events during integration; this does not assume every concurrent
checkout adopted the policy immediately.

The initial inventory contained 2,036 JSONL files under
`~/.codex/sessions`. Every file was streamed, including sessions opened before
the cutoff, and records were filtered by their UTC record timestamp through
**2026-10-30 19:20:59 UTC**. This yielded 52,932 records in the interval before
filtering by record kind. `~/.codex/archived_sessions` was absent. The search did
not inspect authentication files, databases, remote sessions or deleted logs.

Method:

1. Search Git history for the fresh/incremental policy change and inspect its
   diff and timestamps.
2. Decode `function_call_output` and `custom_tool_call_output`, recursively
   unwrapping the JSON/list/text layers used by tool orchestration. Search for
   `stale`, `corrupt`, unknown identifiers/constants, missing object files,
   invalid headers, build/fetch failures and `error:`. A supplementary scan
   checks panic, segmentation fault, out-of-memory, disk-space, killed-process,
   download/extraction and Lake package/manifest errors. Search agent messages
   separately for cache diagnoses and recovery descriptions.
3. Read surrounding commands and actual diagnostic outputs for suspected
   artifact failures. Discard documentation, source dumps, hypotheses,
   deliberate reproduction fixtures and unrelated repositories as incident
   evidence. Group repeated polls, failed repair attempts and reviewer retellings
   by task checkout and failure episode, not by session or keyword count.
4. Follow preserved-artifact paths from those sessions, read their retained
   build logs where needed, and hash the surviving binaries without changing
   them. Compare bytes across task contexts before attributing separate causes.

This is a keyword-assisted investigation, not an exhaustive classification of
every unsuccessful compiler invocation. Tool output can be truncated, logs can
be incomplete, and fresh-mode success does not expose every inconsistent unused
artifact. The interval ends before guard development. A negative search result
cannot establish that other failures did not occur.

## Confirmed GraphEmission encounters

All times below are UTC diagnostic observation times, not artifact creation
times. Each row is a distinct task context; repair retries and review copies
are included in its row. Session citations refer to local JSONL line numbers,
which remain useful while these private logs are retained.

| Task | Observed | Evidence and disposition |
|---|---|---|
| #185 | Oct 29 20:41:54 | `Unknown identifier` for `GraphEmissionPure.ArtifactTyped` and related declarations. The next inspection found the old binary beside a newer trace. Removing that binary and rebuilding passed, followed by the complete 891-module check and audit. [Session lines 202, 226, 235, 243, 271][s185]. |
| #240 | Oct 29 20:58:06 | The candidate check failed in unchanged `Examples.GraphEmission`; direct Lean invocation reproduced it. The session preserved the binary and rebuilt it. The repaired candidate check passed all 900 modules and the audit. [Failure/repair session lines 696, 734, 746][s240]; [acceptance output, line 1859][parent240]. |
| #242 | Oct 29 21:35:50 | Full acceptance failed in `Examples.GraphEmission`. The trace listed output `8e3cc7e2fd7486e2.olean`; the old binary remained present. The session moved aside its `.olean`, `.ilean` and `.trace`, then targeted rebuilding passed without source edits. It proceeded to fresh acceptance. [Session lines 784, 810, 828, 840, 850, 852][s242]. |
| #249 | Oct 29 23:12:48 | Dependency/setup building failed with the same missing GraphEmission declarations. An initial repair used the wrong path and changed nothing; retrying before the correct removal failed again. The correct binary was preserved and removed at 23:13:30. The setup record reports successful rebuilding without source changes. These retries are one episode. [Session lines 140, 144, 146, 154, 163, 199][s249]. |
| #259 | Oct 30 13:58:43 | Full acceptance failed with the same GraphEmission diagnostics in its own checkout. Inspection reported an October 24 binary beside a newer trace. Fresh acceptance passed all 919 modules and the audit. Similarity to the inherited artifact is strong, but byte identity is unconfirmed for this row. [Session lines 1120, 1127, 1133, 1278][language]. |
| #252 | Oct 30 14:07:54 | Full acceptance and a direct Lean probe failed. The retained binary was 1,652,536 bytes; removing it and rebuilding the example passed. [Session lines 864, 868, 878, 887, 897][s252]. |
| #256 | Oct 30 16:33:31 | Known incident: the integration check failed in GraphEmission. Its binary was moved to the task's evidence directory before rebuilding. [Session lines 2738, 2757][language]. |
| #268 | Oct 30 18:34:18 | Known incident: the candidate check failed with the same missing declarations. Subsequent hashing and trace inspection connected it to the donor cache and #256. [Session lines 3545, 3621, 3802][language]; [existing investigation](lake-output-cache-mismatch.md). |

The characteristic diagnostic is:

```text
Unknown identifier `GraphEmissionPure.ArtifactTyped`
```

The #185 repair is especially direct: the original diagnostic, binary removal,
targeted success and full acceptance success all appear in one session, with
no intervening source repair. The #242 trace already contains the same output
identity and historical `/tmp/conaled-233` build path later investigated for
#268. Neither the path nor the file modification time identifies the operation
that mixed the files.

## Artifact identity and remaining cause uncertainty

On this review date, `sha256sum` over these six surviving files returned the
same value, and `cmp` confirmed equality against the #256 file:

```text
1706bc30e261488c78ece61d611928de6a4262f329ae4df4d5ea15b1ef2fdc0a
```

| Task | Preserved file |
|---|---|
| #185 | `/tmp/conaled-realizations/185-stale-GraphEmission.olean` |
| #240 | `/tmp/conaled-realizations/240-stale-GraphEmission.olean` |
| #242 | `~/.local/state/conaled-supervision/scan-optimality-242-244/stale-graph-artifacts/GraphEmission.olean` |
| #249 | `/tmp/conaled-sequential/249-stale-GraphEmission.olean` |
| #252 | `/tmp/conaled-next/252-stale-GraphEmission.olean` |
| #256 | `/tmp/conaled-language-work/256-record/stale-cache/GraphEmission.olean` |

The preservation commands are cited in the encounter table. The existing
[#268 investigation](lake-output-cache-mismatch.md#what-survived) records the
same hash in #268 and the donor cache. Thus the additional hashed encounters
extend the known artifact's history rather than establish new corruption.
These temporary files are evidence pointers, not repository dependencies.

The cache-copy history and identical bytes support inherited inconsistent
outputs as the common explanation. They do not reconstruct the original
mixing operation. In particular, an old modification timestamp does not prove
the inconsistent state existed on that date. The failures occurred after the
policy change, but this evidence does not show that the policy change created
the inconsistent state. Mandatory fresh checks would have bypassed these
project artifacts; they would not necessarily have repaired the donor cache.

## Other errors do not establish another cache defect

The search also found ordinary unsuccessful development builds. Unknown names
alone are not a cache diagnosis:

- `RetentionService` reported a kernel unknown constant
  `Durability.Retention.command_refines` at Oct 30 14:30:16. The same compiler
  output first reports a parse error and an unknown tactic in that newly
  authored module; the next command repairs its source. This is not evidence
  of stale imported artifacts. [Session lines 159 and 170][retention].
- Direct `lake env lean` probes reported missing object files for
  `SquareKit.ListInitial.Fusion` and `Applications.Sequences.OrderedSummary`
  while #252 was being developed. Those are missing prerequisites for direct
  compilation, not proof that `lake build` accepted an inconsistent existing
  output. [Session lines 257 and 269][s252].
- `Leaf.newValue` failures belong to the deliberately mixed-output reproduction,
  not additional historical incidents. [Language session lines 3830, 3840 and
  3854][language].

The temporary guard addresses the demonstrated disagreement between actual
output bytes and a trace's recorded output identity. This history strengthens
the case for detecting that disagreement before accepting copied caches. It
adds no guarantee for a wrong but internally consistent trace/output pair,
concurrent mutation, or external dependency artifacts. Those limitations remain
in the [mitigation discussion](lake-output-cache-mismatch.md).

[policy]: /home/vlad/.codex/sessions/2026/10/26/rollout-2026-10-26T14-42-36-01a17872-de1b-7882-a558-50abccb0878a.jsonl
[s185]: /home/vlad/.codex/sessions/2026/10/29/rollout-2026-10-29T21-38-18-01a18962-89ef-7123-85b2-a53d4ad3e622.jsonl
[s240]: /home/vlad/.codex/sessions/2026/10/29/rollout-2026-10-29T21-27-14-01a18958-65fd-79e1-ac08-0d9779a75584.jsonl
[parent240]: /home/vlad/.codex/sessions/2026/10/29/rollout-2026-10-29T20-28-26-01a18922-91f1-7c03-bcd4-b567fd81be1b.jsonl
[s242]: /home/vlad/.codex/sessions/2026/10/29/rollout-2026-10-29T21-05-08-01a18944-2b9f-77c0-aaed-c3cf618dd46c.jsonl
[s249]: /home/vlad/.codex/sessions/2026/10/30/rollout-2026-10-30T00-09-31-01a189ec-f8aa-7681-a279-7da9fbf42ed9.jsonl
[s252]: /home/vlad/.codex/sessions/2026/10/30/rollout-2026-10-30T14-39-33-01a18d09-83b9-7821-a371-f4feb5410fa9.jsonl
[language]: /home/vlad/.codex/sessions/2026/10/30/rollout-2026-10-30T12-37-52-01a18c9a-1bfe-79a3-b131-c30b9045deff.jsonl
[retention]: /home/vlad/.codex/sessions/2026/10/30/rollout-2026-10-30T15-21-11-01a18d2f-a1f6-7c51-a379-1170ea6841fa.jsonl
