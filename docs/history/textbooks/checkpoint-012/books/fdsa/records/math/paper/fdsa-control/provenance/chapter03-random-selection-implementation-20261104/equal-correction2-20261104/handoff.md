# All-equal example correction 2 — immutable handoff

## Candidate

- Finding: `C03-RANDOM-EQUAL-ELAB-002`.
- Candidate: `d82ee6286de99a032eaf5fd925e6b87f48e0fb36`.
- Tree: `a12d8424dc5ec34e2ffbfad504aeecfe1b1eacb6`.
- Parent: `0fa60badfd353bcd6e22177d852d8d6399a2e0fe`.
- Branch: `work/fdsa-ch03-random-selection`; clean.
- Commit: `fix(selection): normalize all-equal example arithmetic (#174)`. Actual exit 0, tool `838705`, command-local ChatGPT identity.
- Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

Only `Examples/RandomSelectionEqual.lean` changes: four proof bodies, 13 insertions and 6 deletions. All 11 example statements, hypotheses, constants, expected outcomes and source connections remain fixed. All 31 equal-pair and all 256 cumulative declaration headers/contexts are preserved. Cumulative scope remains 239 public names, 17 private helpers and 23 computational definitions across 12 files. The other eleven files, including the actually built equal core and its private helper, are byte-identical.

## Actual predecessor evidence and release

At parent `0fa60bad`, the equal core Built in 14s, while Examples failed at five normalization sites. The actual pair CLOSED exit 1: owned 73189, terminal `fb34ee`, root complete closure `422e29`. Complete outer log read: `f1c90c`; complete closed/native/start/result records: `76be47`.

- Outer: 14,337 bytes, SHA-256 `1257d7c756aebda1439afe87057f0056e1e2f6e2201cf1eea6285a217594c65f`.
- Native: 14,053 bytes, SHA-256 `841fbde177c5a54f3681af697c96f72ec1b0f99214724e57c515f818c85165a2`.
- The native body matches exactly at outer byte offset 127.

Both failed attempts' 28 records remain intact, as do all 203 previous own provenance files. The inherited verification record belongs to accepted `c1cefe4`, not this successor. No old execution session was polled. Checkpoint0132 was verified, uploaded and exposed; its explicit release `cc78f1` authorizes only this bounded correction. The release/durability files are preserved. Root's prior binding metadata was read and all 231 referenced hashes verified in `ff3dca`; the initially oversized raw-list display was truncated and is not credited as a complete read.

## Four proof corrections

| Example | Correction | Unchanged statement and connection |
|---|---|---|
| `empty_boundary` | Simplify `Nat.cast_zero` in the existing `scanMean_replicate` result. | Every empty worker rank has `none`, empty trace, source 2, pure scan 0 and real scan mean 0. |
| `singleton_boundary` | Allow standard simplification with the same `uniformIndex_zero` and `PMF.pure_map` equations. | The general valid/invalid replicate laws still give source costs 9 and 11, with trace `[(1,0)]`. |
| `pair_both_valid_ranks` | Prove `3*(1+1)+i+6 = 12+i` for every Nat `i` with `omega`, then rewrite under the PMF map. | Both valid ranks, every generic payload, all `Fin 2` occurrence choices, exact trace and source `12+i`. |
| `five_equal_source_law` | Prove `3*(4+1)+i+6 = 21+i` for every Nat `i` with `omega`, then rewrite under the source-law map. | Five copies of Nat 4 at worker rank 2, all `Fin 5` draws, exact source `21+i`. |

The arithmetic facts are local proved identities, not added hypotheses or new declarations. There is no computational definition change, source-cost reassignment, altered expected case, linter suppression, new assumption or weakened conclusion. The other seven equal-example proofs are byte-identical. All negative-duplicate atoms, general equal-input executions, absorption, linear-versus-triangular family and public-zero boundary remain unchanged. The original independent expected-case file is hash-preserved.

The complete corrected examples and patch were read in `c66213`; predecessor examples in `dfdd37`; unchanged core's complete earlier read is `e295d3`. The exhaustive assessment (`b38bec`) verifies every header, context directive, definition and unchanged source, and retains the original complete statement/private/case assessments.

## Exact source and type-input bindings

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| Corrected examples | 4114 | `e1896b17dafc623d26b37168153505faa48ad93968acb51c15032e58dfe3c150` |
| Unchanged built core | 11702 | `05abf888d8ef2ab6934a1ad90034ac12e07dd7c79f558828fc719bf3973e1dd2` |
| Exact source diff | 2585 | `ddbdf21c6d8ec2fe83ee0bfdd3296266a1f8cc3e33f6065923652658b046a085` |
| `Statements239-equal-correction2.lean` | 13639 | `02ff01193e8571b22f72047661cd7088bab4c19f196800bcc1e21139bbf931d0` |

Examples Git blob: `a5c7bc4c47d5639f1ad62aa3e6ec413c809b7d95`; core blob: `8f6aee1ec143ea2a8a8f02902ea0625289aa0a9c`. The 239 explicit-@ names, order, printing options and input bytes are identical to stage06 and correction1. The new preparation binds this exact commit/tree and all twelve source blobs. It is prepared input, not actual type output. Both whitespace checks and the actual commit exited 0; the committed patch matches the retained artifact exactly.

Root's next newly named sole serial focus:

```text
Applications.Resources.RandomSelectionEqual
Examples.RandomSelectionEqual
```

## Hold and remaining scope

No author Lean/Lake, environment/cache/output/dependency/profile action or canonical control edit occurred. No successor pair pass, complete candidate check, audit, independent Standards/Spec review, immediate verification or Chapter3 acceptance is claimed.

The universal endpoint proof remains next: every arbitrary Nodup input and every valid worker rank, minima while rank is positive then maxima, exact specified-path probability `1/n!`, actual triangular scan attainment, unbounded Nat family and actual source-cost worst-case transport. No endpoint source has started. The supplied read-only endpoint API route remains author assistance, not review evidence. The original Karp access limitation remains disclosed.

All twelve source files and own provenance writes are now HELD for root's actual successor terminal or explicit release.
