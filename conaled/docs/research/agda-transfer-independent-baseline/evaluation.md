# Independent evaluation of the #106 baseline

Recommendation: **improve the interface and retest**, subject to an explicit bounded follow-up decision. The independent experiment is valid negative evidence about completion within its budget. It did not produce the selected general source proof, and it neither proves the fragment inadequate nor establishes practical independent reuse. No protocol finding invalidates the archived baseline. Publication and the final orchestration review remain separate completion tasks.

The evaluated candidate is agda-unimath `foundation-core.identity-types.assoc` at `75518656f287c203b41cb7f71df46e02b987a084`. The frozen Lean API is `8b1ed308f29cbe9d00e03c8b6b7780ffeb4b7c17`. Source commit `8267b71` has the identical tree; the author's HEAD remains the original frozen snapshot. I did not implement the framework or first port. I previously reviewed them and therefore could not serve as the independent baseline author.

## Integrity and independence

I recomputed these SHA-256 digests:

| Artifact | Digest |
| --- | --- |
| `protocol.md` | `3c88e9c3b9a5146a207fca18bb8e042337ba9d7238e5cb5674593f104414cd78` |
| `MANIFEST.sha256` | `502e3e3d1128ae34f38739861c92504871c236bfc0369aa035014fc13e8280ab` |
| `unassisted-baseline.tar.gz` | `27c81261b1ff1452acfdb2d999eaab6cd9c8293100fdbae057a9c9308d9f129f` |

All 122 manifest entries match, and all 123 archive files match the preserved files. The final partial artifact equals cycle 40 byte-for-byte. Tracked files have no diff against the frozen API; only `baseline106/` is untracked. The archive was left unchanged. Detailed verification is in `evidence-verification.txt`.

The protocol and orchestration record identify fresh author task `01a15f76-ecf1-7da1-bc56-717ed6849978`, launched without inherited turns or an implementation/review role. I rely on the orchestrator's launch record and the author's declared inputs; filesystem evidence cannot prove absence of unrecorded conversations. Public first-port code and pinned upstream proofs were permitted inputs and are disclosed. My accidental upstream proof exposure during scope review is recorded in `scope-review.md`; no proof advice was relayed to the author. Nothing in the retained evidence indicates author contamination or an API repair during the attempt.

## Result and effort

The recorded attempt stopped at the prospective 40-cycle limit. Three initial investigations are described in the ledger without separately captured terminal output. Cycles 4–40 have contiguous records and preserved snapshots/output. Their category counts match the report: seven translation, seven investigation, eleven debugging, nine helper, one application and two validation cycles. Six recorded commands are source reads/searches; 31 are Lean checks, with 17 failures. The ten-cycle checkpoint and final stop are recorded without resetting the budget. Cycle grouping is an author-defined measure, not a standardized effort unit. No person-hour, token-cost or productivity ratio can be recovered from these counts.

Framework construction and repair were zero during this baseline. Dependency discovery, proof-local helpers, translation and debugging consumed the bounded attempt. A failed Python invocation outside direnv is disclosed; the runner's recorded child exit codes correctly distinguish failed Lean checks from successful runner execution. The cycle-29 diagnostic hit the default heartbeat limit while printing a mismatch. Later partial work used a local 800000-heartbeat setting. That is experimental partial evidence, not production policy compliance or authorization to raise limits in accepted source.

I inspected the complete final partial file and the recorded connection failures. `assocGoal` forms the intended nested identity for arbitrary paths. The checked specialization retains arbitrary later paths but fixes the first to reflexivity. Its generated congruence and beta conversions produce a source identity without assuming the desired result or reflecting semantic equality into syntax. The general motive retains the four dependent entries. These components preserve the selected argument's structure, but there is no completed general branch, J application, interpreted consumer or C4 application of a general source `assoc`.

An evaluator replay of the exact final partial file passed. Its named-declaration axiom inspection reports only `propext`, `Classical.choice` and `Quot.sound`. This does not replace a fresh production build or exhaustive audit, neither of which was claimed for the incomplete transfer. The retained partial statement check is useful EDD evidence; the selected general transfer is not EDD green.

## Interface evidence and comparison

The author reused the frozen calculus, named paths, concatenation, beta, substitutions, generic J congruence/rebuilding and public first-port examples unchanged. The author nevertheless handled dependent pairing, raw substitutions, annotation casts, heterogeneous equality and projection/root coherence. Cycles 29–30 preserve failure to connect a fresh specialization with the actual substituted motive. Cycles 34–35 expose nondefinitional concatenation annotation alignment; raw reindexing and generic rebuilding alone did not finish that connection. These diagnostics identify a concrete unfinished obligation on the attempted route, not a demonstrated need for a new logical rule.

The local concatenation congruence helpers already support the retained specialization and plausibly serve other nested-operation proofs. Generic endpoint, projection and reindexing comparisons could reduce repeated bookkeeping. Their value beyond this partial case and their effect on another author's effort remain untested. This evaluation neither implements those helpers nor prescribes a theorem-specific repair.

After archival I checked a separate direct Lean comparison, preserved in `DirectComparison.lean.txt`, `direct-comparison.log` and `comparison-record.md`, including both failed preliminary invocations. The ordinary result follows from category associativity, and its action consequence applies uniformly to arbitrary set-valued functors. Checked faithful C4 and trivial Fin 2 applications retain nonidentity labels; the composite label is 3, faithful action sends 0 to 3, and trivial action fixes 0. The direct theorem already works across ordinary groupoids and families. Reusing a generated proof across additional interpretations is the extra prospective benefit of the source route; it was not demonstrated for this second theorem. The comparison is not a source transfer or a controlled fresh-author timing experiment.

## Decision consequence

The first port's technical result remains intact, and this archive supplies the mandatory independent attempt even though it is incomplete. It does not establish cheap library translation, general Agda portability, or impossibility from one author's bounded failure. Interface work followed by a separately authorized, uncontaminated retest is warranted before expanding selective porting. Any repair or assisted retry must remain separate from this baseline; claimed fresh-author savings require fresh evidence.

Under #103's entry gate, this recommendation requires resolving the interface-repair/retest decision before smooth implementation. Record the decision explicitly. It does not authorize automatic repairs, repeated ports, a second source language, or replacing source soundness with a direct semantic proof. #102's technical acceptance and the independent experiment are distinct gates; a negative experiment waives neither the former nor #103's smooth-model obligations.
