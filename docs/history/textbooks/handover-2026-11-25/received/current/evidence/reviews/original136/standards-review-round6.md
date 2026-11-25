# Standards review — round 6 — C6c

**Outcome: Blocked.** The independent Standards assessment of the supplied C6c material is complete. ST-001 requests correction of contradictory current continuation gates. The stable mandatory validation finding ST-V001 remains unresolved. I found no additional Lean implementation or checkpoint-helper defect in the material read. This is not source acceptance, whole-row qualification, or receiving approval.

## 1. Reviewer, candidate, and evidence boundary

Reviewer: the original independent Standards axis, `/root/parser_review/standards`, continuing the same review loop. Date: 21 November 2026 UTC. Root remains the implementer and coordinator. The read-only relay `/root/verify_seed` supplied material; it did not supply this review's conclusions.

| Identity | Value |
|---|---|
| Original accepted public prerequisite B | `bc95f503ccbf043136c6699992388f750270e8e6` |
| B tree | `3cf266b2a1fa38f13159692fd9ef43fbccaf9009` |
| Reviewed candidate C6c | `2b3738c116b1a9a439a8fa38663e2da824a56339` |
| Reviewed source tree | `49fa40ddd4a5f84a0b743a0b8ca2df6248dbd930` |
| Manifest | `manifest-6.json`, 22 paths, empty entries and exclusions |
| Requirements | `requirements-6.txt`, 312,060 bytes, SHA-256 `2951b9e12bc0c3cf43d3f5c02c621015086040e80ec000f1fc5752a00274d0bc` |

The actual B-to-C6c diff has 22 files, 11,489 insertions and 164 deletions, with the exact manifest path set. It includes 17 author Lean owners, the entrypoint, and four maintained documentation owners. The receipt's outside-scope inventory concerns unchanged tree paths; it is not a manifest exclusion.

This endpoint repeatedly lacked a usable execution environment. I therefore read the actual immutable Git bodies, audit output and evidence through the authorized relay, bound to paths, ranges, sizes and hashes. I did not personally execute Git, Lean, archive verification, recovery, or hashing of filesystem artifacts. The report distinguishes the relay's mechanical comparisons from my assessment of the supplied contents.

Long audit displays used only the reversible prefix substitutions `BCFW.` for `Resources.BinaryCounter.FixedWidthMachine.` and `RCFD.` for `Resources.RotationCertificate.FuelDispatchMachine.`. The relay checked absence of these short prefixes in the original log and exact inverse byte equality. Two manual message transcription errors were explicitly corrected against the actual artifacts: example source line 414 uses `next sentinelCaller`; audit line 8826 uses `instOfNatNat`. Neither was a source defect. Chunk hashes identify the tool-read artifacts, not an independently hashed rendered message. Lean's own printed proof elisions were retained.

Later active tree-core work, the 24-path candidate and checkpoint103 are outside this C6c assessment. They do not silently replace the reviewed source or the frozen102 helper bundle.

## 2. Findings and disposition

### ST-001 — Medium — Open against C6c

**Current continuation gates still prescribe the earlier nineteen-path scope.**

Affected immutable locations:

- `docs/textbooks/CTB.json:236`, `/local_state/CTB-78/next_action`.
- `docs/textbooks/coverage.json:920`, `/qualification_basis/current_gate`.
- `docs/textbooks/CTB.json:1564`, `/local_state/CTB-24/next_implementation_gate`.

The first two values still direct a continuation to “Freeze the full nineteen-path candidate” for validation and independent review. The CTB-24 gate still directs implementation of the strict pair-framing plan and preservation of “the existing twelve author Lean owners.”

C6c instead contains the complete 22-path candidate and 17 author Lean owners, including the recovered, normally built predecessor, decoded dispatcher and connected clients. Newer `author_increment`, `fuel_machine_preparation` and top-level `next_ticket_gate` values describe that development, but the named operative current and next gates contradict them. A continuation following those gates can select the earlier subset and omit the three fuel owners.

This is a current-record defect, not a claim of actual checkpoint loss: checkpoint102 preserves all 22 source paths. The unchanged guidance makes CTB and coverage the owners of current mathematical progress and requires each delivery to state its current scope, unfinished obligations, validation and next action. Relevant owners are `docs/textbooks/README.md`, `docs/textbooks/external-agent.md` and `docs/agents/task-authority.md`.

**Required correction:** synchronize the operative gates to the full current manifest and actual implementation stage, or explicitly identify superseded instructions as historical and bind them to their older candidate. Preserve canonical requirements and historical acceptance objects.

**Implementer disposition:** root acknowledged the finding and will correct the named active gates for the complete current 24-path/tree-core stage in the next candidate. Root will preserve C6c and secured103/C7a. That correction has not been reviewed here; ST-001 remains open against C6c and requires an immutable follow-up through this same axis.

### ST-V001 — Blocking validation — Unresolved

The required passing exact-candidate whole-library guarded check and exhaustive audit, final nonrepairing verification, and supported post-validation comparison are not available for C6c. Focused builds, Audit6, source recovery and archive delivery do not discharge this gate.

The latest supplied actual observation is `acceptance-c6c-exit137-first-observation.json`, 2,175 bytes, SHA-256 `b5e4eca7dcfe842f171622573c314d22db9c19d0404640a3387d6fdc906f4bf0`. At 2026-11-21T22:34:24.442878+00:00, root session13287 was still running and had reported at least one constituent failure:

- `Examples.CartesianFilling`, log line6119, build header `[10166/10242]`.
- Actual diagnostic: `Lean exited with code 137`.
- Final outer outcome unknown; cause not established by the log; no passing receipt.

The failed module is outside the B-to-C6c changed-path list. The observation does not include an actual failed-file body comparison. Neither its unchanged-path status nor exit137 establishes the cause or permits waiver. I do not infer an out-of-memory diagnosis or a Lean source defect.

Historical failed whole validation and the interrupted C5b check retain their original scopes. C5b has no known final passing outcome after the reset. A later completion of session13287 must be recorded separately.

**Required disposition:** investigate and complete the matching mandatory gate, obtain its passing receipt, perform final nonrepairing verification and the supported post-validation comparison, then return through the same review loop. This finding adds no separate pre-validation comparison requirement. No source acceptance or row qualification is authorized while it remains unresolved.

## 3. What was actually read

The new requirements suffix was read completely. The first 218,148 bytes exactly preserve requirements5; the older required prefixes are also preserved. All three new Lean files were read in full:

| Owner | Bytes | SHA-256 |
|---|---:|---|
| `Applications/Resources/BinaryCounter/FixedWidthMachine.lean` | 40,378 | `005720a8f68c8140125a9e22724bdb007d096cc55bb253dc982cd2b6f3a86b76` |
| `Applications/Resources/RotationCertificate/FuelDispatchMachine.lean` | 28,035 | `a233cf25f0557e6bdad5c763e187c18199b2a7fbb1322b62ef2747f7127e665a` |
| `Examples/RotationCertificateFuelMachine.lean` | 40,502 | `0e97492fa34beac791117d3e04cc35b450d23cf76ee9c001300f0a12b7fe375b` |

Actual Audit6 reading covers all 91 core and 65 dispatcher public types, original log lines6728–9147; all 78 new definition prints and all 27 synthesis outputs, lines11506–12981; and the exact 27 synthesis commands. Four selected example theorem types were read at lines10336–10400 and11408–11505. These cover live handoff/caller/halt, the workspace counterexample, and the eager binary 48/57 separator. The complete examples source was read.

Standalone example type output at lines9148–10335 and10401–11407 was not relayed or freshly read by this axis. Some example timed types and values also occur in the fully read print tail. I do not claim to have reread every one of the 217 added standalone public type checks or every inherited audit line.

I also read the relevant pinned TM2 and EvalsTo APIs; every changed CTB and coverage value, with exact identical mirrors grouped; the full inbox diff; every distinct new paper prose segment and the complete preserved plans; all five frozen102 helper files; and the actual102 archive, recovery, save and upload records. Detailed artifact identities and mechanical comparison results are preserved in the companion JSON and the authorized relay's bridge records.

## 4. Formal implementation and connected clients

### Fixed-width predecessor

The predecessor's mathematical specification independently distinguishes positive words `false^k ++ true :: tail` from all-zero words. Positive execution returns `true^k ++ false :: tail`; failure restores the original all-zero word. Width and arbitrary high-tail bits remain literal data. The correspondence to the existing source counter uses its actual returned predecessor, without normalizing high zeros or substituting an unrelated witness.

Owned runtime blocks use actual finite pop, branch, push, reset and goto operations. Whole-list length, numeric interpretation and the proof-side predecessor function do not enter runtime callbacks. Fuel has Bool symbols, borrowed positions have Unit symbols, and the local observation register is Option Bool. The caller's register component and protected stack family remain explicit. Generic semantic theorems are intentionally more general than finite instantiations; the finite instances and concrete clients supply the required finite alphabets, labels, registers and stack identifiers.

The phase equations allow arbitrary incoming registers, protected data and pending borrowed tokens. Pending scratch represents already borrowed low zeros. General borrow time is `runSteps raw + borrowed.length`, and its logical original input is `false^borrowed.length ++ raw`. The client counterexamples correctly prevent omission of that scratch. Empty-scratch positive execution takes exactly `2*k+2` pinned TM2 transitions; all-zero width b takes `2*b+2`; the uniform bound is `2*width+2`.

The program exposes live result labels and delegates external bodies to the actual caller. The ambient-program agreement theorem preserves this ownership boundary. The source tariff remains separate from the TM2 clock; the implementation does not promote structural source work into machine time.

### First-handoff invariants and timing data

The owned-label predicate, proof-side remaining rank and actual local-step lemmas establish progress and a rank decrease of one. Prefix theorems produce an actual present configuration, a path of owned-source steps, exact remaining rank, and the distinction between earlier owned states and the first live exit. Caller independence extends through that endpoint.

The represented-fuel invariant tracks the original word through borrowing and both restoration phases. It is separate from the unconditional frame and cell laws. Cell conservation counts fuel, borrowed cells and every protected stack; it applies to local paths through handoff. It does not cover arbitrary subsequent caller allocation.

The timed records are actual Type-valued EvalsToInTime data with the pinned transition function and endpoint, rather than assumed oracle fields. The sentinel client demonstrates the scope sharply: the predecessor reaches a live handoff at step2 with unchanged cells; the caller pushes a protected cell and halts at step3, still producing a present halted configuration; step4 yields outer None. Actual timed composition uses that same caller and intermediate configuration. The generic composition client states its caller-time premise explicitly.

### Decoded-certificate dispatch

The dispatcher specializes the same predecessor program and adds a protected Tag certificate stack plus an inspection block. Inspection peeks at presence and preserves the complete certificate. Empty certificate dispatch takes one transition and leaves arbitrary fuel and borrowed scratch untouched. A nonempty certificate adds one transition to generalized borrowing; empty-scratch bounds are `2*k+3`, `2*b+3`, and uniformly `2*fuel.length+3`.

The three live exits remain distinct. Dispatch does not decide certificate syntax, tree equality or rotation legality. Its rank, frame, cell and caller-independence results retain the first-handoff boundary. The source continuation connection reuses the actual returned fuel and the actual parsed/applied fields; it does not equate dispatcher time with complete verifier execution.

### Independent connected examples and scope

The 61 public client declarations exercise zero width, redundant high zeros, nonpalindromic words, arbitrary stale registers and context, pending scratch, positive and restored-zero paths, ambient callers, actual prefix invariants and post-handoff allocation. They distinguish EOF equality from nonempty processing, reserved and incomplete syntax, and an actual emitted rotation.

The binary examples preserve eager decoding order: a 24-bit encoded input with a one-bit incomplete certificate rejects with source observation48, whereas a fully packed tag rejects with observation57. Only a completely decoded certificate reaches the five-transition zero-fuel gate in the supplied separator. The token-level untouched suffix property is not extended to unread raw binary input.

The pinned API confirms that TM2.step executes a bounded statement block, a halt statement returns a configuration with no label, and the following step produces outer None. EvalsToInTime.trans composes the same transition system and actual middle state. Those meanings match the source records and examples.

These components do not complete the verifier machine or the formal NP correspondence. Input and move parsers, rotations, equality, repeated streaming, binary/framing adapters, quantitative composition, and final output/cleanup retain their outstanding obligations. The future input-parser partial plan is explicitly unimplemented and unreviewed preparation, not evidence of a completed result.

## 5. Preservation and focused evidence

The relay bound all 22 actual C6c source bodies and modes to the candidate capture, Audit6 input map, and its before/after snapshots. Fourteen prior author owners match their secured C5b Audit5 descriptors. The old C5b Git object is unavailable after the reset, so this is a comparison to preserved exact descriptors, not a new direct C5b Git-object diff. The entrypoint adds exactly the three new imports to its preserved prior body. The six compiler, project and audit configuration files remain byte-identical to B.

Recovered normal builds actually completed successfully for the three new owners (1,346 jobs) and the selected prior client owners (1,349 jobs), with unchanged matching inputs. They are fresh recovered-environment builds, not reconstructed successful logs from before the reset.

Audit6 actually completed with exit0. It reports 2,841 kernel-safe declarations, 1,902 theorem declarations and 43 project modules, with zero unsafe declarations and the established axiom allowance of propext, Classical.choice and Quot.sound. The new module counts are core255/141, dispatcher179/88 and examples71/56, expressed as safe declarations/theorems. All 40 prior module counts are unchanged.

The entire 32,328-byte Audit5 source occurs byte-for-byte in Audit6 at offset179. Its census, source ownership, generated/private roots, safety checks and axiom allowance are preserved. The prior command-output tail also exactly matches the corresponding Audit6 prefix. That mechanical output comparison supports reuse of earlier evidence; it is not a claim of fresh reading of all inherited output. New commands comprise 217 checks, 78 prints and 27 syntheses. The explicit finite synthesis output covers the concrete control and every relevant alphabet position.

All 44 complete historical CTB new-ticket objects remain decoded-equal. All 681 old numeric/Boolean/null leaves remain unchanged; one new false qualification-change leaf gives 682 current leaves. Coverage's complete 129-leaf numeric/Boolean/null map is unchanged. The old seven component descriptions and six owner entries are exact prefixes of their expanded arrays. Historical receiving and qualification objects remain unchanged.

Chapter5 remains 92/94, with FDSA-5-92 and FDSA-5-93 open. Chapter9 remains 61/110, with FDSA-9-62 through FDSA-9-110 open. The current work-list replacement describes completed source-level stages and remaining validation/machine obligations without rewriting the canonical tickets. ST-001 concerns the inconsistent operative gates.

The C6c paper preserves the complete secured101 paper prefix and the earlier C5b paper prefix. The fully read fuel design, independent cases and future partial plan match their maintained paper copies after only the documented heading-depth transform. Historical failed attempts and the later successful recovery/build account remain distinct. Capture-time text saying the expanded audit was prepared but unrun is consistent with the capture preceding the later Audit6 execution.

## 6. Frozen102 operations and actual delivery

I read the complete frozen102 checkpoint_common.py, make_checkpoint.py, verify_packet_archive.py, verify_recovered_source.py and helper README, using their actual inventory-bound bodies. No later helper draft is substituted.

The helpers construct the full original-B delta, check source capture and live freeze, retain original adapter/restorer sources, require complete predecessor dispositions and matching build-progress evidence, and refuse existing output paths. Archive verification checks safe unique paths, ordinary file/directory modes, size and hash inventory, declared source payloads and the original prerequisite before fresh manual extraction. The 128 MiB limit is an archive payload guard, not a compiler resource limit.

Recovery inspection checks an ordinary public clone with its own Git storage, full history, original-B HEAD, exact reconstructed index tree and complete staged delta, all restored bodies/modes, and working-tree hygiene. It records the caller-supplied actual restorer exit and log, and separates recovery from Lean acceptance and durable upload. I found no actionable helper defect for the actual frozen102 use; I did not run additional helper tests.

The actual checkpoint102 archive has 2,534,264 bytes and SHA-256 `9721ea1244e1ba6591c9d7c2f759477b38073241b69be1a056c1f6cf5bc5e18b`. It contains 102 inventoried members plus INVENTORY.json, 22 source updates and no deletions, bound to the C6c tree. Archive verification passed. The actual fresh ordinary-clone restoration passed with public history of 2,424 commits and without the private C6c commit. Its complete command record and all 22 restored source descriptors were supplied. The actual upload record reports success for the same archive bytes.

These are separate established outcomes: archive integrity, source restoration, and durable delivery. None supplies the missing whole-library acceptance result. This round6 report was authored after checkpoint102 and is not a member of that frozen archive.

## 7. Prior review history and final disposition

The current and secured101 round5 Markdown and JSON reports match their preserved descriptors exactly. Standalone round1–4 Markdown/JSON report files are absent from the current evidence directory, secured101 evidence and its inventory. The common review record retains their reviewer identities, filenames, hashes, outcomes, brief scope and finding dispositions; it does not embed their complete bodies.

I therefore preserve those earlier conclusions only as recorded review history and do not claim a fresh body comparison of missing files or recreate their contents. The current review reuses unchanged guidance and the retained cumulative round5 assessment within its stated boundaries, while reading the new C6c material as specified above.

**Required next review:** supply an immutable candidate containing the acknowledged current-gate correction, preserve all prior requirements and findings, and return matching validation evidence through this same Standards axis. ST-001 is open against C6c; ST-V001 remains unresolved. The source assessment, focused successful evidence and secured recovery packet do not change the Blocked outcome.
