# Standards review, round 7 — C7c

Authored UTC: 2026-11-22T00:33:11.760771+00:00

## Outcome

**Blocked.** The same original Standards axis, /root/parser_review/standards, has completed its round 7 assessment of the reading scope described below. I found **no new Lean-source, contract, documentation, or checkpoint-helper defect** in that material. **ST-001 is fixed with independent review evidence for C7c. ST-V001 remains unresolved and blocking.** No source acceptance, receiving acceptance, qualification change, complete verifier, NP result, or whole-book completion is asserted.

This continues the original review loop and original public base. The material bridge supplied source and evidence, not review conclusions. The judgments and these report bodies are authored by the original Standards reviewer. I did not modify source, the common review record, another axis's report, compiler inputs, dependencies, or any active validation workspace.

| Identity | Exact value |
| --- | --- |
| Original public base B | bc95f503ccbf043136c6699992388f750270e8e6 |
| B tree | 3cf266b2a1fa38f13159692fd9ef43fbccaf9009 |
| Reviewed candidate C7c | 8c1ae22f3c29da427786e457cb3d42154584d7da |
| C7c tree | 743351811890c0a8f2bef4246d8a8770d3248643 |
| Requirements7 | 383,575 bytes; SHA-256 7e65db3e85cb867b3fd8cc4c681bb48a9662b821042723a4d294cd8836e1657b |
| Scope | All 24 original-B changed paths: 19 author Lean owners, the aggregate entrypoint, and four documentation owners |
| Manifest | manifest-7.json; entries empty; exclude empty |

All source references in this report mean the immutable C7c Git blob, unless another candidate is explicitly identified. Evidence filenames refer to /workspace/scratch/39407f75909a/continuation085. The complete source payload in conaled-textbooks-105-progress-2026-11-21 was independently compared with C7c. Later prospective 26-path Input work is outside this assessment.

## Stable findings

### ST-001 — fixed in C7c; historical C6c finding retained

The previous C6c report correctly identified operative gates prescribing a nineteen-path candidate and a twelve-owner pair-framing stage, although C6c already contained 22 paths and 17 author owners. I directly read all four operative strings from C7c, including the additional top-level continuation gate, and checked their decoded equality.

| C7c location | JSON pointer |
| --- | --- |
| docs/textbooks/CTB.json, line 236 | /local_state/CTB-78/next_action |
| docs/textbooks/CTB.json, line 1564 | /local_state/CTB-24/next_implementation_gate |
| docs/textbooks/CTB.json, line 2114 | /next_ticket_gate |
| docs/textbooks/coverage.json, line 920 | /qualification_basis/current_gate |

They now require the complete current 24-path original-B candidate, all 19 author Lean owners, the cumulative paper, guarded whole-library build and exhaustive audit, immediate nonrepairing final verification, supported post-validation comparison, and both original review axes. They accurately identify the tree-prefix producer and client as compiled while leaving complete input parsing and subsequent verifier, quantitative, NP, and canonical obligations open.

The actual Git delta and source-owner array support those counts. The correction therefore resolves the concrete narrowing/stage defect for C7c. This does not rewrite the immutable C6c report or grant C6c a later correction. Historical attempt paragraphs and prior acceptance records retain their original scope.

### ST-V001 — unresolved, blocking

The required passing exact-candidate whole-library validation and exhaustive audit receipt, immediate final nonrepairing verification, and supported post-validation comparison have not been supplied for C7c. Focused producer/client builds, Audit7, source review, archive verification, and recovery do not discharge those requirements.

The later evidence records an ordinary C7c whole check started at 2026-11-22 00:10:36 UTC in the separately owned acceptance-7 checkout. The command is the unchanged native adapter running ./check.sh --candidate 8c1ae22f3c29da427786e457cb3d42154584d7da. The checkpoint106 observation records an in-progress check. I read its start, workspace, status, and dated observation records; none is a completed result or passing receipt. This report does not infer a final outcome from a start record.

The historical C6c session 13287 became unavailable. Its 23:59 observation and subsequent 00:06 clarification retain a null actual outer exit, no receipt, and four observed constituent exit137 results. The cause remains unknown. The clarification correctly limits the process listing to one exec PID namespace; it does not establish that another namespace has no surviving writer. I neither inspected nor mutated the old acceptance checkout. The older C5b whole-check outcome also remains unknown after the reset.

The remedy remains the existing matching validation sequence and reassessment through this same loop. No extra prevalidation comparison gate is introduced. A later completed check must be recorded as later evidence, not silently substituted into this report. A changed source candidate needs its own matching assessment. The remaining full-verifier and canonical mathematics are separate substantive obligations and remain open even if this component eventually clears validation.

## Reading method and limits

This round began with the same review context and an unavailable direct executor. /root/verify_seed provided read-only, immutable material. I read and acknowledged the complete requirements7 suffix, both complete new Lean sources, and the requested TreeParser source-frame excerpt through that bridge. When a bounded direct immutable read succeeded, I stopped bulk transcription and completed the remaining inspection directly.

The frozen checkpoint106 bridge record preserves the earlier acknowledgment boundary; the later handoff records both source EOF acknowledgments and the restored access. I checked both artifact hashes. They are provenance records, not independent acceptance reports:

- standards-material-bridge-7-progress-checkpoint106.json: 19,929 bytes; SHA-256 12da817546eb2dbb7d2a6ea7d426a884bbad1d5305aea34014adf58a90fb8f09.
- standards-material-bridge-7.json: 12,605 bytes; SHA-256 43fa77c74a66113e1c4b333ddd58ddef798adf88c2bb5b7c0a883f33aaca4955.

### Complete new source and specification reading

I read TreeParserMachine.lean through line 1387/EOF, all 69,147 bytes identified by SHA-256 f24080d3817c3fdca2b93222348ee38f30e318f9830e908b1e61c37a87fbe92c, and Examples/RotationCertificateTreeParserMachine.lean through line 1170/EOF, all 64,635 bytes identified by SHA-256 7699dcb50d7187b1177dbb9356b90a06586ac1daae602333b136254e8598c664. Direct Git comparisons subsequently bound these actual bodies to C7c and Audit7.

The complete new requirements7 suffix is bytes [312060,383575), lines 5511–6753. It contains the full 40,104-byte represented tree/input plan, 23,774-byte independent tree-case plan, and 5,507-byte quantitative TM2-to-TM1 future plan. I independently verified their exact raw copies in requirements7 and their paper copies after only the stated heading-depth change.

I read every distinct C7c paper addition, including the complete 15,718-byte future complete-input case plan, and all changed CTB/coverage values and the full inbox/entrypoint diff. The three repeated plan copies were assessed through the complete raw requirements bodies plus exact mechanical paper comparison. The earlier 264,302-byte C6c paper is an exact preserved prefix, not a fresh whole-paper rereading.

The bridge corrected one manually introduced typo in the requirements relay: the actual workspace formula is 2*0+0+0+1 = 1. I read and accepted that correction. The original artifact bytes were unchanged. Relay hashes bind the tool-read artifacts; they are not a cryptographic verification of the rendered conversation text.

The supporting TreeParser excerpt, lines 1–120, includes the requested TreeFrame, stackPrefix, resumeTreeRun, parseTreeLoop, and resumeTreeRun_prefix definitions completely. Its last unrelated private helper continues beyond that excerpt. After access restoration I directly read pinned Mathlib Computable.lean lines 30–123 at revision 56a005855ea17e0b0958f73ec801ae140b0a1679 and compared installed bytes with that Git blob. The whole-file SHA-256 is 5ef637a9dd8791282f1770344cd7d80d5c196726c7ba435390a1c0f4a5ce1eae. This establishes the actual FinTM2, step, initList, and haltList boundary used here.

### Complete new elaborated-output reading

I directly read every new Audit7 command and its actual saved output: **211 public type checks, 76 definition/inductive prints, and 20 finite-instance syntheses**. The types cover all 126 public producer declarations and all 85 public client declarations. The original output range is lines 12984–20598/EOF, bytes [953075,1527555), 574,480 bytes, SHA-256 c2ce21ef87da71957aa1fee6404ddffa39b619fdb87613bf4987ba853914a3fe.

The complete range was read in 19 contiguous bounded chunks, with no omitted line. The structured report records each original line/byte range and hash. For display only I used reversible literal aliases P., Ex7., TM., ST., and RC. for the exact namespaces listed in the JSON. Each alias was absent from the original full log, the full log hash was checked, and reversing the transformation recovered each original chunk exactly. This was my direct reading, not a bridge relay and not new elaboration. Lean's own pretty-printer proof elisions remain elisions; I do not claim to have expanded them or every generated auxiliary body.

I separately read the actual audit header and all 45 module-count rows. The entire prior 58,429-byte Audit6 source occurs exactly inside Audit7 at [121,58550), and the entire prior 946,982-byte command output is exactly preserved at Audit7 log [6093,953075). Those comparisons preserve prior evidence; they do not convert previously unread historical output into fresh reading.

In particular, the round6 limitations remain: historical Audit6 standalone client-type ranges 9148–10335 and 10401–11407 were not read in that round. Round7 does not claim to have reread those old ranges. The old C5b object limitation and rounds1–4 report-body availability limitation also remain. The old round6 relay corrections are retained in that report.

### Direct evidence inspection and execution boundary

I read the matching successful build records and complete logs, the audit input/result/summary records, candidate/baseline metadata and capture result, changed documentation, fixed-plan preservation records, frozen helper differences, checkpoint105 archive/recovery/save/upload records, and the actual restoration log. I compared actual Git blobs, bytes, modes, hashes, JSON values, requirement prefixes, and archive members. I ran the reviewed frozen archive/directory inspector read-only; I did not extract or restore a new clone, run Lean, execute another audit, or start, stop, repair, or cap any build.

One grouped read-only check stopped at an absent standalone requirements.txt. A subsequent successful check verified all six earlier requirement prefixes against their recorded lengths/hashes and actual requirements6 bytes. Standalone requirements1–5 files are absent in the current continuation directory; their complete contents remain preserved as exact prefixes. This is a precise comparison boundary, not an assertion that absent standalone bodies were freshly read.

Repository guidance read for this continuation, including task authority, formal development, architectural quality, external continuation, and the review loop, is byte-identical between B and C7c. Visible review context and current immutable sources were sufficient; no external conversation retrieval was used.

## Independent source and contract assessment

### Finite representation and actual operations

The new producer uses one destination-indexed core. Its five phases, live success/failure labels, stack sum, finite temporaries, and caller parameters are actual maintained definitions. Raw, reverse, and each output have Tag alphabet; pending has Unit alphabet; each protected stack retains its own alphabet. The concrete client checks 7 stack indices, 15 labels, and 68 register values.

The actual FinTM2 structure only demands finiteness of its designated input alphabet. The new module independently supplies alphabetFintype for every stack, and the concrete syntheses exercise the dependent alphabets and finite stack/control/register types. Generic semantic lemmas use only the equality assumptions they need; the finite specialization supplies the additional finiteness assumptions. The program and caller are fixed before arbitrary input words, outputs, registers, and protected lists.

Runtime blocks inspect finite registers populated by actual peek/pop operations. The pending-empty branch follows an actual pop and peek. Transfers use the actual popped tag. Every unbounded repetition is a goto. Source trees, frames, lengths, parser results, OpenPrefix evidence, ranks, and endpoint descriptions remain proof-side objects; I found no unbounded semantic parser or list traversal hidden in a runtime callback.

### Literal endpoints and source correspondence

Ordinary entry requires empty reverse and pending stacks while allowing arbitrary old outputs, protected stores, caller state, and stale owned temporaries. Success consumes exactly the first tree prefix, retains the literal unread suffix on raw, and prepends the accepted code to only the selected physical output. Failure restores the entire original raw word and every output. Both ordinary endpoints clear scratch and reset only the owned temporary fields.

The generalized emit, undo, and dropPending lemmas retain arbitrary accumulator and tail material. General emit correctly leaves pending unchanged; the ordinary success theorem obtains empty pending from its reachable representation invariant. Partial-transfer theorems distinguish zero steps, all transfers, and the later empty probe.

The source connection represents actual stackPrefix frames in reverse and exactly 1+leftSlots frames Unit tokens. The induction follows the actual parseTreeLoop and resumeTreeRun results, with prefix and slot relations supplying the emitted complete code. Compression to a slot count does not erase the serialized shape: the reverse stack retains it. The mixed-frame and nonpalindromic clients exercise this distinction.

The all-raw run_source theorem uses the actual parseTreeRun result and produces the exact source-connected live configuration. FirstSuccess is defined at the exact first-return time, with iff results for the actual source parse and literal raw=treeCode++suffix. It is not arbitrary eventual reachability. The finite machine and initList theorem use the same installed blocks and actual stack initialization; no haltList result is asserted from a live handoff.

### Timing, reached space, and caller boundaries

The proved successful count remains 2*L+2=4*n+4. Independent OpenPrefix/Blocked evidence characterizes every failed raw word and gives the exact 2*k+p+4 count, including the rejection probe, rollback, both empty probes, and all pending-token removals. The unconditional bound is 3*M+5. These are actual TM2 transitions, distinct from source-event work.

Every owned configuration, including corrupted scratch states, has derived one-step progress and exact rank decrease. The actual prefix theorem exhibits a reached configuration and an owned-step path. No termination premise is assumed. The source theorem still requires its stronger representation invariant; rank/progress on arbitrary states does not silently grant source correctness.

The space potential sums every actual stack cell, including all old outputs and protected lists, plus phase credit. Local owned transitions make it nonincreasing. The inclusive first-handoff bound is 2*M+O+U+1. The all-N family exhibits the actual configuration after M+1 steps and attains that bound, including M=0. This is an executed sharp witness, not an assumed reachable-state predicate.

The Type-valued exact and linear EvalsToInTime records are constructed from actual iterate equalities. The sentinel example separately proves live return at 4, actual push and inner halt at 5, and outer none at 6. A fixed allocating caller exceeds the component's space bound after handoff. A fixed misleading caller manufactures a later success and reenters the core after a genuine first failure. These examples justify the prefix-only preservation, workspace, and recognition boundaries.

Two destinations execute under one installed program. The second call starts from the actual successor of the first return, including the counted one-step reset/goto. Both timed records are composed through the literal shared configurations. The exact count is 2*Ls+2*Lt+5, with the 17-step leftTwo/nil client. Its every-prefix space proof counts the first emitted code as old output for the second call and is restricted to this nonallocating caller.

### Connected cases and architecture

The complete client preserves the independently fixed ordinary cases, arbitrary blocked tails, two distinct old outputs, stale temporaries, nonempty and mixed ghost frames, all six invalid-entry executions, generic transfer domains, all-N sharpness, actual caller counterexamples, genuine timed composition, and emitter connections. Empty/foreign failures take 5, nil success 4, singleton success 8, two-node success 12; the incomplete N/NE/NN/NNE cases retain 8/9/11/12.

The source and machine clocks remain separate. For example, nil source work is 3 versus 4 machine steps, and a large preexisting needRight prefix still takes physical transfer time although source resumption has a fixed tariff. The actual emitted rotation input supplies the first tree call's word: that tree call takes 12, while the existing full source parser observes 46. The future full-input machine's proposed 31 is not claimed as an execution of this tree-only component.

The core reuses the existing parser representation and generic ranked-prefix facts without changing prior owners. Its finite destination parameter supports genuine reuse on the same raw/scratch stores; the connected second-destination execution demonstrates that use. No new general parser framework or free physical data relocation is assumed. I found no weakened fixed expectation, dummy success premise, unsafe runtime bypass, or replacement of an actual timed record by budget arithmetic in the inspected material.

## Cumulative preservation and documentation

Direct original-B Git comparison has exactly the manifest's 24 changed paths, no deletion, and no out-of-scope source delta. C7c is one supported immutable snapshot parented to B; the merge base is B. The receipt's large excluded inventory denotes paths outside task scope and is distinct from manifest.exclude, which is empty.

All 17 earlier author Lean owners are byte-identical between C6c and C7c. The entrypoint adds exactly the two new imports. All six audit configuration files are byte-identical between B and C7c and match the audit's before/after bindings. Every one of the 24 C7c source blobs, lengths, and modes matches Audit7's input descriptors and before/after hashes.

The C6c-to-C7c CTB changes comprise nine paths; coverage changes comprise two. I read every distinct new value, the full new parser preparation object, and all four gates. The coverage status is exactly the current author-increment status. The append-only paper history distinguishes initial failed attempts, the compiled initial slice, and the complete producer/client success. Statements that Audit7 was next in the captured documents retain their pre-audit observation boundary; the later actual audit result is separate evidence.

All 44 complete new_ticket objects are decoded-equal to B and C6c. Every original CTB numeric/Boolean/null leaf is preserved: 681 from B, with the already existing additional false qualification leaf giving 682 at C6c and C7c. The complete C6c/C7c maps are equal. Coverage's 129 such leaves are unchanged. The original seven component entries and six owner entries remain exact prefixes. Historical receiving/qualification data are unchanged outside the specifically inspected current-work updates.

The entire C6c paper is retained as a prefix. Requirements7 retains all 312,060 actual requirements6 bytes; each earlier recorded complete-prefix hash also matches. All three fixed plan copies match exactly after heading-depth normalization. The future Input case plan is preserved at paper bytes [341470,357208), after the same heading-only transformation; its raw SHA-256 is c93165730c7b27bf3743990ea2e4eb11bf5fe4cfe1c6d5d00aee1f34fa0a4ef9.

I read that entire future plan and its separate mathematical-check report. The finite label/stack/register arithmetic, sequential failure partition, rollback orientation, dirty-accumulator assumptions, high-zero preservation, first-full-handoff ownership, and cost-model distinction are retained. Its bounded Python model is supplementary nonformal evidence; I did not execute or freshly audit that model. Neither future Input owner exists in C7c. The plan requires later scope/requirements release and actual Lean source, proofs, builds, and review. The quantitative simulation plan likewise remains a future theorem obligation, including finite support, initialization/encoding, actual timed simulation, and output cleanup.

Chapter 5 remains 92/94, with FDSA-5-92 and FDSA-5-93 open; Chapter 9 remains 61/110, with FDSA-9-62 through FDSA-9-110 open. Complete input/move parsing, represented rotations and equality, repeated streaming, eager binary/framing adapters, final output/cleanup, quantitative composition, and formal NP correspondence are not supplied by this component. No canonical denominator or qualification was advanced.

## Matching focused evidence

Producer build12 and client build6 completed normally through the unchanged native adapter. The complete logs report 1,287 and 1,337 jobs respectively. Producer12's before/after source hash is f24080d3…; client6 binds the full 24-input snapshot unchanged during that command and includes the 7699dcb5… client. I directly compared every Lean input, including the entrypoint, with C7c.

The four documentation files changed after client6. That boundary is explicit in the audit inputs and in this report: the focused build does not certify those later documentation bytes. Audit7 then binds all 24 final C7c paths and six unchanged configuration files. Before/after identity checks are evidence of observed input stability, not proof against transient edits or a replacement for isolated whole validation.

Audit7's actual exit is 0. Its actual header reports 3,400 kernel-safe declarations, 2,264 theorem declarations, 45 project modules, zero unsafe declarations, and only propext, Classical.choice, and Quot.sound in the transitive axiom union. The new producer contributes 428 safe/272 theorem declarations; the new client contributes 131/90. Generated and private declarations explain why module totals exceed the 126/85 public declaration counts.

The audit source is 82,898 bytes, SHA-256 4501c6a1b539162cd891c26077294d2a1f7318e949f5863666502f1dba858f88. The actual log is 1,527,555 bytes, SHA-256 773a869ac7fa9e71863742eceb78f64f30009387a1fae7692f8a6ac56f9ff600. Input and result hashes are recorded in the structured companion. No extra resource cap or manual olean injection is reported or introduced by this review. This remains an imported-closure audit, not the mandatory whole-library exhaustive audit.

## Operational sources and checkpoint105

I compared the five frozen105 helper sources with the fully read frozen102 versions and verified all five against both actual packet inventories. checkpoint_common.py, verify_packet_archive.py, and verify_recovered_source.py are unchanged. Only make_checkpoint.py and its README change.

The builder now accepts an explicit manifest, requires exact decoded agreement with the supported receipt, retains every previous scoped owner, forbids exclusions/projected entries, preserves the complete previous requirements as a prefix, and requires the current manifest in the payload. The complete original-B source-delta, body/mode/hash, disposition, progress, archive, and restoration boundaries remain. I read every changed helper line and found no new helper defect. The seven original native operational files, bundled restorer, and START.md are byte-identical between frozen102 and frozen105. I did not substitute later mutable helpers.

Checkpoint105 is the exact C7c source tree with 24 updates and zero deletions. I independently ran the reviewed archive/directory inspection read-only, checked the actual archive identity and every inventoried file, and compared all source payload bytes with C7c. It has 266 inventoried members, 267 regular members including INVENTORY.json, 72,541,905 selected payload bytes and 72,591,511 total regular bytes, within the 128 MiB limit.

| Checkpoint105 item | Exact identity / evidence |
| --- | --- |
| Archive | 7,973,464 bytes; SHA-256 ecce3fadb9b97ffd6517de99fd41c0a82daccf16cfc96a5a89b95aa6920c962a |
| Inventory | 49,606 bytes; SHA-256 cbfb71d5f715a77bef3d964da2d915c567e581d709a51b4902136cc870cc2852 |
| Recorded fresh restoration | Passed; actual restorer exit0; ordinary full-history public clone; original-B HEAD; exact reconstructed C7c tree; no private author commit required |
| Recorded save/upload | Succeeded; exact matching archive; library_file_id libfile_fde3_f-1385ae6840248191943465b7cb9a4a26_bcb09d6951dc8191bbb29f2ba3c27d9d |
| Source acceptance | False |

I read all recovery verification command results and the actual restoration log, including the source-tree result. This is inspection of recorded fresh restoration plus a new read-only archive/payload comparison, not a new clone restoration by this reviewer. Upload evidence is separately recorded; archive checking does not imply upload or Lean acceptance.

Round5 and round6 Markdown/JSON reports are byte- and mode-equal between the current continuation and frozen105 and match its inventory. Standalone rounds1–4 report bodies remain absent in both locations. Their previously retained metadata, outcomes, scopes, and dispositions do not constitute full report bodies. I have not recreated them or claimed a fresh comparison of missing bodies. The round6 report's historical reading limits and Blocked result remain intact.

## Disposition for the coordinator

Carry ST-001 forward as fixed with C7c-specific review evidence and keep its C6c history unchanged. Carry ST-V001 as the sole unresolved Standards finding for this assessed candidate. The content assessment supplies no acceptance waiver and does not resolve the remaining full-programme mathematics.

Preserve this self-authored Markdown and its structured companion with the next checkpoint. This report was completed after checkpoint105 and is not retroactively a member of that archive. Any later validation result or source change must be associated with its actual candidate and reviewed through the same original loop.
