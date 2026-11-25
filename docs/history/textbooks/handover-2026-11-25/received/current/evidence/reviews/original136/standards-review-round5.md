# Standards review — round 5, same implementation review loop

**Outcome: Blocked. Full source/content and supplementary statement review are complete, with no source findings. ST-V001 remains unresolved because matching whole-candidate integrated acceptance evidence is missing.**

The same independent Standards axis, /root/parser_review/standards, reviewed the complete nineteen-path immutable candidate on 2026-11-21. This report preserves the earlier rounds and their findings; it neither opens another review loop nor substitutes for the independent Spec axis. The coordinator owns review-record.json. No receiving acceptance, publication authorization, FDSA-5-93 qualification, or complete verifier-machine/NP result follows from this report.

## Immutable inputs and full scope

| Input | Reviewed identity |
| --- | --- |
| Original base and merge base | bc95f503ccbf043136c6699992388f750270e8e6 |
| Candidate C5b | 92e40e2200511531d377def795f0a3038752dd7a |
| Tree | 44b75c9f8e05960b4f7cc3e523497698fbdd4599 |
| Previous reviewed candidate C4b | e2a0a0cd3d7be96362659d02a2e8a5631f61848e |
| Commit list | One synthetic commit: 92e40e22 Immutable scoped review snapshot |
| Full diff | git diff bc95f503ccbf043136c6699992388f750270e8e6...92e40e2200511531d377def795f0a3038752dd7a |
| Nonempty diff size | 19 files, 7,589 insertions and 306 deletions |
| Supported receipt | candidate-5b.json; status ok; whole mode; 9,665,468 bytes |
| Receipt SHA-256 | 2d2df8e1ac43731234acb7b6db6511b30de4ce39006d2f3a921cac909eea08ba |
| Scope identity | 267f2d073de9d88b4976c968274a850c0178af941f1f369261cdc277b4084b99 |
| Source/content identity | 9d9bf0e5601a12d96d43b2954107e4871330cbc6d2d913bf40119103f91ff554 |
| Projection identity | 392a9025ee47d574cfdca516e0e588a29194f85ad67c4a091b81b6494652479a |
| Source metadata | candidate-5b-metadata.json; SHA-256 7b96c924a4b3d82021c04b56914839b984d896776aa06b3977e9d2a510caaa29 |
| Full requirements | requirements-5.txt; 218,148 bytes; SHA-256 76f3a3bb9f00f92a125cc6fbca95e1ad72168ddac188627c70c7c9495635a5ab |

Evidence paths in this report are relative to /workspace/scratch/39407f75909a/continuation085. Candidate source paths refer to immutable objects in /workspace/scratch/39407f75909a/conaled. I used git show/git diff, supplied immutable evidence and the retained pinned API analysis, rather than reviewing mutable author source.

I independently verified the actual tree, original merge base, one-commit history, nonempty full comparison, receipt identity, scope, all nineteen immutable byte sizes and SHA-256 values, and recorded file modes. Manifest-5 has entries {} and exclude []; no task content is projected away. The receipt's outside-scope inventory is not an exclusion of requested changed files. The expanded baseline retains the original accepted base.

The full scope comprises:

| Family | Candidate paths |
| --- | --- |
| Stack and complete-input parsing | Applications/Resources/RotationCertificate/TreeParser.lean; InputParser.lean; Examples/RotationCertificateParsing.lean |
| Streaming, witnesses and word verifier | Applications/Resources/RotationCertificate/Streaming.lean; Witness.lean; Verifier.lean; Examples/RotationCertificateVerification.lean |
| Fixed four-bit codec and binary verifier | Applications/Resources/RotationCertificate/BitCodec.lean; BinaryVerifier.lean; Examples/RotationCertificateBinary.lean |
| Actual finite four-bit decoder machine | Applications/Resources/RotationCertificate/BitDecoderMachine.lean; Examples/RotationCertificateBitDecoderMachine.lean |
| New strict pair framing | Applications/Resources/RotationCertificate/BitPairFraming.lean; Examples/RotationCertificateBitPairFraming.lean |
| Public integration | SquareApplications.lean |
| Paper and maintained records | docs/research/fdsa-rotation-certificate-preparation.md; docs/textbooks/CTB.json; docs/textbooks/coverage.json; docs/textbooks/inbox/README.md |

Implementation filenames abbreviated within a family use its stated Applications/Resources/RotationCertificate directory. The structured report records all complete paths and current hashes.

All twelve prior Lean owners are byte-identical to C4b. I reused their earlier complete source assessments only after checking that equality, and checked the new consumers and preservation in this round. The requirements retain all 164,086 bytes of requirements-4.txt as an exact prefix; I read the complete 54,062-byte addition. Both raw preimplementation plans occur verbatim in the requirements: framing-draft/BitPairFraming.design.md, 34,003 bytes, SHA-256 002c5c5100283ab4f9de839285bac67f625b95c7e60589c56ab24082c8380ac0; and framing-draft/BitPairFramingCases.plan.md, 19,208 bytes, SHA-256 79d39ae64b1ff4e824a76962e1e03fb893e9518a978af4d5f46a300f3d8afd93. The case plan explicitly distinguishes independently fixed semantic expectations from transition counts derived with the supplied control outline. It does not pretend to be a blind acceptance review.

## Applicable standards and architecture

The applicable guidance remains AGENTS.md and its task-authority, domain/glossary, architectural-quality, formal-development and review-loop pointers; README/development acceptance policy; ADR 0001's module separation, ADR 0010's composition and exhaustive audit, and ADR 0006's arbitrary-tail principle; the code-review skill and heuristics; and example-driven-development's statement, counterexample, intermediate-form and connected-client requirements. These inputs are unchanged at C5b. I re-read the current review skill, architectural-quality guidance and statement-review guidance while retaining the earlier complete standards analysis.

This increment adds one concrete application of the pinned TM2 interface. It keeps the independent representation/parser, actual finite program, numerical observations, operational proofs and source verifier binding visibly separate. It does not define a parallel transition semantics or assume a generic cost interpreter. It uses the existing binary verifier and its independent BinaryYes language, Mathlib's actual step/reachability and timed-record interfaces, and ordinary public-result clients in Examples. The new public imports are two ordinary additions to SquareApplications.lean; earlier imports remain present.

The local configuration/extensionality and iterate-step helpers serve the concrete proof rather than introducing an unnecessary generic framework. The explicit branch cases in the potential argument correspond to operationally different changes in cells and phase credit. A concrete 800-line owner is reasonable for this cohesive parser, five-phase machine, complete execution and resource argument, with the 533-line connected owner kept separate. This is an architectural judgment based on the actual interfaces and consequences, not a file-length rule. No heuristic concern with a concrete adverse consequence warrants a source finding.

The earlier twelve owners retain their previously assessed semantics: actual arbitrary-frame/tail parsing, complete-input EOF rejection, decrement-before-parse streaming and actual reached-tree recursion, independent common-size/distance Yes language and attained-minimum witnesses, word/binary all-raw acceptance and work bounds, actual packed emitters, and the universal finite four-bit decoder machine with injective result encoding and reached-workspace proof. Source work is still distinguished from machine time. The new owner does not alter those definitions or tariffs, nor inherit their open whole-library acceptance.

## Independent representation and semantic statement review

The new core's lines 25–157 define and establish strict framing independently of the machine and verifier. Escape emits false followed by the actual first-coordinate bit. Frame appends one true flag and the complete second coordinate. Unframe examines flag positions: true returns the entire remaining suffix as certificate, false consumes a required payload, and either EOF before a delimiter or a lone false rejects. True in a payload position is ordinary data. This is not a search for any raw true bit and does not perform numeric normalization.

The success equivalence quantifies over every raw list and both returned coordinates: unframe raw = some (input, cert) iff raw = frame input cert. No well-formed-frame premise is needed on the raw direction. The failure iff classifies every malformed word as an escaped first coordinate or that escape followed by one false. The generalized escape-prefix law maps the actual suffix result; none stays none, so an arbitrarily long escaped prefix cannot repair a failed continuation. Frame injectivity recovers both coordinates.

The exact frame length is 2I+C+1. Frame append says that an arbitrary appended suffix extends the certificate; this representation is intentionally not prefix-free. There is no trailing-junk rejection at the framing layer. Later four-bit or rotation syntax belongs to the existing binary verifier. The source parser uses tail-first structural recursion but carries no claimed new source-work tariff; the machine's different operational order is connected by value correctness and separately proved actual transition counts.

Lines 159–188 specify resultCode none = [] and resultCode (some (input, cert)) = none :: (input.map some ++ none :: cert.map some). Its full Option-pair injectivity proof uses the absence of none from either mapped payload, the separator law, and injectivity of mapping some. It distinguishes failure, successful empty coordinates, false payloads, and boundary placement. Successful length is I+C+2. The paper correctly treats the initial marker as part of the chosen format; it does not falsely claim that both markers are individually necessary for injectivity.

The executable verifyFramed definition, lines 701–705, matches the actual unframe result. Failure returns false; success passes exactly its two returned fields, in order, to the Boolean projection of verifyBitsRun. Its raw iff does not substitute guessed coordinates. Trace acceptance uses the prior exact encoded legal-move result, soundness returns the independent BinaryYes predicate, and certificate existence uses the existing independent-language equivalence. The immutable Yes/BinaryYes definitions and their preceding assessments are unchanged; no execution-defined circular language was introduced.

## Actual finite machine, generalized phases and cost boundary

Lines 190–273 define four stack indices, five labels, Option Bool registers, Bool alphabets on input/firstReverse/certReverse and Option Bool on output. The source and elaborated output explicitly supply finiteness of every alphabet, not merely the input alphabet demanded by FinTM2. One fixed machine exists before the universal raw-input quantifier. There is no list-valued register, input-dependent program, preloaded parsed pair, source-recognizer callback or size/value oracle.

Store overwrites the register with the actual pop result. All getD uses follow a presence branch. Jump and finish reset the register. The five program bodies perform actual input pops, accumulator pushes, gotos, reversal emissions and cleanup. They never call unframe, verifyBitsRun, runSteps, reverse, length, value or a complete-list transformer. Proof-side reversal and lengths describe these executions rather than execute inside a callback. The longest scanner branch has bounded finite work within one TM2 label activation. The claimed clock is the pinned TM2.step count; no new theorem identifies it with Lean allocations, TM1 transitions or a complete verifier execution.

The thirteen step laws, lines 308–393, include every scanner shape, copy/emit/clear nonempty and empty case, and halt. They quantify over arbitrary incoming registers and every untouched stack. Their targets record reset registers and the actual preserved lists. In particular, cleanup neither silently erases a preexisting certificate-reverse stack nor overwrites an arbitrary old output.

The complete phase laws, lines 405–508, retain precisely the intermediate state each phase needs:

| Phase | Generalized inputs and target | Actual transitions |
| --- | --- | --- |
| emitFirst | Empty input and certReverse; arbitrary firstRev, output and registers; emits reversed firstRev before the old output and a leading marker | length(firstRev)+1 |
| clearFirst | Empty input and certReverse; arbitrary firstRev/output/registers; discards firstRev, preserves old output, resets and halts | length(firstRev)+1 |
| emitCert | Empty input; arbitrary both reverse accumulators, output and registers; emits both coordinates and both markers in order | length(certRev)+length(firstRev)+2 |
| copyCert | Arbitrary raw suffix, both reverse accumulators, output and registers; preserves old certificate prefix before the raw suffix | 2 length(raw)+length(certRev)+length(firstRev)+3 |
| scanPrefix | Arbitrary raw/firstRev/output/registers; certReverse explicitly empty; appends old output to the code of the actual parsed result with the reversed first accumulator prepended | runSteps(raw)+length(firstRev) |

The scan statement includes failed continuations and arbitrary old output. On failure its result is exactly the old output after clearing all accumulated first bits. It does not overgeneralize exact haltList to a nonempty unrelated certificate-reverse stack. The source derivations use the actual step equations and induction with open accumulator/register parameters; the small complete-run theorem is a specialization of that general proof.

The total result at lines 538–587 is present: next iterated runSteps raw times from literal initList machine raw equals some (haltList machine (resultCode (unframe raw))). Source rejection is represented by the empty output at an actual reset halted configuration. It is never implemented by the outer none obtained after stepping past halt.

| Raw form | Exact reached-halt count |
| --- | ---: |
| Frame with first/certificate lengths I,C | 2I+2C+4 |
| Escape of q first bits, missing delimiter | 2q+2 |
| The same escape followed by a lone false | 2q+2 |
| Arbitrary raw length N | At most 2N+2 |

These counts include delimiter/EOF handling, copies, real reversals, actual rejection cleanup, both markers, reset and halt. Certificate-only frames attain the universal bound. The declared runSteps recurrence is proof-side and absent from the program. The exact and bounded TM2OutputsInTime definitions construct records with machine_run as execution evidence and the proven numerical bound. The noncomputable polynomial record fixes this same machine and identity alphabet equivalences, uses polynomial 2X+2, and supplies outputsFun for every raw input. Noncomputability is confined to polynomial proof-data construction, not the executable program. The explicit injection laws close the representation gap that an arbitrary constant output encoding would leave.

## Reached workspace and same-witness composition

Lines 589–699 sum the lengths of all four actual stacks. Phase credit is one at scanPrefix/emitFirst, two at copyCert/emitCert, and zero at clearFirst/halt. Consuming the true delimiter pays for the increase from one to two credits; transferring cells preserves the sum; each marker consumes one credit; failed scans and cleanup cannot increase the potential.

Step monotonicity quantifies over arbitrary configurations c,d with actual machine.step c = some d. The proof includes all branch shapes and arbitrary unrelated stack contents; it does not assume a prevalidated input or only the intended successful path. Reaches monotonicity inducts over the actual reflexive-transitive transition relation. Literal initialization has potential N+1, yielding stackCells reached ≤ N+1 for every actually reached block-boundary configuration. A separate bound on each stack follows from that total. The claim does not concern every internal stepAux node or unproved physical storage overhead.

The connected empty-pair case constructs all four transitions from raw [true] to haltList [none, none] and derives real reachability. Its terminal two cells both meet N+1 and refute N. Thus the positive space client is inhabited and checks the claimed extra cell; it is not a theorem with an unexplained reachability premise.

The new completeness law, lines 753–798, obtains one actual accepted certificate from verifyBitsRun_complete_small. With C≤I², the exact frame length gives 2I+C+1≤(I+1)². The same certificate is used for accepted verifyFramed, constructed framing timed evidence bounded by 2(I+1)²+2, and every-reached configuration's cells bounded by (I+1)²+1. The connected client's quantifier order retains one certificate outside all these claims. It does not exchange witnesses between acceptance, time and space. The additional bound 40(frame length)² is explicitly the previous binary source-work observation; it is not added to actual framing steps or called a machine-time result for verifyFramed.

## Connected cases and proof-repair assessment

I read all 533 lines of Examples/RotationCertificateBitPairFraming.lean and checked the uses of public contracts. The fixed expectations remain connected to the general results rather than being replaced with private proof details or unrelated evaluations:

- Recognition and injectivity clients recover both coordinates and the complete optional result. The boundary separator distinguishes ([false],[]) from ([],[false]); failure differs from successful emptiness.
- Empty input, lone false, guarded false/true payloads, missing delimiter and incomplete guard use the general malformed families and actual run theorems. True as payload cannot become the delimiter. Every post-delimiter suffix is retained, including lone false and additional true bits.
- Nonpalindromic first/certificate examples preserve internal order and coordinate order. Appending arbitrary bits extends exactly the certificate. Same numeric values with different zero widths remain observably different.
- Initialization exposes the unchanged raw list and empty auxiliary stacks. Arbitrary stale registers cannot invent missing input. Four visible transitions for [false,true] show accumulation, failure detection, an actual clear pop and reset halt.
- General phase clients retain arbitrary old output and registers, plus nonempty reverse accumulators. The concrete leftover-certificate counterexample proves why a complete cleanup theorem cannot omit the empty unrelated-stack restriction.
- The four-step empty-pair path supplies actual reachability and the sharp workspace example. Present failure/success are distinguished before their later outer-none results. Arbitrary raw clients consume actual timed-record fields and the single constructed polynomial machine.
- Returned fields feed the existing verifier. An empty first coordinate is valid framing yet rejected for every certificate. General packed-emitter clients join actual emitted outputs, framing, unframing, source acceptance and actual framing-machine execution.
- The existing one-rotation emitters provide I=56 and C=8. Their frame has 121 bits, execution reaches the full 66-symbol result after 132 steps, and the source binary verifier returns (true,137). Appending either bit gives a valid 122-bit frame and 134 framing steps while the binary verifier returns (false,112) for the incomplete certificate. These are deliberately distinct observations.
- The complete-small client packages one accepted witness with length, framed length, constructed time data and universal reached-space claims. BinaryYes is concretely inhabited by the one-rotation input.

The retained repair diffs change proof scripts only: removing unnecessary remembered equations, using rfl in an already reduced none branch, exposing the actual iteration goal in outputsInTime_small, normalizing the empty first coordinate's zero contribution, removing an omega call after simp had closed the arithmetic goal, and reusing the normalized actual-run client. The semantic definitions, public conclusions, counts, bounds and independently fixed example values remain intact. Failed first/second client builds remain failed evidence for those exact earlier bodies; the matching final build is assessed separately.

## Supplementary audit: independently inspected actual output

FocusedAudit5 actually completed successfully on the C5b identities. I inspected focused-audit-result-5.json, focused-audit-inputs-5.json, the actual audit source and full new printed output, and checked the supplied author summary against that evidence. The root summary is evidence of the author's inspection, not a substitute for this independent axis.

| Evidence | Bytes / SHA-256 |
| --- | --- |
| FocusedAudit5.lean | 32,328 / 138bf48088cc6a64eafd9fe6645d7d3b735ba92206f8390b13730af36dcfebd6 |
| focused-audit-inputs-5.json | 16,277 / 3f37c58afac7f75af7ce16cf0090bfd9b61707f42223159e910d7974bce000af |
| focused-audit-result-5.json | 11,640 / c445b32c7a918979baabc725da10faf68b7b48601b60616e9d58bce0d79bf497 |
| focused-audit-5.log | 489,331 / e1920e6d95e4ebdeda15139966e2287f929e85aadf88950e8a4a63afce5f973c |
| focused-audit-summary-5.json | 7,669 / 0ea11447102f1747bcc058b38d18d2e03fd7498def883f1fa4daefe7b2aec17e |

The actual log reports 2,336 kernel-safe declarations and 1,617 theorems across 40 imported project modules, zero unsafe runtime declarations, and exactly propext, Classical.choice and Quot.sound in the transitive axiom union. All fourteen new owners are imported; they total 1,053 logical declarations and 746 theorems. The new framing core contributes 242/155 and its example owner 57/54. All thirty-eight prior module counts are unchanged.

The complete inherited printed output is exactly 214,364 bytes, SHA-256 5fde980fcd7f1a208fe395d0c2aa7288fac3cc7d32aa1d6cdd73c528dfe6c819, byte-identical to the previously inspected Audit4 output. That permits exact reuse of its 102 contracts, 27 definition prints and six finite syntheses. I independently read every line of the additional output, lines 3008–6724, covering 119 further contracts (71 core and 48 example checks), 30 definition prints and seven finite syntheses. For readability only six named namespace prefixes were shortened during display: the new core, its Examples namespace, Resources.RotationCertificate, Resources.BinaryCounter, Turing.TM2 and Turing.FinTM2. No binders, terms, conclusions or cases were removed; the original log preserves the unshortened text and Lean's own proof-argument elisions.

The elaborated types retain the intended raw universality, open registers/accumulators/outputs, explicit empty unrelated stacks, present exact halt, fixed machine, independent language, same selected witness and actual Reaches domains. The printed executable definitions show finite callbacks, the actual parser match and verifier-field binding. Constructed timed and polynomial bodies use the intended execution records. The synthesized instances cover stack indices, labels, registers and all four alphabets. I found no hidden coercion, implicit parameter, notation shadowing, circular premise or vacuous output encoding changing the intended claims.

The ProofAudit namespace is byte-identical to Audit4. Its only difference from the candidate's ProofAudit namespace is the scoped success message; the inventory, root selection, transitive axiom traversal and forbidden-axiom failure logic are unchanged. The expanded imports and extra print/check commands remain outside that logic. Before/after source maps and configuration maps are equal; the immutable nineteen-file source map matches the candidate. The audit uses the pinned native adapter and lake env lean -EhasSorry without extra resource caps, toolchain overrides or manual compiled-output injection. It is a successful imported-closure census and statement inspection, not exhaustive whole-library acceptance.

## Preservation and maintained records

I independently compared actual immutable JSON objects and source bytes, using preservation-round5.json as a checklist rather than treating it as approval. All forty-four complete new_tickets objects equal their original-base values. Canonical requirement owners, namespaces, source correspondence, authorized scope, current user override, historical catalogs and the other immutable CTB top-level objects remain unchanged. All six canonical history/obligation files listed by that record match B, C4b and C5b. Other local task objects are unchanged; CTB-78 changes only the documented navigation next_action.

Every preexisting numeric/Boolean/null leaf remains unchanged: all 681 original-base CTB leaves, all 682 C4b CTB leaves, and all 129 coverage leaves. Programme denominators and qualified/open progress are preserved. Chapter 5 remains 92/94 with FDSA-5-92 and FDSA-5-93 open. Historical receiving records still cover the accepted cumulative084 foundations; the current receiving-acceptance scope explicitly excludes the new cumulative author work, including framing. No current component result is counted as full source-row qualification.

Within C4b→C5b, CTB changes are confined to CTB-24's current work/navigation and the CTB-78 navigation mirror; coverage changes are current_work status/scope and qualification_basis current gate. The status text records successful matching focused builds while keeping exact candidate validation, original independent review and receiving acceptance open. The paper's preparation and implementation-draft language deliberately preserves historical stages and sends precise compiler/audit outcomes to matching delivery evidence. It does not retroactively call earlier failed snapshots successful.

The entire C4b paper is an exact prefix of the current 166,236-byte paper, SHA-256 fb72f51286711c1f5f1a7d60798265764de6a31b41f2dbc045e22259755863e5. Both fixed plans are present in full with only heading levels shifted; their raw forms are also present verbatim in requirements-5. I checked these transformations directly. The appended implementation map accurately describes the actual core, phase restrictions, marker potential, same-witness source connection and discriminating cases. The inbox changes only the FDSA-5-93 row to point to this retained paper and current scoped work. The complete verifier machine, represented-state invariants, quantitative composition and cleanup, and formal NP correspondence remain explicit open obligations; FDSA-5-92 and the broader programme are retained.

## Matching build evidence and unresolved required validation

| Check | Matching result and scope |
| --- | --- |
| Immutable full diff style | Independently ran git diff --check B...C5b: exit 0 |
| Framing core producer | framing-draft/bitpair-framing-producer-1.json and .log: exit 0, 1,339 jobs; core hash 62b4b6cb63c9711a0582798a736f342f5a850325be8deb1962e096d4f028fa49 |
| Connected framing build3 | framing-draft/bitpair-framing-examples-build-3.json and .log: exit 0, 1,347 jobs; example hash 871160b76b8c7842c7252516f207728e311a145e6219dd4e0582216c2e17a2e1; same core before/after |
| Expanded imported-closure audit and statements | Actual exit 0 with the source, counts, permitted axioms and independently inspected outputs above |
| Exact-candidate whole-library guarded validation and exhaustive audit | Required; not supplied; unresolved ST-V001 |
| Matching integrated acceptance receipt and final nonrepairing verification | Required; not supplied; unresolved ST-V001 |
| Supported final post-validation comparison | Required after those gates; not supplied; unresolved ST-V001 |

I independently matched the two successful build log hashes and exact source hashes. Producer log SHA-256 is fac34ac20d775ca71d4248920dcb7da6fb274137daf54ce9a6ee83939c2ac525; final example log SHA-256 is c96aba5bab6651ebd4e8962b0bff3664b68eaad6241bd5e5de88cd280652e245. They report successful normal builds. The pinned Mathlib module-system import warnings remain visible; the reports do not suppress them or turn prior proof failures into successes.

The old-base command is not a C5b validation. The supplied baseline-observation-current.json, 17,777 bytes, SHA-256 1922e642d6b005df5fec77869210cdb3ec11330bb1178e4432ec1a13d50c2d8a, records that root-owned session 41860 was still running at the 10:44:05 UTC observation with eight constituent Lean exit-137 failures. Cause is not established; the supplied excerpts do not diagnose a proof error, and root records no imposed caps. Those observations neither establish a C5b source defect nor a passing whole-library receipt. I did not interrupt, restart or change that workspace.

During report preparation the coordinator relayed a newer root observation at 11:05:32 UTC: a ninth old-base exit-137 event, in SquareKit.SmoothQuotientGeneratedBaseChange, with the original command still running and no established cause or source diagnostic. The updated observation is 20,181 bytes, SHA-256 2ec78bf372fb83b6878fad03db6411fe341a8bd38ce53f39618d8f004432854f. This operational update supersedes the failure count at the earlier timestamp; it does not change this source assessment or ST-V001. The earlier eight-failure description retains its explicit historical time and scope.

There is no new required prevalidation comparison for this round. Supported capture plus checked before/after audit identity evidence binds the source assessment. The required supported comparison is the final one after exact-candidate integrated validation and nonrepairing final verification. Its absence is part of the retained ST-V001, not a new finding or an invented additional gate.

### ST-V001 — Missing exact-candidate integrated acceptance evidence

- **Category and severity:** validation/evidence; blocking acceptance.
- **Disposition:** unresolved, first recorded in round 1 and reassessed in rounds 2–5. No source-finding ID is created for the same missing gate.
- **Location:** the C5b candidate/evidence set, current common validation state, and the missing full acceptance receipt/final verification/final comparison. Matching focused evidence is candidate-5b.json, candidate-5b-metadata.json, the framing producer/example records and FocusedAudit5 records described above.
- **Applicable rules:** README.md Build and audit; docs/development.md exact-input validation policy; docs/agents/formal-development.md; docs/agents/review-loop.md Validation of the candidate; code-review skill sections 3 and 5.
- **Evidence:** the full source and supplementary statement reviews are complete and clean, and focused producer/example/audit evidence matches. The exact nineteen-path candidate has no supplied successful integrated whole-library guarded check/exhaustive audit receipt, immediate nonrepairing final verification or supported post-validation comparison.
- **Concrete consequence:** complete public-entrypoint integration, whole-library policy/coverage and exhaustive whole-library axiom acceptance remain unestablished. Prior candidate review or selected-closure evidence cannot establish those broader gates for this expansion.
- **Remedy:** supply the successful isolated guarded whole-library check and exhaustive audit for this exact candidate, retain matching receipt and compiler/dependency identities, perform immediate nonrepairing final candidate verification and supported final post-validation comparison, then reassess ST-V001 in this same axis. Any source change requires recapture and reassessment of the complete scope against the same original base.

## Disposition and retained history

No source finding or new heuristic finding is raised. The complete source/content and supplementary statement assessment is concluded for C5b. Overall Standards remains **Blocked**, not Passed, because ST-V001 is unresolved. This conclusion does not determine the independent Spec outcome.

All eight earlier Standards report files remain byte-for-byte unchanged. Their exact hashes are recorded in the structured round 5 report. In particular, round 4 Markdown remains 58b8025dddd654e6abc31cec1ac38c0f2c84b23d160ac16131f7ac4d6be899fe and round 4 JSON remains 8df163bf3c6a4bc48ba3975c7ab03dc4401f63a0adf9a479b082fa7109f96bab. Previous failed snapshots and completed scoped reviews retain their original identities and dispositions.

I did not edit candidate source, switch checkouts, run heavy builds, modify the coordinator record, publish, contact external recipients or create a replacement reviewer. This report and its structured companion are the only round 5 deliverables owned by this axis.

**Final axis summary:** base bc95f503ccbf043136c6699992388f750270e8e6; candidate 92e40e2200511531d377def795f0a3038752dd7a; tree 44b75c9f8e05960b4f7cc3e523497698fbdd4599. Source findings: 0. Unresolved validation findings: 1, ST-V001. Worst issue: missing mandatory integrated acceptance evidence. Standards outcome: **Blocked**.
