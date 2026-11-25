# Spec review — round 5

**Outcome: Blocked.** The complete nineteen-path source/content assessment and matching focused-audit statement review are finished with **zero source findings**. **SP-V001** remains unresolved because the exact candidate still lacks the required integrated validation, matching acceptance receipt, final nonrepairing verification and final post-validation comparison. Matching focused compilation and the actual selected-closure audit support the component results described below; they do not discharge the whole-library gate.

This is the same independent Spec axis, `/root/parser_review/spec`, in the existing implementation review loop. The fixed original base, all earlier reports and all historical dispositions are retained. No source changes are requested. This report does not advance an accepted prerequisite, qualify a textbook row or authorize receiving publication.

## Candidate, scope and requirements

| Input | Identity |
| --- | --- |
| Repository | `/workspace/scratch/39407f75909a/conaled` |
| Fixed original base and merge base | `bc95f503ccbf043136c6699992388f750270e8e6` |
| Review-ready round-5 candidate, C5b | `92e40e2200511531d377def795f0a3038752dd7a` |
| Candidate tree | `44b75c9f8e05960b4f7cc3e523497698fbdd4599` |
| Commit | `92e40e22` — Immutable scoped review snapshot |
| Complete diff | `git diff bc95f503ccbf043136c6699992388f750270e8e6...92e40e2200511531d377def795f0a3038752dd7a` |
| Prior reviewed candidate, C4b | `e2a0a0cd3d7be96362659d02a2e8a5631f61848e` |
| Complete requirements | `requirements-5.txt`; 218,148 bytes |
| Requirements SHA-256 | `76f3a3bb9f00f92a125cc6fbca95e1ad72168ddac188627c70c7c9495635a5ab` |
| Supported full receipt | `candidate-5b.json`; status `ok`; 9,665,468 bytes |
| Receipt SHA-256 | `2d2df8e1ac43731234acb7b6db6511b30de4ce39006d2f3a921cac909eea08ba` |
| Scope identity | `267f2d073de9d88b4976c968274a850c0178af941f1f369261cdc277b4084b99` |
| Source/content identity | `9d9bf0e5601a12d96d43b2954107e4871330cbc6d2d913bf40119103f91ff554` |
| Projection identity | `392a9025ee47d574cfdca516e0e588a29194f85ad67c4a091b81b6494652479a` |

Evidence filenames below are relative to `/workspace/scratch/39407f75909a/continuation085`. Repository-relative source references designate the immutable C5b body. The companion JSON supplies every scoped source size/hash, all actual audited declaration names and the evidence descriptors.

I independently matched all nineteen immutable bodies to `candidate-5b-metadata.json`, checked the changed-path set, tree and merge base, and checked the relevant evidence hashes. The full base-to-C5b diff contains nineteen paths, 7,589 insertions and 306 deletions. C4b-to-C5b changes seven paths: two new Lean owners, the public entrypoint, paper, CTB, coverage and inbox. The previous twelve Lean implementation/example owners are byte-for-byte identical to C4b; only that identical content reuses earlier analysis. No review approval transfers automatically to the expansion.

The entire 164,086-byte round-4 requirements file is an exact prefix of the 218,148-byte round-5 file. I read all 1,143 added lines, including the fixed preimplementation design and independent distinguishing cases. Earlier rounds read the complete preceding prefixes: 88,675 original bytes, 106,818 round-2 bytes, 128,670 round-3 bytes and 164,086 round-4 bytes. The fixed framing design has SHA-256 `002c5c5100283ab4f9de839285bac67f625b95c7e60589c56ab24082c8380ac0`; the fixed cases have SHA-256 `79d39ae64b1ff4e824a76962e1e03fb893e9518a978af4d5f46a300f3d8afd93`. Requirements were preserved, including their original programme and acceptance obligations.

`baseline-5.json` and `scope-extension-5.json` retain the original base; they do not record accepted-base advancement. `manifest-5.json` contains all nineteen paths, `entries = {}` and `exclude = []`. No supplied task content is projected away or excluded.

| Scoped owner | Review treatment |
| --- | --- |
| `Applications/Resources/RotationCertificate/TreeParser.lean` | Identical to earlier reviewed body |
| `Applications/Resources/RotationCertificate/InputParser.lean` | Identical |
| `Examples/RotationCertificateParsing.lean` | Identical |
| `Applications/Resources/RotationCertificate/Streaming.lean` | Identical |
| `Applications/Resources/RotationCertificate/Witness.lean` | Identical |
| `Applications/Resources/RotationCertificate/Verifier.lean` | Identical |
| `Examples/RotationCertificateVerification.lean` | Identical |
| `Applications/Resources/RotationCertificate/BitCodec.lean` | Identical |
| `Applications/Resources/RotationCertificate/BinaryVerifier.lean` | Identical |
| `Examples/RotationCertificateBinary.lean` | Identical |
| `Applications/Resources/RotationCertificate/BitDecoderMachine.lean` | Identical |
| `Examples/RotationCertificateBitDecoderMachine.lean` | Identical |
| `Applications/Resources/RotationCertificate/BitPairFraming.lean` | New; all 800 lines reviewed |
| `Examples/RotationCertificateBitPairFraming.lean` | New; all 533 lines reviewed |
| `SquareApplications.lean` | Changed public imports reviewed |
| `docs/research/fdsa-rotation-certificate-preparation.md` | Entire prior paper retained; fixed plans and current claims checked |
| `docs/textbooks/CTB.json` | Protected objects and current changes independently checked |
| `docs/textbooks/coverage.json` | Protected values and current changes independently checked |
| `docs/textbooks/inbox/README.md` | Changed current navigation/status reviewed |

The applicable AGENTS, task-authority, domain, architecture, formal-development, review-loop, code-review and example-driven statement-review guidance remains unchanged. I also read ADR-0006 and the relevant language-direction criteria for reified computations, mathematical models, resource observations, library clients and compiler obligations. The review applied independent-statement, actual-definition, quantifier/domain, vacuity, intermediate-state and connected-counterexample checks. I used immutable `git show`/`git diff` and read-only evidence inspection. I did not edit source, switch a checkout, run a heavy build, publish or mutate `review-record.json`.

## Findings and historical dispositions

### SP-V001 — Exact expanded candidate lacks required integrated validation

- **Class/severity:** Validation blocker; blocking acceptance.
- **Status:** Unresolved; carried from round 1, reassessed for C5b in round 5.
- **Location:** The integrated acceptance gate for candidate `92e40e2200511531d377def795f0a3038752dd7a`, tree `44b75c9f8e05960b4f7cc3e523497698fbdd4599`, including the complete public entrypoint and exhaustive project audit.
- **Requirement:** The complete saved requirements, README Build and audit, development guidance and review-loop candidate validation require matching isolated whole-library source-policy/build/exhaustive-audit evidence, its acceptance receipt, final nonrepairing candidate verification and supported final comparison after validation. Required missing validation prevents a Passed outcome.
- **Evidence:** The new core passed an ordinary 1,339-job focused build at its immutable hash; its connected examples passed an ordinary 1,347-job focused build at their immutable hash. Actual Audit5 passed over forty imported project modules, including all fourteen new owners. This axis inspected the 119 added elaborated contracts, thirty added definition prints and seven added finite syntheses, and checked byte identity of the inherited actual output. These are selected-closure results. No successful exact-C5b integrated gate, matching acceptance receipt, final nonrepairing verification or final post-validation comparison has been supplied.
- **Consequence:** Overall Spec remains **Blocked**, although source assessment is complete with no source findings. Whole-library/public-entrypoint acceptance and accepted-base advancement remain unestablished. A checkpoint, capture, source freeze, focused pass, historical receiving result or old-base run does not establish that missing result.
- **Remedy:** Supply successful isolated integrated validation for this exact candidate, matching receipt and stable compiler/dependency/environment inputs, then final nonrepairing verification and the supported final post-validation comparison. Reassess this same finding on this same axis. Source changes require a new immutable candidate against the same original base.

No separate round-5 prevalidation comparison is required, planned or treated as a missing gate. The supported capture and verified before/after audit identities bind the reviewed source. The required comparison is the final comparison after integrated validation and final verification.

There are **zero source findings**, **one unresolved validation finding**, and **no source changes requested**. No source finding `SP-001` has been allocated. The worst issue remains `SP-V001`.

| Round | Candidate | Source findings | SP-V001 | Overall |
| --- | --- | ---: | --- | --- |
| 1 | `282443e16474bfce14e9b5ab6eabb265a87b84ed` | 0 | Unresolved | Blocked |
| 2 | `e395b3a802d8baedb6fa46f59c1e1addb3b90d55` | 0 | Unresolved | Blocked |
| 3 | `8270f74ca87c0ed1dbc60a754dbc03bf0618f32c` | 0 | Unresolved | Blocked |
| 4 | `e2a0a0cd3d7be96362659d02a2e8a5631f61848e` | 0 | Unresolved | Blocked |
| 5 | `92e40e2200511531d377def795f0a3038752dd7a` | 0 | Unresolved | Blocked |

## Retained full-scope assessment

The twelve earlier Lean owners have exactly their previously reviewed bodies, so their detailed round-1 through round-4 analyses remain applicable. The following records the material retained semantics rather than treating their earlier Blocked outcomes as approvals.

**Parsers.** The tree parser executes actual frame resumption and child reconstruction, with generalized arbitrary stack/tail contracts including failed continuations. Raw success, exact consumption, prefix uniqueness and emitter composition remain connected to the actual implementation. Successful work is `7*n+3`; unrestricted raw work is at most `5*M+2`. The full input parser binds both returned trees, separators, returned fuel bits and EOF, permits unequal tree sizes syntactically and retains high-zero width. Successful work is `7*Ns+7*Nt+3*b+15` and raw work is at most `20*(M+1)`. Runtime does not consult specification codes or tree-size oracles. Reserved tags, missing children, bad delimiters, trailing data and unequal-size syntax remain covered by connected cases. [Sources: TreeParser, InputParser, RotationCertificateParsing; round-1 report.]

**Streaming verification and witnesses.** Endpoint equality occurs only at actual certificate EOF. Each nonempty step executes the fixed-width predecessor before parsing, applies the parsed move to the current returned tree, and feeds actual remaining fuel and input to the recursion. Every failure stops. Termination length is proof-only. The all-raw iff has no validity, canonical-width, equal-size or positive-fuel premise: acceptance means exact encoded successful moves with count at most `value bs`. The raw bound remains `(3*bs.length+3*source.numNodes+12)*cert.length+3*source.numNodes+6`. Independent `Yes` uses exact input encoding, common-size shapes and attained distance bounded by the threshold. A minimum trace, rather than an arbitrary normalization route, fits both the threshold and `2*n−2`; successful intermediate sizes give a word witness of length at most `2*M²` including small shapes. The full verifier parses input first and binds its returned fields to the stream, with all-raw iff, independent soundness, small completeness and `32*(M+W+1)²` work. Current-tree, stale-position, fuel-width, every reserved tag and arbitrary unvisited token-tail distinctions remain connected. [Sources: Streaming, Witness, Verifier, RotationCertificateVerification; round-2 report.]

**Bit codec and binary verifier.** The fixed four-bit least-significant-bit-first map covers all sixteen tags and preserves order and width. Packing costs `6*N+1`. Tail-first complete unpacking has arbitrary-suffix contracts for both outcomes: `+4` per packed prefix tag on suffix success, `+2` on suffix failure, with no tag decode after recursive failure. All-raw success is exact encoding; one-to-three-bit terminal fragments reject, costing `2*q+2` after `q` complete blocks. Valid unpacking costs `4*N+2` and raw work is at most `I+2`. Packed emitters execute actual source emitters and packing, costing `8*M` and `8*W+2`. The binary wrapper executes complete input decoding, input parsing, complete certificate decoding and actual stream in that order, with no second parse or word-wrapper call. Input failure skips certificate bits; eager certificate decoding can reject a partial ending before any stream step. Its independent `BinaryYes`, all-raw iff, accepted bit witness `C≤I²` and raw work `40*(I+C+1)²` remain unchanged. Literal costs, endian/high-zero cases, partial tails and complete emission-plus-verification `267` remain connected. [Sources: BitCodec, BinaryVerifier, RotationCertificateBinary; round-3 report.]

**Existing concrete block decoder.** The three-stack, three-label machine retains finite control and an injective success/failure output. Actual generalized scan/emission/cleanup phases prove, for every raw input, a present exact halt target after `2*(I/4)+2` transitions, bounded by `I+2`. Its actual timed and polynomial records use one fixed machine. The potential theorem covers actual reachable configurations with stack cells at most `I+1`, including the tight empty-success case and the distinction between a present halt and subsequent outer `none`. Arbitrary entry registers/stacks, malformed residuals, actual ordering and finite instances remain covered. These conclusions concern that component; the new paired framer is reviewed separately below. [Sources: BitDecoderMachine, RotationCertificateBitDecoderMachine; complete round-4 report.]

## Independent framing and result representations

The new owner defines the mathematical pair format before proving its machine implementation:

`escapeBits input = input.flatMap (fun bit => [false, bit])`

`frame input cert = escapeBits input ++ true :: cert`.

The false guard distinguishes a first-coordinate payload from the delimiter. A true bit after a false guard is payload. The first true flag encountered at a guard position terminates the escaped first coordinate; every subsequent bit belongs to the certificate. A trailing false certificate bit or another true certificate bit is therefore ordinary data. No parity-only recognizer, search for the first raw true bit, numeric normalization or prefix-free claim is substituted for this grammar. [Source: BitPairFraming, lines 25–157, `escapeBits`, `frame`, `unframe` and raw contracts.]

`unframe` has the four required branches: empty input fails; true-headed input returns empty first coordinate and the complete tail; a lone false fails; false plus a payload recursively decodes the suffix and prepends that payload to the returned first coordinate. Its general prefix theorem applies to arbitrary raw suffixes using `Option.map`, hence covers successful and failed continuation. Exact raw success is equivalent to equality with `frame input cert`. Exact raw failure is equivalent to either `escapeBits input` or `escapeBits input ++ [false]` for some input. These two malformed families allow arbitrary payloads, including true, and cover all failures without a validity premise.

The source recursion evaluates the suffix first. The finite machine scans the prefix first and buffers data. The contracts establish equal returned results through their actual executions; they do not assert the same evaluation order or cost.

The append law is `frame input cert ++ tail = frame input (cert ++ tail)` for arbitrary tail. A valid frame can be a strict prefix of another valid frame. Such a tail changes the certificate rather than becoming ignored junk. Frame equality recovers both coordinates; zeros and their widths remain observable.

The independent output representation is:

| Semantic result | Output stack |
| --- | --- |
| Failure | `[]` |
| Successful empty pair | `[none, none]` |
| Successful pair `(input,cert)` | `none :: (input.map some ++ none :: cert.map some)` |

Here `none` is one of three output-alphabet symbols; false payload is `some false`. Neither is absence of the machine configuration. The full `resultCode_injective` proof recovers both arbitrary coordinates, using absence of marker symbols inside mapped Boolean payloads. Success output length is `I+C+2`. The two markers are the chosen fixed format; no unjustified claim that both are logically necessary for every possible injective format is made. [Source: lines 159–188, `resultCode`, `resultCode_injective`, `resultCode_length`; matching actual prints and connected encoding examples.]

## Actual finite machine and operational semantics

The machine has four stack identifiers: `input`, `firstReverse`, `certReverse` and `output`. Its five labels are `scanPrefix`, `copyCert`, `emitCert`, `emitFirst` and `clearFirst`. Registers are exactly `Option Bool`, hence have three possible states. The first three stack alphabets are Bool and the output alphabet is Option Bool; finite instances are supplied for every alphabet, identifiers, labels and registers. The seven new actual finite syntheses corroborate these definitions. The machine is fixed before quantifying over raw inputs. Initialization puts the raw bits on the input stack, leaves the other three empty and selects scan with zero registers. It does not preload a result. [Source: lines 190–264, finite carriers, `program`, `machine`; initialization and actual printed records.]

The executed statements use stack pops/pushes, finite register tests, fixed updates, jumps and halt. Each `getD` is guarded by presence of a value just popped in that statement. Old registers cannot invent a missing input bit or alter a delimiter. Jumps and finish reset the register. Executed callbacks do not inspect an unbounded stack/list, evaluate length, call the recognizer/verifier, obtain a numeric fuel value or invoke an answer oracle.

The complete program performs these concrete operations:

| Label | Actual behavior |
| --- | --- |
| scanPrefix | Pop the flag. EOF enters cleanup; true enters certificate copying. False pops one payload; missing payload enters cleanup, otherwise push it onto firstReverse and repeat scan. |
| copyCert | Pop one remaining raw bit and push it onto certReverse; at EOF enter emitCert. |
| emitCert | Transfer one reversed certificate bit to output as `some bit`; when empty push the separator marker and enter emitFirst. |
| emitFirst | Transfer one reversed first-coordinate bit to output; when empty push the leading marker and halt. |
| clearFirst | Pop one accumulated first-coordinate bit per transition; when empty halt, preserving output. |

Under the pinned mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, a TM2 transition executes the chosen finite statement through its nested primitives until goto/halt. Goto ends that transition and does not execute the next label immediately. The longest selected scan branch contains a fixed eight primitives; it hides no variable-size traversal. The clock is this pinned TM2 transition count. It is not the source-event tariff or a newly proved TM1 simulation cost. The pinned definitions read in round 4, including `stepAux`, `step`, `Reaches`, `initList`, `haltList` and the timed/polytime records, are unchanged.

A halt instruction itself does not erase untouched stacks. Exact `haltList` equality therefore needs the appropriate other stacks to be empty. The new code respects this distinction in both the one-step and phase contracts. Ordinary rejection reaches **some exact halt configuration** with empty encoded output; the following transition returns outer none. It does not use outer none as an ambiguous rejection witness.

## Arbitrary-state steps and complete phase contracts

`cfg` exposes every label, register, raw stack, first reverse stack, certificate reverse stack and old output. `cfg_eta` covers every actual machine configuration. The thirteen one-step equations cover all scan shapes, both cases for each subsequent label and halt. They quantify over arbitrary old registers and untouched stacks, proving complete configuration equality. In particular, terminal emit/clear step equations preserve arbitrary unrelated raw/certificate stacks rather than silently deleting them. [Source: lines 265–403; actual elaborated types.]

The following actual-iteration theorems generalize the changing state needed by their inductions:

| Phase | Premises and result |
| --- | --- |
| `emitFirst_iterate` | Raw and certificate reverse stacks empty; arbitrary firstReverse, old output and registers. After `a.length+1` steps, exact halt with `none :: (a.reverse.map some ++ out)`. |
| `clearFirst_iterate` | Raw and certificate reverse stacks empty; arbitrary firstReverse, old output and registers. After `a.length+1` steps, exact halt preserving old output. |
| `emitCert_iterate` | Raw empty; arbitrary both reverse stacks, old output and registers. After `b.length+a.length+2` steps, exact halt with both ordered coordinates/markers followed by old output. |
| `copyCert_iterate` | Arbitrary raw suffix, both reverse stacks, old output and registers. After `2*raw.length+b.length+a.length+3` steps, certificate order is `b.reverse ++ raw`; all payloads are actually transferred. |
| `scanPrefix_iterate` | Arbitrary raw suffix, old firstReverse, old output and registers, with certificate reverse empty. After `runSteps raw+a.length` steps, exact halt with `resultCode ((unframe raw).map (fun pair => (a.reverse ++ pair.1,pair.2))) ++ out`. |

The scan contract covers every suffix outcome. Failure clears both old and newly accumulated first bits and preserves arbitrary old output. Success prepends the old first bits in their intended order. The arbitrary-output scan theorem is a genuine strengthening of the initial preparation, explicitly retained in the final requirements, not a narrowing to an empty-output example.

The empty unrelated-stack premises in phase theorems are necessary for exact haltList equality. The connected counterexample starts cleanup with an unrelated certificate reverse stack `[true]`; it remains present at halt, so that result is not `haltList machine out`. This directly rejects the tempting but false unrestricted cleanup claim. More general one-step equalities remain available where only the label/register changes and a stack is preserved.

The proofs compose actual one-step equations through `next`, defined using Option.bind of the actual machine step. They follow the actual enlarged reverse stacks, updated output and returned suffix. Emission and copying preserve arbitrary prior output; failure does real repeated cleanup. Mathematical reversals and append identities are proof descriptions of those steps, not executed free conversions. [Source: lines 405–508 and the arbitrary-state examples.]

## Exact counts, all-raw timed data and workspace

The proof-side `runSteps` recurrence is:

| Raw shape | Count |
| --- | ---: |
| Empty | 2 |
| `true :: cert` | `2*cert.length+4` |
| Lone false | 2 |
| `false :: bit :: raw` | `runSteps raw+2` |

It yields exact valid-frame time `2*I+2*C+4`. This accounts for I guarded-prefix scans, delimiter transition, C certificate copies, EOF transition, C certificate emissions, separator transition, I first-coordinate emissions and final marker/halt. A complete escaped prefix of q bits without a delimiter, with or without one dangling false guard, takes `2*q+2`: q scans, one failure probe, q cleanup steps and final halt. The missing payload is detected inside the same fixed scan transition. [Source: `runSteps_escape_append`, frame/missing-delimiter/incomplete-guard count and run theorems.]

`machine_run` covers every raw input, without framing-validity or success premises, reaching `some (haltList machine (resultCode (unframe raw)))` at the stated actual count. The universal bound is **`runSteps raw ≤ 2*raw.length+2`**, not equality for every input. It is tight for certificate-only frames. The exact target remains present at that count; a subsequent transition is outer none. The all-raw theorem and absorbing absence also prevent a hidden earlier disappearance being mistaken for this result.

`outputsInTimeExact` and `outputsInTime` are constructed timed records containing the actual step count, the actual run theorem and the proven inequality. `computableInPolyTime` contains one fixed machine, identity bit/output alphabet equivalences, polynomial `2*X+2` and actual per-input output evidence. I inspected the complete elaborated record bodies. Its mathematical noncomputable packaging does not add an oracle to the executable finite program. [Source: lines 469–587 and actual Audit5 prints.]

Workspace uses the sum of all four actual stack lengths. Credit is one in scanPrefix/emitFirst, two in copyCert/emitCert, and zero in clearFirst/halt. Potential is cells plus that credit. The general `step_potential_le` quantifies over all actual configurations and assumes only `machine.step c = some d`, without a well-formed-state or reachability premise. Its complete cases account for transfers, consumed flags, cleanup and markers: a delimiter removes one cell while adding one credit, and each output marker adds one cell while consuming one credit. [Source: lines 589–699.]

`reaches_potential_le` uses the pinned actual Reaches relation, and `reachable_stackCells_le` starts at the real initialization potential `N+1`. Therefore **every actually reachable configuration has at most `N+1` stack cells**, including failure paths. This is a transition-boundary cell theorem; it does not claim host allocation, physical-bit space or a transient stepAux bound. The empty pair uses raw `[true]`, and the visible four-transition execution reaches two output markers. Its actual Reaches proof establishes the tight extra cell, so the workspace example is not vacuous. A connected per-stack result follows from the same actual reachability premise.

## Returned fields, independent language and one witness

`verifyFramed` executes `unframe` and, on success, feeds its actual returned coordinates to the existing `verifyBitsRun`. Failure returns false. The code adds no measured source-work tariff for framing. All-raw acceptance iff gives an exact frame whose binary verifier accepts. The expanded trace iff gives exact packed input/certificate codes, an actual successful move trace and the threshold condition. Soundness returns independent BinaryYes for the same first coordinate. `binaryYes_iff_exists_framed_certificate` preserves the independent distance-language meaning already reviewed. [Source: lines 701–798; actual prints of the wrapper and previously inspected Yes/BinaryYes.]

The existing attained-minimum witness supplies a certificate with `C≤I²`. Consequently the same frame has length `2*I+C+1≤(I+1)²`, framing time at most `2*(I+1)²+2` and every actually reachable framing configuration has cells at most `(I+1)²+1`. `outputsInTime_small` constructs the timed record for that actual frame; it is not a machine implementation of full verification.

The connected `a_single_small_witness_has_acceptance_time_and_space` places one existential certificate outside the conjunction of certificate size, frame size, actual acceptance, actual timed-record inhabitance and a universal bound over all configurations actually reached from that same frame. It does not select separate unrelated certificates for different clauses. The one-rotation BinaryYes client demonstrates a nonempty instance.

The client `binary_source_work_is_bounded_by_the_framed_length` proves the existing binary source tariff is at most `40*frame.length²` for all input/certificate pairs, using `I+C+1≤2*I+C+1`. It does not add source work to machine transitions or assert an unproved quantitative simulation. The framed emitter client uses actual packed emitter return values, not merely hypothetical mathematical encodings. The full parsing/fuel/rotation/equality/streaming machine and its quantitative composition remain separate open work.

## Connected cases and distinguishing counterexamples

I reviewed all 533 lines of the new example owner against the fixed preparations and read all forty-eight actual elaborated public contracts. The cases exercise returned values, actual phases, actual timed records or actual reachability.

| Distinction | Connected evidence |
| --- | --- |
| Coordinate/result injectivity | Full arbitrary equality iff; failure versus empty success; separator distinguishes coordinate order. |
| All raw success/failure forms | Exact frame recovery, both malformed families with real cleanup, arbitrary failed suffix not repaired by an escaped prefix. |
| Empty and guarded endings | EOF/lone false cost 2; arbitrary payload without delimiter costs 4; guarded payload with delimiter costs 6. |
| Certificate retention | Arbitrary true-headed tail retained in full; arbitrary appending extends only the certificate; valid frames can be strict prefixes. |
| Endian/order/width | Opposite coordinates, nonpalindromic literal frame, zero widths in either coordinate and same numeric value with different raw width/time. |
| Initialization and stale state | No precomputed pair; arbitrary old registers cannot create absent flag/payload or confuse true payload with delimiter. |
| Visible failure execution | The escaped true prefix without delimiter has four explicit transitions and actual cleanup. |
| Arbitrary accumulated data | Old first bits precede decoded first bits; failed raw suffix clears old first bits while retaining arbitrary output. |
| Emission/copy phases | Arbitrary output suffix and registers; old certificate bits precede arbitrary raw suffix; exact counts connected. |
| False cleanup generalization | Unrelated certificate stack survives cleanup, preventing an incorrect haltList conclusion. |
| Finiteness | All work alphabets, identifiers, labels and registers checked. |
| Actual workspace | Four visible empty-pair transitions, actual reachability and tight extra output cell; universal per-stack bound. |
| Halt versus absence | Failure/empty success present at exact counts and absent one step later. |
| Uniform time | Certificate-only inputs attain the bound; every raw input has an actual timed record and uses the constructed fixed polynomial machine. |
| Semantic composition | Actual returned fields feed the existing verifier; empty first coordinate is valid framing but universally fails verification; actual emitters feed the whole source composition. |
| Same small witness | One outer certificate gives all acceptance/size/time/space clauses; a concrete BinaryYes instance inhabits the client. |

The independent one-rotation calibration connects actual emitter results to the earlier encodings. Its input has 56 bits and certificate 8 bits. The binary verifier returns `(true,137)`. The frame has 121 bits, output has 66 symbols, and the actual framing machine takes 132 transitions. Appending **either** Boolean bit leaves a valid 122-bit frame with 134 framing transitions, while the certificate now has an incomplete final codec block, so binary verification returns `(false,112)` and framed verification rejects. This distinguishes framing validity from certificate validity and shows why a longer frame can cost more framing transitions while failing earlier under the separate source-verifier tariff. [Source: `one_rotation_*` and `an_appended_certificate_bit_remains_framed_but_fails_the_verifier`; literal actual types in Audit5.]

No optional-example quota was imposed. The retained cases cover the actual semantic distinctions, arbitrary-state domains, failure paths and quantifier order required by the saved plans.

## Paper, maintained records and programme preservation

The entire prior 105,134-byte paper is an exact prefix of the new 166,236-byte paper. The added 61,102 bytes contain both fixed preparations plus the current contract map. The two fixed preparations are retained in full with only the documented Markdown heading-depth change and final-newline normalization: the compared 53,260-byte text has SHA-256 `58227db4def9d459dd45b21f8cedd645e3cedf3f78831b6e0c12ce56371fa484`. Their historical preparation statements remain historical, not implementation-review approvals. I read the current map and checked its claims against the actual contracts.

The entrypoint imports the new core and connected example owner. The inbox change concerns the current FDSA-5-93 continuation and retains the broader gate. The current paper/map/status distinguish framing-machine transitions from source-verifier work, explicitly retain full integrated validation and do not claim full verifier-machine or NP completion.

I independently compared immutable original-base, C4b and C5b JSON, including full protected objects and existing int/float/bool/null path/type/value leaves, rather than accepting the author's mechanical preservation record as review approval:

- All **44 complete historical new_tickets objects** are unchanged.
- Canonical requirement authority/commit/owners/namespaces, literal current-user override, source correspondence, authorized scope, historical catalogs and the explicit tracking exception remain unchanged.
- Remaining PFDS work, mathematical findings, unrelated local states and the separate ADWH owner remain intact.
- Among local states, only CTB-24 current work/gates and CTB-78 next action change. All twenty prior component entries, eighteen prior owner entries and twelve prior implementation source-owner entries are retained as exact array prefixes.
- Historical acceptance evidence, checkpoint-074 objects, current historical handoff and progress-084 objects remain unchanged. A current receiving-scope description now explicitly excludes the new framing component from old acceptance; it does not rewrite historical success.
- All 681 original-base and 682 C4b existing CTB nontext leaves match, and all 129 existing coverage nontext leaves match; there are zero mismatches.
- Canonical lineage, mathematical notes and the chapter-5 obligation ledger remain outside the changed scope and byte-identical to the original base. The ledger SHA-256 remains `f512f6b3723e8e036e9292aab985e93d15b2bf49b1c2c6dff79b3e6911ffcaad`.

Chapter 5 stays **92/94**, chapter 9 stays **61/110**, and no qualification is changed. C05-093 remains the ledger alias FDSA-5-93 for the page-76 NP-membership/polynomially checkable witness statement, not a printed exercise number. FDSA-5-93 remains open for the complete formal verifier machine, representation/composition/resource simulation and formal NP correspondence, with required acceptance still pending. The distinct mandatory FDSA-5-92 exact maximum `2*n−6` for `n≥11` remains open. The full programme is retained.

The new framing component discharges only its reviewed component statements subject to the unresolved acceptance gate. It does not silently delete remaining complete-verifier, composition, quantitative simulation, NP or separate-maximum obligations. [Sources: immutable paper, CTB, coverage and inbox; protected-object comparison; supplementary `framing-draft/preservation-precheck-097.json`.]

## Matching focused evidence and actual audit readback

### Normal producer and connected example builds

| Evidence | Actual result and immutable binding |
| --- | --- |
| `framing-draft/bitpair-framing-producer-1.json` | Exit 0; ordinary focused core build completed 1,339 jobs. Core 34,844 bytes, SHA-256 `62b4b6cb63c9711a0582798a736f342f5a850325be8deb1962e096d4f028fa49`. |
| Core record hash | `466b227510a51e7c11cae3160b594e89134dcbc80934cea5b45ee30621d5b3db` |
| Core log | 4,558 bytes; SHA-256 `fac34ac20d775ca71d4248920dcb7da6fb274137daf54ce9a6ee83939c2ac525` |
| `framing-draft/bitpair-framing-examples-build-3.json` | Exit 0; ordinary connected example build completed 1,347 jobs. Example 27,139 bytes, SHA-256 `871160b76b8c7842c7252516f207728e311a145e6219dd4e0582216c2e17a2e1`; both core/example hashes match before and after. |
| Example record hash | `7b1b98cdca60f57222349e6ed778eafdca8867be95634d930c3e619612c4bca9` |
| Example log | 4,626 bytes; SHA-256 `c96aba5bab6651ebd4e8962b0bff3664b68eaad6241bd5e5de88cd280652e245` |

I read both records and full short logs and checked their hashes. These are normal pinned Lake producers through the recorded native profile, with no added resource caps, admissions or manual olean injection. The logs contain module-system import warnings and no proof errors. Their actual completion times are 10:21:23 UTC and 10:29:29 UTC, respectively.

### Actual Audit5

The focused audit **actually completed** with exit 0 in the root-owned session 44389, from 10:51:15 to 10:52:51 UTC. It is not merely a prepared script or proposed command.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `FocusedAudit5.lean` | 32,328 | `138bf48088cc6a64eafd9fe6645d7d3b735ba92206f8390b13730af36dcfebd6` |
| `focused-audit-inputs-5.json` | 16,277 | `3f37c58afac7f75af7ce16cf0090bfd9b61707f42223159e910d7974bce000af` |
| `focused-audit-result-5.json` | 11,640 | `c445b32c7a918979baabc725da10faf68b7b48601b60616e9d58bce0d79bf497` |
| `focused-audit-5.log` | 489,331 | `e1920e6d95e4ebdeda15139966e2287f929e85aadf88950e8a4a63afce5f973c` |
| Author inspection summary | 7,669 | `0ea11447102f1747bcc058b38d18d2e03fd7498def883f1fa4daefe7b2aec17e` |

The completed audit's source-before/source-after mappings agree and match all nineteen immutable metadata bodies; the recorded configurations also agree. The prepared input/metadata status predates the completed audit and is not itself a completed result. The completed result explicitly has `whole_library_acceptance = false`.

The actual census reports **2,336 kernel-safe declarations, 1,617 theorems, forty project modules and zero unsafe runtime declarations**. Its axiom union is exactly **propext, Classical.choice, Quot.sound**. All fourteen new owners are present: 1,053 logical declarations and 746 theorems in total. The new core contributes 242/155 and its examples 57/54. The thirty-eight prior module counts are unchanged.

I checked the audit namespace against Audit4 and the original repository ProofAudit. The audit logic is retained; the import boundary and scoped success wording identify this selected closure. There is no special allowance for the new namespace or unsafe declarations. The complete Audit4 source appears verbatim in Audit5 after the two additional imports.

Audit5 emits **221 actual contract checks, 57 definition prints and thirteen finite syntheses**. The inherited 102/27/6 commands and their 214,364 bytes of actual output are unchanged. The 119 added contracts comprise 71 core contracts and 48 connected case contracts. I read all 3,717 lines of the new actual output, covering the thirty new printed definitions and seven new finite syntheses as well as those contracts. Only six namespace prefixes were abbreviated for display; hypotheses, binders, universes, values and bodies were retained, and the original log was not modified.

This readback checked the independent raw recognizer and result code, finite domains, complete program, arbitrary-state premises, exact present-halt target, actual timed/polytime record bodies, actual Reaches hypotheses, one-witness quantifier order, literal lengths/counts/output and actual source-work results. It therefore does not rely solely on theorem names, author summaries or source-text intent. Earlier complete semantic readbacks remain applicable only to byte-identical inherited output.

### Failed attempts remain failed

The first round-5 snapshot was candidate `295e3e6a09881220a6aaeaf19e0523a354e1e9b6`, tree `7ff7b1fec31d25ae9428c843e8620eabfab40aa1`, preserved in checkpoint 096. The first direct core check and first two connected example builds failed. I read their result records and independently compared the failed immutable Lean bodies with C5b.

The four core edits adjust proof cases/rewrites and the explicit actual-iteration target in the small timed record. The three example edits normalize the true-headed count, remove a redundant tactic and reuse the corrected count proof. They do not change definitions, theorem statements, expected values, case scope or tariffs. The matching successful producers and Audit5 apply to C5b, not retroactively to the failed snapshots. All earlier round-4 failed/uncompiled and failed-example snapshot dispositions likewise remain historical.

## Old-base run and comparison boundary

The old-base whole-library command remains a different computation at `bc95f503ccbf043136c6699992388f750270e8e6`. The current record read for this report is `baseline-observation-current.json`, observed **2026-11-21 11:05:32 UTC**, 20,181 bytes, SHA-256 `2ec78bf372fb83b6878fad03db6411fe341a8bd38ce53f39618d8f004432854f`. It records session 41860 still running with **nine constituent Lean exit-137 failures**, including the latest SquareKit.SmoothQuotientGeneratedBaseChange. It records matching failed source bodies across the original base, C5b, author and acceptance checkouts. It supplies no overall passing receipt, proof diagnostic or established cause. Exit 137 alone does not establish a source defect, imposed cap or particular memory cause.

The earlier eight-failure observation at 10:44:05 UTC remains a historical observation (17,777 bytes; SHA-256 `1922e642d6b005df5fec77869210cdb3ec11330bb1178e4432ec1a13d50c2d8a`). Neither observation validates C5b or closes SP-V001.

The late C4b prevalidation comparison, `live-compare-4.json`, has actual exit 0/status ok and SHA-256 `b54e43b36c3adbaf420aadd075813353b8bfc3ce7df69ccd34c0902284ce1eeb`. I checked its identities against C4b metadata. It remains historical prevalidation evidence for that candidate, not round-5 validation or a final comparison. The earlier reports are not rewritten to pretend this later evidence had arrived before their completion.

No extra prevalidation comparison is imposed on C5b. The supported final post-validation comparison remains pending along with exact-candidate integrated validation and final verification. Overall Spec therefore remains **Blocked with zero source findings and unresolved SP-V001**.

## Report preservation and next reassessment

All eight earlier Spec report files are retained byte-for-byte. Their exact hashes, the complete nineteen-file scope and audit inventories are recorded in the companion JSON. No source, checkout or coordinator record was modified by this review.

The next reassessment on this same Spec axis should examine matching exact-candidate integrated evidence and the required final verification/comparison. Until that evidence exists, the source assessment above is complete, but no Passed Spec outcome, accepted-base advancement, FDSA qualification, full verifier-machine completion, NP conclusion or receiving publication is established.
