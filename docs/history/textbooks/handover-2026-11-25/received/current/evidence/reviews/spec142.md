# Spec review — immutable candidate142, original loop round9

**Overall outcome: Blocked.** The full53-owner intended public-claim, operational-definition, dependency and connected-case assessment is complete within the reading and reuse limits below. **SP-D001 is resolved in142. SP-D002 remains open on142. SP-V001 remains blocking acceptance.** No source acceptance, integrated acceptance or textbook qualification is granted.

This report is the independent successor Spec assessment by `/root/requirements_review/spec139`, replacing original `/root/parser_review/spec` in the same CTB-24/FDSA-5-93 loop. It preserves the original seven rounds, the successor round8 assessment on139, all stable findings and every historical UNKNOWN. No new Standards142 report was read before producing this assessment. The current report supersedes only its own provisional reading-progress report; it does not rewrite historical reviews.

## 1. Candidate, requirements and review authority

| Item | Immutable identity |
|---|---|
| Candidate C142 | `b785e1298c1ba188fe59ac3ecd6e647a4b4f9f92` |
| Tree | `89c45ac0fda464a47eec42d4db1813c967e62355` |
| Incorporated ticket base M | `ec4949a94ed70084d70f5b273fb0cc6dca8b2647` |
| Original full-spec base B | `bc95f503ccbf043136c6699992388f750270e8e6` |
| Previous reviewed C139 | `50581179674f0ccf364ca3c372b5e07e5c70c80e` |
| Cumulative scope | 53 owners; manifest entries `{}`, exclusion list `[]` |
| Scope identity | `c72a77903b0cf83573225f4e22f07260979a2d0a5484ffd25b72923f723319ce` |
| Source/content identity | `abe00a1381c340f23af5b48ad6eb40af484e844e2cf0358a7db0092048fb5c6e` |
| Projection identity | `9ba5fd76e05224d822fce921af29dc9d6ad96324c75641cc44985bc60ceff565` |

The supported receipt is `/workspace/scratch/ae71b485b114/work/review/candidate142.json`, 9,731,525bytes, SHA256 `245212dc08a030395d2b86845394835743e8e6a156c26ec2079277cb9b1d5944`. Its exact53-path scope agrees with this assessment's inventory. Each of the53 immutable source bodies was hashed independently against its receipt descriptor; all match. Repository source was read through exact Git objects from `/workspace/scratch/ae71b485b114/work/conaled`, never by treating changing author files as142. The supported diff remains `git diff M...C142` with the original B/M identities retained.

The full governing specification remains the immutable restored requirements15 file, not an abbreviated replacement:

- `/workspace/scratch/ae71b485b114/restored/conaled-textbooks-136-progress-2026-11-23/evidence/requirements.txt`: 2,205,749bytes, SHA256 `73ef064c6dc6cdb737c1a27224b2bfb4e7e0092213107318723aff0a885aeb9d`.
- `/workspace/scratch/ae71b485b114/work/review/timing-addendum138.md`: 5,708bytes, SHA256 `c6a043aab84600f557e03fb60465d230cb5a992ea57ac7338e85289df96283a7`.
- `/workspace/scratch/ae71b485b114/work/review/controller-tape-addendum140.md`: 5,322bytes, SHA256 `cdd07335fff81761599f4ecf2074b3d065a13806997eb0b103cdd73160cad361`.
- `/workspace/scratch/ae71b485b114/work/review/primitive-addendum141.md`: 6,738bytes, SHA256 `83f6d00bdc401d7b859b8b58c0b55a8f8d9398f49166cf46e06df29f8329420c`.

The original `/workspace/scratch/ae71b485b114/restored/conaled-textbooks-136-progress-2026-11-23/evidence/review-record.json` remains805,915bytes, SHA256 `f2068a2d24aa03a297521e219ce96a742f956abc91488e19319f9fa019843c20`. Standalone round1–4 report bodies are absent and are not reconstructed. Exact matching original-round7 analysis is attributed to its original reviewer; its Blocked outcome is never reused as approval.

The current user's two overrides are retained verbatim in the JSON companion: one self-contained archive per checkpoint time, and no local progress posting to issue558. No compiler, source/dependency/output writer, issue message or publication was performed by this reviewer. Root owns checkpoint backup and acceptance execution. This report is review evidence for the single checkpoint archive, not a second independent archive.

The candidate's AGENTS, code-review and example-driven-development skills, review-loop/task-authority guidance, domain, architectural-quality, formal-development, glossary and composition/audit ADR are exact matching Git entries from139. Their previous full reading remains applicable. This is the same Spec axis, with no third substantive reviewer or replacement acceptance process.

## 2. Findings and dispositions

### SP-D002 — P2, unresolved on142: the current paper overstates the configured live2/none3 case as genuine initialization

**Location:** `docs/research/fdsa-rotation-certificate-preparation.md:75005`, with the actual case in `Examples/TuringSimulation.lean:521` and its following source/primitive run declarations.

The paper describes “genuine-init live2/none3 boundary observations.” The connected two-label case actually starts at

```lean
twoInitial T = ⟨some false, true, T⟩
```

for an arbitrary `Tape Bool`. The source program sends false to true and then halts; `two_native_steps`, `two_primitive_bound`, `twoPrimitiveRun` and `threePrimitiveOuterNone` consume or construct that actual configured run. They preserve its full tape and true register, with counts2 to live halt and3 to outer `none`. No native `TM1.init` or `TM0.init` identity connects this particular arbitrary-tape true-register case to initialization.

The pinned Mathlib definition `TM1.init` chooses `some default`, `default`, and `Tape.mk₁ l`. The native `TM1to0` default similarly uses `(some (M default), default)`. Expanded actual output2986–3039 exposes the ordinary `instInhabitedBool` arguments and the explicitly configured `twoInitial`; it does not contain a genuine-initializer result. The independently frozen primitive expectations explicitly specify true registers and arbitrary tape for this source-run case and distinguish it from the genuine-init controller consumer. Thus the count/endpoint proofs meet their intended fixed case, while the paper claims a stronger initialization boundary.

**Required remedy:** describe this observation as an actual source-run live2/none3 case in a supported successor candidate, or separately prove the stronger initialization connection using explicit correct defaults and an actual input tape. The fixed transition counts and intended case should remain intact.

Root subsequently reported a one-phrase author correction at10:04:17Z in later source. That information does not change immutable142 or resolve this finding here. This Spec finding was identified independently from the paper and source before that acknowledgement; the new Standards report and future source were not used as142 evidence.

### SP-D001 — P2, resolved in142: active continuation gates now describe the current53-owner stage

The four originally flagged active fields now agree with the current CTB-24 implementation gate:

| File | Active field |142 line |
|---|---|---:|
| `docs/textbooks/CTB.json` | `local_state.CTB-78.next_action` |236|
| `docs/textbooks/CTB.json` | `local_state.CTB-24.next_implementation_gate` |1564|
| `docs/textbooks/CTB.json` | `next_ticket_gate` |2440|
| `docs/textbooks/coverage.json` | `source_readiness.current_gate` |903|
| `docs/textbooks/coverage.json` | `qualification_basis.current_gate` |921|

All five were independently read, together with the complete139-to142 JSON delta. They identify the cumulative53 owners, full inherited requirements plus the timing/controller/primitive addenda, successful narrower development checks and still-pending ordinary modules, public types and exact cumulative acceptance. They preserve whole build/exhaustive audit, immediate nonrepairing verification, supported comparison and both original axes. They explicitly separate the139 failure observations and later observation/I/O/certificate research. They retain the full remaining programme and prohibit qualification from focused checks or checkpoints.

Earlier dated46/48/51-stage records remain historical; they are not interpreted as current acceptance. The original139 finding remains historically valid. Resolution is specifically against142's corrected active fields, not an edit to the previous report.

### SP-V001 — blocking acceptance, unresolved: exact current validation and remaining actual statement output are unavailable

The actual readable143 development command exited0 with stable bound inputs. It provides narrower evidence for the matched amalgamated producer/generic bodies. It does not establish ordinary installed module validation or the complete acceptance gate.

Still absent are actual output for the18 new controller-client declarations, a matching ordinary142 module/client validation result, exact whole142 success with exhaustive audit, immediate supported nonrepairing final verification, and supported final comparison. The selected five axiom outputs show only `propext`, `Classical.choice` and `Quot.sound` for those queried roots; they are not an exhaustive53-owner audit.

The historical139 ledger records seven actual Lean subprocess exits137, with no outer child-exit/terminal result at that observation. No cause is inferred from137, and this report does not upgrade any historical UNKNOWN. A narrower successful development run cannot supply the missing139 terminal or current142 acceptance.

**Required remedy:** supply actual matching ordinary module/client evidence and all18 missing controller-client statement outputs for independent reading, then successful exact cumulative whole build/exhaustive audit with stable input records, immediate supported nonrepairing verification and supported final comparison. Continue this same finding and these same review axes. A source correction requires a new supported immutable candidate and explicit delta review.

## 3. Full-scope source and mathematics assessment

No actionable mathematical statement, operational-definition, case-connection, count or endpoint defect was established by the source and output reading described here. This statement has the precise limits in sections4–6; it is not a proof that every intended theorem has been captured, every proof has been independently checked, or the candidate is accepted.

### Primitive native transition counts

`Applications/Resources/TuringSimulation/TapeToPrimitive.lean` was read completely, including all262 lines and proof bodies. Its runtime count follows the actual selected TM1 body: a move or write adds one; load updates registers without adding a primitive step; branch selects the actual branch; goto or halt emits one dummy write. `primitiveBound` is a syntax bound taking the maximum of branches. The positivity theorem is material: equal-first-step transport is used only for positive iteration, so folding a load/branch cannot silently identify different zero-step configurations.

`statement_exact` is about literal `TM0.step (TM1to0.tr M)` from the supplied statement/register/tape configuration to the complete translated `TM1.stepAux` result. It does not merely count abstract source constructors or project away tape contents. `statementEvalsTo` stores that exact count. `source_step_bounded` consumes an actual source transition and a bound on every actual program label. `finite_run_bounded` consumes the actual finite source iterate; its zero-step case is reflexive and its successor proof composes the reached intermediate configurations and witness counts. The endpoint is the full translated configuration, including register state and tape.

The concrete TM2-to-TM1 translation has primitive syntax bound at most3 on every native label, including continuation labels. The statement action-to-goto bound is3, while normal statements have bound1. This is independent of reachability and avoids assuming the desired bound only on examples. `stack_run_bounded` consumes an actual TM1 timed witness with boundW and produces a TM0 witness with bound3W. A live translated halted configuration is still a configuration; the subsequent native step to outer `none` is proved separately.

### Same-count finite-support restriction

`Applications/Resources/TuringSimulation/FiniteControl.lean` was read completely, all379 lines including proofs. `map_iterate_option` transports actual optional iterations through the native `Machine.map` under the alphabet retraction, supported-label inverse and actual `Supports` closure premises. It handles both present configurations and `none`. Its evaluation and timed-evaluation transport preserve the same literal `h.steps`, not only an unrelated upper bound or existential reachability fact.

The finite restriction is to the subtype of an actual finite support containing the original default state. Ambient control need not be finite. The identity alphabet map preserves the entire tape, and the restricted initializer is the actual `TM0.init` with the corresponding supported default. The arbitrary-source restriction requires support membership; the genuine-initial restriction obtains that premise from `Supports`.

The proof-side label retraction is noncomputable and may use a fallback on unsupported labels. The separately defined `closedRestrictMachine` does not use that retraction during execution: it evaluates `M q.val a`, returns `none` unchanged, or attaches the support proof to the actual returned state/action. Source and printed definition both expose this match. No runtime membership decision or fallback branch is inserted. Its extensional equality to the native map restriction transports the same-count results. This establishes the stated finite carrier/transition semantics; extracting a numerical enumeration or explicit transition table remains a separate task.

### Actual finite package defaults and encoded initialization

`Applications/Resources/TuringSimulation/FiniteStackToTape.lean` was read completely, all365 lines including proofs. `finiteActionBound` is the supremum of the actual finite program's action bounds, fixed before choosing raw input. `encodedInitial` uses the supplied `tm.main`, `tm.initialState` and literal marked multiplexed `trInit` tape. Its relation to `initList` is proved using those supplied package fields, rather than a convenient global default.

The installed `related_marker_observation` is in142: it retains the target label/registers, true bottom marker and each track's symbol at the reversed source stack's index0. That is the bottom-side symbol dictated by the representation, not a mistaken assertion about the source stack's top. Later controller observation research is outside142; this installed generic observation is not excluded with it.

Finite primitive support is constructed from the native `TM2to1.trSupp` and `TM1to0.trStmts` of the actual finite program. `Package.ambientInhabited` explicitly contains the translated body at `tm.main` and `tm.initialState`; `controlInhabited` uses that supported ambient default. The whole initial tape is preserved under `mapCfg`, and the package's initial configuration is proved equal to native `TM0.init` with the intended instances. The expanded actual type/definition output was read specifically to check those otherwise implicit choices.

Alphabet finiteness requires every indexed stack alphabet, along with the package's finite index/control/register fields. Control support and alphabet finiteness are not allowed to vary with the raw input. The package's `closedMachine` is again a direct actual ambient-transition match with an attached support proof. `restrictRun`, `restrictInitialRun` and `closedInitialRun` preserve the same witness steps and whole optional endpoint.

### Controller quantitative instantiation

`Applications/Resources/RotationCertificate/FrontEndStreamTapeMachine.lean` was read completely, all257 lines including proofs. It quantifies over the fixed finite caller and supplied initial state before arbitrary raw input, including malformed input. LetN be the original raw length andA the finite action maximum of the actual controller program. The source execution is obtained from the controller's genuine-init iteration theorem. The per-stack hypothesis comes from its actual peak theorem: a particular stack length is bounded by the complete stack sum, which is at most `max N 1` on the required prefix. No target runtime/space oracle is assumed.

The native TM1 bound is

`runSteps raw * (1 + A * (2 * (max N 1 + A) + 2))`.

The supplied explicit polynomial expression is

`(N^2 + 10*N + 36) * (1 + A * (2 * (N + 1 + A) + 2))`.

For fixedA this is an expression of degree at most3 inN. This assessment does not import the later research's `Polynomial` object or witness-composition declarations into142. The primitive bounds are three times these native expressions. Finite support restriction preserves the same primitive witness count. The outer-`none` theorem pays one additional step after the live halted configuration.

The live endpoint retains the full native `TrCfg` relation to the actual `haltList` with the verification bit. Input and output tracks remain distinct: framedRaw is the input store, fuel is the Boolean answer store. The start is already encoded by `trInit`. These results do not provide an executed ordinary Boolean input serializer, ordinary output adapter, visited-tape-space bound or conventional formal NP theorem.

### Fixed connected cases

The complete new274-line controller client and every appended generic-client proof were read. The fixed expectations were independently read in `/workspace/scratch/ae71b485b114/work/checkpoint140a-preparation/frozen/research/tm-research/primitive-next/EXPECTATIONS.md`: 3,185bytes, SHA256 `2600234fa4d42e45d9d91cc658f3c0efe1d12fccae19379716afd4193f9ccf52`. Its current copy had the same hash at reading.

| Case | Actual connection assessed |
|---|---|
| Generic goto | One primitive dummy write, arbitrary supplied tape/register, complete unchanged tape endpoint. |
| Outward scan | Two primitive transitions: move right then dummy write; go label/register retained. |
| Empty push true | Three transitions; selected true symbol remains on the tape at the full returned endpoint. |
| Empty pop | One transition; false register becomes true; entire tape unchanged. |
| Empty peek | Three transitions with separately connected first left excursion, second return/register update and third continuation selection. The intermediate head is off the bottom marker. |
| Two-label source execution | Actual true-register, arbitrary-tape source run; live halt2, outer `none`3; generic finite-run theorem also yields bound2. This is the SP-D002 configured-run distinction. |
| Infinite ambient control | Nat control with support `{0,1}`; actual initial list run reaches live halt in1 and outer `none` in2. Finite subtype and closed transition preserve those counts and complete tape. `Infinite Nat` and finite supported-control instances are explicit. |
| Controller F01 | Raw `[]`, source clock20 and peak1; actual native and finite primitive rejecting endpoints. |
| Controller F02 | Raw `[false]`, source clock20 and peak1; actual native and finite primitive rejecting endpoints. |
| Controller V01 | Literal41-bit equal-leaf raw fixture, source clock95 and peak41; native/finite primitive acceptance and polynomial specialization2127. |
| Package defaults/encoding | Supplied true register state; empty and singleton-false encoded inputs both length1 but distinct absent/present-false track symbols at the marker; raw/answer stores distinct; full tape retained under finite restriction. |

The halt-only source used for the local primitive action fragments does not reach those action go states from its default run. The source and frozen expectations accurately identify them as tests of explicitly supplied simulator configurations. The separate two-label case consumes a real source run, and the controller consumer proves genuine initialization for its package. No false reachability assumption is introduced to connect the local fragment tests.

The cumulative review still binds the original84 independent controller records,142 cleaner boundaries,96 generic domains,81 positive closed fixtures and all preceding component cases. The new F01/F02/V01 bridge examples do not replace that obligation. The old timing client's selected-track counts6/1/1, live7 versus outer8, loaded branch8 versus1, and two-source-step exact8 versus bound14 remain unchanged and were re-observed in current actual output.

## 4. Exact source reuse and reading limits

All43 owners unchanged from139 were independently compared as complete Git tree entries, including mode and object identity. No later candidate approval is inferred from that identity. The53-owner accounting is:

| Owner group | Count | Assessment method |
|---|---:|---|
| Original-round7 Lean owners |19|Explicitly attributed original matching-body analysis, retained through round8; no historical approval reused.|
| Round8 component/controller Lean owners |20|Round8 complete operational definitions/instances, public contracts and fixed connected cases, with recorded selected proof and trace reading. Exact bodies unchanged.|
| Existing `StackToTape` producer |1|Complete600-line source/proof and139 actual public-type reading reused; exact body unchanged.|
| Unchanged textbook guides |3|Complete round8 guide readings reused; exact bodies unchanged.|
| New142 Lean owners |5|Complete source including all proofs:262/379/365/257/274 lines respectively.|
| Changed generic client |1|Complete139-to142 diff: two imports and appended lines360–723,364 lines including all proofs. The original357-line source body was previously read fully and is otherwise unchanged.|
| Aggregate and three changed documentary owners |4|Full import delta, full new paper append, complete CTB/coverage delta and all current affected active fields.|

The complete path/hash/source inventory is in `spec142-document-and-scope-check.json`; `spec142-reuse-and-source-identity.json` identifies unchanged and changed/new owners. All46 scoped ordinary Lean owners are directly imported by `SquareApplications.lean`. This is a structural import check, not a successful aggregate compilation.

The preparation paper's139 body is an exact byte prefix of142;142 adds8,815bytes/134 lines,74902–75035, all read. The full75,035-line paper was not reread. Requirements15 remains unchanged; complete operative outline/API/case ranges previously read are retained explicitly in the JSON companion and original `spec139.json`. The full53,261-line append-only requirements body, embedded support scripts, repeated trace/provenance material and all historical documentary scalar fields were not reread wholesale.

For the20 unchanged component/controller owners, ordinary theorem proof interiors were omitted except the exact supplementary ranges in `spec139.json`. Most intermediate `TracePoint` rows in the old Stream client's1321–1905 were not reread; every one of its44 case records, actual run/owned/cell contracts and trace endpoints was assessed. All84 controller records and their connections were assessed, with the81 positive literal records mechanically matching1,292 frozen fields and zero mismatches. That mechanical equality is not an execution or proof. The exact unchanged bodies permit analysis reuse without inventing an obligation to repeat every unchanged proof line; the original limits remain visible.

Pinned native dependency reading newly covered `PostTuringMachine.lean`104–229 and430–574 at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`: native TM0 semantics/initialization/support/map and map-step statement, TM1 initialization and TM1to0 defaults/translation/configuration/support construction. It supplements the round8 pinned `StackTuringMachine.lean`137–173 and331–704 reading. No complete reading of either entire native file or all omitted native support-proof lines is claimed.

## 5. Actual elaborated output and its precise boundary

The readable actual log is `/workspace/scratch/ae71b485b114/work/continuation/public-types143-readable.log`,96,332bytes/1,374lines, SHA256 `bd4fa3af0e2693e67102ebaa5166029ed7fbe205784b27904fc60130bf0a832b`. Its actual child and final receipts record the ordinary native-profile `lake env lean -EhasSorry` invocation on the amalgamated query source, exit0, no added limits, and stable bound input hashes. The namespace bodies of all four current producers and the entire generic client were independently matched against142, discarding only blank lines. Their module headers/import context are separately recorded; the amalgamation is not an ordinary installed module build.

The following output was independently read in full for142:

| Output | Reading |
|---|---|
| Readable1–70 |14 `TapeToPrimitive` declarations.|
| Readable71–253 |29 `FiniteControl` declarations.|
| Readable254–423 |36 `FiniteStackToTape` declarations.|
| Readable424–602 |14 controller bridge declarations.|
| Readable603–879 |109 generic-client declarations, including the previous timing cases.|
| Readable1326–1365 |Six current definition prints and five current selected axiom outputs.|

These are202 current named checks. The mixed log also has42 outside142 research checks at880–1325 and three outside142 axiom queries at1366–1374. Lines880–1004 were incidentally displayed while reaching the current boundary; no research assessment or candidate142 conclusion is based on them. The remaining research output and those three research axiom results were not read/approved here. The whole1,374-line log is therefore not claimed completely read.

The expanded4850-line actual log, `/workspace/scratch/ae71b485b114/work/continuation/development-cases143-attempt2.log`,333,654bytes, SHA256 `5ee87d172f9f76edba492141239d15f1543029f7c4adcef32559a5c46f8c55f3`, was additionally read at635–647,1062–1070,1081–1090,1913–2092,2986–3039,3153–3163,3201–3211 and4712–4841. These ranges check explicit native-init defaults, finite controller live/outer endpoints, the configured two-label source run, finite genuine-init examples, the six prints and five selected axioms. The whole4850-line expanded log was not read.

Default readable printing elides some inferred existential witness types and proof arguments. Explicit immutable source types were read, and the critical default/init/run boundaries above were additionally checked with expanded implicit arguments. The generated recursive `_f` bodies and proof terms behind printing ellipses are not claimed expanded. Full corresponding new source bodies were read instead. The five selected axiom roots list only the repository's standard `propext`, `Classical.choice`, `Quot.sound`; this limited observation is not an exhaustive audit or a substitute for reading the runtime definitions.

The18 named declarations in `Examples/RotationCertificateFrontEndStreamTapeMachine.lean` —17 theorems and `haltCaller` — are absent from these244 queries. Their exact names are retained in `spec142.json`; their complete source/proof/case connections were independently read, but their actual elaborated statement-output gate remains pending. Anonymous examples and generated helper types are not counted among the202 named checks. The preserved historical Audit6 gap of57 outputs in the Standards reading record is also not among these244 checks and is not closed by this Spec report.

## 6. Validation, remaining programme and continuation

The standalone/combined development evidence supports useful current source reading. It does not establish that the53 ordinary owners compile together under their installed imports, that the aggregate builds, that the exhaustive audit passes, or that the required final verification/comparison succeeded. No142 whole result or matching final verification/comparison was supplied. The139 child-exit observations are kept separate, with no invented outer terminal, retry outcome or memory/resource-cause explanation.

142 advances the source-level mathematics beyond139: fixed-controller quantitative native time, primitive TM0 simulation and finite-support restriction are now present. Their ordinary-module and whole acceptance remain open. The remaining programme still includes ordinary executed Boolean input/output adapters and their bounds, visited primitive tape space, final certificate-class/encoding/witness correspondence and formal NP, exact rotation diameter, FDSA-5-92, the full canonical VFA/FDSA/PFDS book/thesis union and separate ADWH obligations. Later certificate/observation/I/O research remains outside142 unless a new immutable scope explicitly installs and reviews it. No canonical row was qualified by this assessment.

The next useful review inputs are the missing18 controller-client actual type outputs, matching ordinary module/client evidence, exact whole/audit receipts and immediate final verification/comparison. A supported successor carrying the SP-D002 wording correction can be assessed by immutable delta review while retaining the full53-owner analysis and all original requirements. Both original axes and stable findings continue in the existing record. There is no reason to keep a compiler-free reviewer active merely waiting for a missing result.

## 7. Reproducible review artifacts

All paths below are within `/workspace/scratch/ae71b485b114/work/review/` and are included for checkpoint recovery:

- `spec142.json`: identities, exact requirement/addendum references, findings, reading ranges, missing declarations, retained historical limitations and validation boundary.
- `spec142-reuse-and-source-identity.json`: independent43-owner identity comparison and new/changed source descriptors.
- `spec142-document-and-scope-check.json`: all53 actual hashes against receipt, nonempty matching guidance entries, paper-prefix/import checks and full active gate text.
- `spec142-development-body-binding.json`: exact five-body binding to the successful readable amalgamated query source, with the differing module headers recorded.
- `spec142-type-output-index.json`: mechanical244-name alignment to readable output; semantic reading is claimed only for the current ranges above.
- `spec139.md`/`spec139.json` and the original restored review record: preserved prior source analysis, attribution, proof/trace limits and historical outcomes.

**Final disposition for immutable142: Blocked; SP-D002 and SP-V001 open, SP-D001 resolved only for142.**
