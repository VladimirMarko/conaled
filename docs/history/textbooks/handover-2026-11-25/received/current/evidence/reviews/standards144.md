# Standards round10 — immutable candidate144

**Outcome: Blocked.** ST-003 is an unresolved source finding, and ST-V001 remains an unresolved validation gate. ST-001 and ST-002 are resolved on144 only. The source assessment and the output reading described below are complete for this report; this is neither source acceptance nor whole-library acceptance.

This is the same successor Standards axis, `/root/requirements_review/standards139`, in the original CTB-24/FDSA-5-93 review loop. All seven historical rounds, successor round8 on139 and round9 on142, original finding identities and historical reading limits are retained. No new loop or third substantive axis was created. The current Spec report was not read.

## Candidate and governing scope

| Item | Exact identity |
|---|---|
| Candidate | `a45cfbc32273fb6c86171ab1b6749f89ff007fa0` |
| Tree | `0fdae5c200efdb59de26b569543799783be3d476` |
| Ticket/public M | `ec4949a94ed70084d70f5b273fb0cc6dca8b2647` |
| Original full-spec B | `bc95f503ccbf043136c6699992388f750270e8e6` |
| Cumulative scope |60 owners;45 unchanged from142,7 new,8 changed |
| Scope identity | `6745d491eb3e2eb696661aad90a8e14538770105a7e3aca2c3561ee2b6cf39ec` |
| Content identity | `37336083ff06084a2cf854219a283828cab08253f3b0d807750b1e08cfeb8a6c` |
| Projection identity | `22b413ae8650b3d37c053b557aef75c659c9e3004d71f75ca0e0326ca639cb19` |

Source was read through exact candidate Git objects. Every scoped source SHA-256, byte count, mode and Git blob was independently verified. Mutable author changes, including any future145 remedy, are outside this assessment. The receipt, source map, all60 source identities and exact specification references are recorded in `standards144.json`.

Full immutable requirements15 remains authoritative:2,205,749 bytes, SHA-256 `73ef064c6dc6cdb737c1a27224b2bfb4e7e0092213107318723aff0a885aeb9d`. It is supplemented by timing138, controller140, primitive141, output-observation142, ordinary-IO143 and ordinary-integration144 addenda. All six addenda were fully read across rounds. Requirements15 was not freshly read in full; the exact actual read ranges remain recorded without narrowing the requirements. The original review record, SHA-256 `f2068a2d24aa03a297521e219ce96a742f956abc91488e19319f9fa019843c20`, and this axis's complete139/142 history remain governing provenance.

## Open findings

### ST-003 — Two retained encoded-input statements do not elaborate

**Medium; open and blocking on144.** Locations are immutable `Examples/RotationCertificateFrontEndStreamTapeMachine.lean`113 and120, in `empty_encoded_input_has_a_marker_without_a_raw_symbol` and `singleton_false_encoded_input_has_a_symbol_on_its_marker`.

The final conjuncts are respectively:

```lean
(trInit (machine haltCaller true).k₀ ([] : Bits)).length = 1
(trInit (machine haltCaller true).k₀ ([false] : Bits)).length = 1
```

Their standalone length result supplies no expected alphabet for `trInit`. A selected index and a `List Bool` cannot determine the whole dependent alphabet family. The actual exact-body combined run reports application type mismatches at combined20629/20636, expecting `List (?m.52/54 (machine haltCaller true).k₀)` from the supplied `Bits`. Both later public queries fail with `lean.unknownIdentifier`, at combined22221/22222 and actual log119/120. These two types were not emitted.

All16 retained combined body ranges were independently compared to exact Git144. The finding is tied to real source and actual diagnostics, with the combined-versus-ordinary-module limitation retained. It is not a claim of a mathematical counterexample, nor a claim that every other declaration failed.

Applicable rules are the checked-case requirement in `.agents/skills/example-driven-development/SKILL.md`56–63, formal claim/validation requirements in `docs/agents/formal-development.md`7–16, and the code-review rule that failed or incomplete matching validation prevents passing. The concrete consequence is that these two intended empty-versus-present-false observations are unavailable as checked declarations and cannot close their actual-type reading gaps.

**Remedy:** supply the actual machine alphabet explicitly at both `trInit` applications, for example `(Γ := (machine haltCaller true).Γ)`, while retaining the exact expected tapes, lengths, cases and clocks. Capture a successor candidate and check these exact declarations and the ordinary module graph. No future mutable correction closes the finding on immutable144, and no resource or linter suppression is prescribed.

### ST-V001 — Matching cumulative acceptance remains unavailable

The current combined statement query actually exited1. Exact ordinary-module144 validation, guarded whole144 build/exhaustive axiom audit, immediate nonrepairing verification and supported final comparison are not supplied. Both continuing independent axes remain necessary on one immutable candidate. Combined development, source capture, style checks, selected-root axiom output and root/helper reading cannot replace those gates.

Two additional actual diagnostics in retained `Examples/RotationCertificateFrontEndStreamMachine.lean` are the unused section variable `[Fintype K]` at3301 and unused simp argument `Nat.zero_add` at8500. The combined probe's `warningAsError` wrapper promotes these lints. They are recorded as probe-validation observations under ST-V001. `docs/development.md`52–57 explicitly says ordinary linter warnings remain nonfatal, so this report does not invent an ordinary-build failure or a separate Standards finding from that severity difference.

The earlier whole139 run belongs to a different source identity. Seven child137 exits were previously reported; no outer terminal result was supplied to this axis. The cause and terminal outcome remain unknown here.

## Resolved findings on144 only

**ST-001:** All five active decoded gate values were read in full, independently checked equal and matched to actual scope60. They are CTB `/local_state/CTB-78/next_action`236, `/local_state/CTB-24/next_implementation_gate`1564, `/next_ticket_gate`2440, and coverage `/source_readiness/current_gate`903 and `/qualification_basis/current_gate`921. The full decoded value and value hash are retained in JSON. The gates distinguish actual development evidence from pending ordinary modules, queries, whole audit, verification, comparison and reviews. Qualification counts remain unchanged. Historical C7c resolution,139 recurrence and142 resolution remain accurate for those candidates; dated51/53-owner history is not mistaken for an operative gate.

**ST-002:** The exact paper75005 correction is captured: “actual two-step source-run live2/none3 boundary observations.” The original true-register arbitrary-tape case is retained. The new genuine native-init peek is a separate live5/none6 case with its own initialization and visit history. Candidate142's original finding is not retroactively changed, and no143 review round is invented.

## Independent source and installation reading

All seven new owners were read fully: `CertificateCorrespondence`, `TapeReflection`, `SingletonOutput`, `MarkedInput`, `PolynomialDecider`, `VisitedSpace`, and `Examples/RotationCertificateCorrespondence`.

All changed formal additions were read: controller producer1–35 and250–992; generic examples1–22 and719–1172; finite-stack addition367–381; controller-client1–22 and270–513, with diagnostic context109–125 and170–270 also inspected. Each complete prior142 namespace body of the four appended source owners was independently found byte-for-byte unchanged exactly once in144. That supports qualified reuse without implying a fresh read of every old line.

The complete142-to144 aggregate and paper diffs were read, including the seven added aggregate imports, exact wording correction and appended paper75036–75143. The recursive decoded JSON diff changes exactly the five active gate fields; all other values, including qualification, are unchanged. The entire75,143-line paper was not freshly read.

All69 frozen staging members and25 block transformations were independently verified against their recorded hashes and source ranges. Twenty-four selected fragments occur literally in144. The remaining controller fragment differs only by the documented obsolete-comment removal; the complete staged-controller-to144 diff was read and changes its header and three comment labels, not theorem or proof text. The four recorded namespace renamings and added namespace open remain explicit provenance. This mechanical agreement does not validate ordinary import context.

For the actual current query, all8 frozen preparation members, all61 dependency source identities, all16 retained body ranges and all3 verbatim query fragments were independently matched to the frozen combined file and exact Git144. The native result's296 before/after binding maps are equal; those descriptors were mechanically compared, not all individually read. The ordinary product/import provenance limitation remains explicit.

## Substantive assessment

The generic architecture keeps rotation-specific construction in the controller and clients. Reflection maps complete tapes, swaps directions and preserves control, writes and optional-step counts. Singleton output follows from full TrCfg and stack contents. Marked input distinguishes blank, false and true; it executes the empty1/positiveN+2 prelude, preserves physical input orientation, lifts live source prefixes and intercepts a stopped source with one emitter write followed by a separate outer-None step. The emitter obtains the answer from the distinct fuel store.

The decider structure fixes finite machine data, actual blank/start, an injective nonblank letter encoding and one polynomial before quantifying over raw input. Expanded types confirm the supplied blank/start instances rather than accidental ambient defaults. Its generic contract observes the stopped tape head; the controller separately proves the stronger complete singleton tape and native evaluation result. The concrete constant decider appropriately retains the remainder of its original input. A conventional pair serializer or external complexity adapter is still open.

The time composition retains actual witnesses and stored transition counts when widening bounds. Physical space quantifies over every actual live prefix, includes input positions and visited heads, and locates every nonblank tape cell using global coordinates. An erased or returned tape is not substituted for visit history. The genuine-init peek has native default source control/register, live5/none6, positions including−1, and retained visits at−1 and0. It remains distinct from the original configured2/3 example and the reflected three-step fragment.

Certificate correspondence retains literal threshold encodings, including redundant high zeros, exact input/frame lengths, malformed raw rejection, actual move-trace soundness/completeness and existing small-certificate bounds. New fixed connected cases exercise both answers, true supplied registers, input/output store separation, full tape orientation and unchanged boundary clocks. The two older failed length conjuncts are tracked explicitly by ST-003.

No additional concrete mathematical mismatch or Standards violation was found within this source and output reading. This statement is qualified by the actual reading and validation limits below.

## Actual output reading and limits

The selected native query ran11:39:09–11:45:27Z, elapsed377.240338989s, exit1, stable inputs, no resource/time limits added. Its log is425,067 bytes and5,637 lines, SHA-256 `0fc808c040c53237261586efed25e35e2c186b79c9f9bf951896fbe2e933de61`. Result scalar/control/receipt fields and the complete child-exit record were read. The full296-entry descriptor maps were compared mechanically.

| Output | Independent reading |
|---|---|
| All diagnostics | Six actual diagnostics read: two promoted lints, two source errors, two downstream unknown identifiers |
|349 planned readable types |347 emitted types fully read, log30–2158; two unavailable types remain |
| Old18 controller clients |16 actual types emitted and read; the two ST-003 declarations have no emitted type |
|18 expanded commands |14 complete emitted outputs read at2159–2896 and5558–5585; one large contract partly read at4167–4290 and5537–5557; three large expansions not read |
|22 selected axiom roots | All22 outputs at5586–5637 read; only `propext`, `Classical.choice`, `Quot.sound` listed for those roots |

The full declaration-to-output mapping, expanded command identities and exact remaining ranges2897–4166 and4291–5536 are retained in JSON. These are output-reading limits, not source-reading gaps: corresponding readable contracts and immutable source were read. Selected roots from a failed combined run are not an exhaustive audit or acceptance proof.

The new readable ordinary-space type explicitly includes the final interval equality. The full immutable contract935–962 was also read. Its expanded Exists domain explicitly binds an actual `EvalsToInTime` for the same native input, singleton finish and bound. However, the current `pp.all` output still elides let types at4171–4191, a repeated run binder at4271 and the final tail at5556–5557. The older native144c2124–2125 printer elision remains historical fact. Neither elided output is described as fully visible.

All57 historical Audit6 declaration outputs were actually read in round9 and remain credited. Their rounds6/7/8 output-range limits are retained historically, not reopened as a current unread gap. No144 execution is inferred from that old evidence. Full fresh cumulative reading is not claimed: the45 unchanged paths and older unchanged bodies use qualified prior analysis with the original limitations. Rounds1–4 standalone bodies remain absent, the historical C5b Git object remains unavailable, and root/helper reading never becomes this axis's own reading.

The original full programme remains open, including conventional adapters/NP, the broader textbook/thesis programme, unchanged qualification and every historical UNKNOWN. No compiler, acceptance/source/dependency mutation, external message or publication was performed by this axis. Earlier provisional report bodies were preserved under timestamped names before replacement for checkpoint recoverability. Root owns the user's single independently restorable archive for each cutoff; local progress must not be posted to issue558.

**Final disposition for this supplied evidence:** two open items, ST-003 (medium source finding) and ST-V001 (blocking validation gate); ST-001/ST-002 resolved on144 only; Standards **Blocked**. Candidate `a45cfbc32273fb6c86171ab1b6749f89ff007fa0`, M `ec4949a94ed70084d70f5b273fb0cc6dca8b2647`, original B `bc95f503ccbf043136c6699992388f750270e8e6`.
