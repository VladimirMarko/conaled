# Conventional adapter: implementation reading 146

**Assessment:** no semantic mismatch found between the successful assembled research and the frozen contracts and fixtures read. This is implementation assistance and actual-output reading, not an independent review or acceptance decision.

## Actual evidence and coverage

The recorded command compiled `ConventionalNative144a.lean` in the existing acceptance139 Lake environment with `-EhasSorry`. Its receipt records **exit 0, unchanged bound inputs, 78.724019908 seconds**, and no added resource or time limits.

| Evidence | SHA256 |
|---|---|
| Successful result, 8,864 bytes | `8cdf2815fc1c8e5511c72e8bc2f35e95650664840ef17536fe7c5578ab753092` |
| Successful log, 119,652 bytes / 1,484 lines | `15afab789bb7416a231884b089edbf53859411ebbee6df741022ff5b5fe2d440` |
| Combined source, 70,278 bytes | `851713367dc85513122f45b1499ca41df2c9415165e93694d5e55555f420e056` |
| Frozen original and repair1 EXPECTATIONS, identical 4,057 bytes | `90a248687dc2e4eabfc4a01d97ff6efe354aa9c09c49b2f282ce26c9051c7cf3` |

**All log lines 1–1484 were read.** The first batched tool response was truncated; lines 1–250 were reread separately in full. No unread output range remains.

| Output | Lines | Reading status |
|---|---:|---|
| 159 ordinary `#check` results | 1–669 | Complete as emitted; implicit existential types/defaults are suppressed |
| Five axiom roots | 670–680 | Complete; each lists only `propext`, `Classical.choice`, `Quot.sound` |
| Expanded `PrintMove.delta` | 681–688 | Complete |
| Expanded `PrintMove.decide_of_native_run` | 689–846 | Complete |
| Expanded `PolynomialBooleanDecider.printMove_run` | 847–1484 | Complete through its final stopped assertion |

The 162 output headers match the 159 ordinary plus three expanded source queries in order. There are no error/warning lines, `sorryAx`, or visible ellipsis/truncation markers. Named definitions remain named under `#check`; their operational bodies were read in source.

All four repair1 files were read in full. Each namespace body occurs **exactly once, byte-for-byte**, in the successful combined source: Adapter 164–628; Space 638–898; Cases 907–1195; Consumer 1206–1335. The preparation map, repair1 manifest, expectations, public contract, and complete native decider dependency were also read. Historical UNCOMPILED headers remain preserved in frozen files; the success applies to the assembled exact bodies.

## Contract assessment

The actual target operation is `(T.write letter).move direction`. The adapter reads the actual native command. A move takes one target transition and preserves the whole moved tape. A stationary write takes two transitions: print/move right into returning control, then preserve the neighbour and move left. Its normal endpoint is the **entire written tape**, including both tails.

The finite-run theorem constructs an actual optional-iteration witness to `normalCfg finish`. Its count is the sum of 1 per actual move and 2 per actual write along native prefixes, bounded by twice the native count. It includes zero steps. This is connected to executed transitions, not an assumed timing interface.

Decision consumes the actual native stopped proof and an output equality under an injective Boolean embedding. It appends **one real print-self/right-move transition** into accept or reject. The complete endpoint tape is `finish.Tape.move right`; count is `simulationTime + 1 ≤ 2*T + 1`, with bounded witness `2*B+1`. Outer none is a distinct further observer step.

The expanded consumer fixes package `d` and alphabet equality before `raw`. Every visible native default uses `d.start`; every tape default uses `d.blank`. Target initialization is `normal d.start` with literal `raw.map d.bit`. Alphabet and input length remain unchanged. The package already supplies finite alphabet/control, injective nonblank bit letters, and a fixed natural polynomial. Target control has cardinal `2*card Q+2`; time is the fixed polynomial `C 2 * d.time + C 1`. The classical equality consumer remains explicitly noncomputable and does not export an enumerated transition table.

Space follows every actual target prefix and selected direction. Temporary write excursions and the final decision movement count as visits. The interval contains the initial input cells and origin, including empty input, and has cardinal at most `max N 1 + U`. The paid witness gives `max N 1 + (2*B+1)` for every prefix up to its actual count. Outer none adds no cells. Generic `N` does not assert arbitrary initial tape support fits that length; the decider consumer specializes to literal input and its length. The other-coordinate lemma checks the physical frame of one combined operation.

## Frozen cases

| Fixture | Observed contract |
|---|---|
| Already stopped false / true | Normal 0; reject / accept 1; outer none 2; paid generic theorem consumes actual T=0 witness |
| Write false / true on empty / present-false input | All four normal counts 2 and decision counts 3; all four full decision tapes and terminal controls explicit; outer none 4 for the general family |
| Supplied start | Native start true and target normal true, while ambient Bool default is false |
| Literal inputs | Empty head none; present-false head some false |
| Right then left | Full original tape restored; normal 2, decision 3; positions [0,1,0,1], visits {0,1} |
| Write true then erase | Full original blank tape restored at 4; positions [0,1,0,1,0]; visits {0,1}, interval Icc 0 1; no Boolean-output claim |
| Bool target control | Cardinal 6 |

Exact positional/set fixtures for the zero and one-write families explicitly use representative true / true-empty instances. The log does **not** separately emit the positional/set claim for each false/present-false combination. Counts and full endpoints cover all four one-write combinations. No expectation was changed.

The space consumers and some finite-run existential types were printed only readably. Their suppressed witness types/defaults were checked in the exact successful source, rather than claimed visible in expanded output. `printMove_run_with_space` retains the target witness but omits the source/count equality from that narrower public result.

## Scope

This remains checked research **outside the current 60 owners**. It establishes no ordinary-module installation, controller-specific final combined-machine result, whole-library acceptance, textbook qualification, or conventional NP theorem. No compiler, source/stage edit, deduplication, build-output change, or publication was performed for this reading.

The companion JSON supplies exact file hashes, source mapping, all query/output ranges, the five roots, contract assessments, fixture coverage and visibility limits.
