# Integration147 source plan: ordinary wrapper and print-and-move execution

This is a source integration plan for root, not an installed source increment,
candidate capture, compiler result, independent review, or acceptance action.
Only files in `work/integration147-preparation` were created for this task.
Delimiter research, including the running repair3 successor, is outside this
plan regardless of its later result.

## Recommendation and scope

Add three reusable owners to the current 60-owner scope, giving a proposed
63-owner scope. Keep every current owner. Preserve the current native Boolean
decider module and all controller proofs; do not retrofit them during this
bounded extraction. Append the two checked fixture bodies to the existing
`Examples/TuringSimulation.lean`, and add the three new owner imports to
`SquareApplications.lean`.

| Proposed owner | Complete checked bodies | Direct imports to add |
|---|---|---|
| `Applications/Resources/TuringSimulation/OrdinaryPackage.lean` | Both `Resources.TuringSimulation.StackToTape.OrdinaryPackage` blocks from successful `GenericOrdinary144b.lean` | Current `MarkedInput`, `FiniteStackToTape`, `SingletonOutput` |
| `Applications/Resources/TuringSimulation/PrintMove.lean` | Complete `PrintMove` adapter and `PrintMove.Trace` blocks from successful `ConventionalNative144a.lean` | The six Mathlib imports listed in `OWNER_PLAN.json` |
| `Applications/Resources/TuringSimulation/PolynomialDeciderPrintMove.lean` | Complete `Resources.TuringSimulation.PolynomialBooleanDecider` consumer block from that conventional source | Current `PolynomialDecider`, new `PrintMove` |
| Existing `Examples/TuringSimulation.lean` | Append complete `Examples.TuringSimulation.OrdinaryPackageCases` and `Resources.TuringSimulation.PrintMove.Cases` blocks | New `OrdinaryPackage`, new `PolynomialDeciderPrintMove`; Mathlib `Fintype.BigOperators` and `Fintype.Prod` for the literal cardinality case |
| Existing `SquareApplications.lean` | Preserve the body and all imports; add imports of the three new owners | The three new modules above |

All namespaces stay exactly as checked. In particular, the conventional cases
retain `Resources.TuringSimulation.PrintMove.Cases` even though their file owner
is `Examples/TuringSimulation`. No public declaration is renamed. Both new
generic theory owners have no rotation-certificate imports. The decider bridge
also has no rotation dependency.

The adapter and its target trace belong together: both describe the actual
combined print/move step. The bridge is a separate third owner so adding it does
not make the existing native-decider contract import a conventional target model.
Folding the bridge into existing `PolynomialDecider` would save one file but
broaden the dependency boundary for every existing native client. Four files,
with a separate `PrintMoveSpace`, are possible but not needed for these complete
cohesive blocks. This three-owner plan is additive and acyclic.

## Exact source selection and extraction rules

`OWNER_PLAN.json` gives exact source-file hashes, inclusive line ranges, byte
offsets and body hashes for all seven selected complete namespace blocks. The
successful combined files are authoritative. In particular, the final literal
24-symbol proof is selected from `GenericOrdinary144b`, not the earlier repair1
file with its subsequently repaired proof ending.

The generic body ranges are 1883–2012, 2032–2265 and 2283–2530. The conventional
ranges are 164–628, 638–898, 907–1195 and 1206–1335. Retain every declaration,
private helper, instance, proof, local `omit`, attribute and section in each
selected block. Preserve `autoImplicit false` and `warningAsError true` for the
new owners and appended cases. Put all imports before module documentation.
Historical research headers may be replaced with truthful API documentation;
the selected namespace bodies themselves need no rewrite.

Do not copy either combined source wholesale. Their prefixes contain existing
owners, historical research assembly and imports used for that assembly.
The existing `SingletonOutput` already contains the exact generic package-halt
support block used by the successful generic probe. The current native decider
owner and its existing constant-machine cases also contain the exact prefix
bodies used by the successful conventional probe; these occurrence checks are
recorded in `OWNER_PLAN.json`. Reuse those owners once. The obsolete research
import names `MarkedInputRun` and `SingletonOutputSupport` must resolve to current
`MarkedInput` and `SingletonOutput`, respectively; no new compatibility files
are proposed.

Every `open` in a selected block is within its namespace. Appending complete
blocks after the existing file's closing namespace preserves that scoping.
Private generated declaration names may acquire the new module identity during
ordinary compilation; that is an ordinary-module validation obligation, not a
reason to delete or rewrite their proofs. `Bind.bind` stays explicit throughout.

## Contracts and fixed observations to preserve

The ordinary package fixes `tm`, all-index alphabet finiteness when needed,
`outputLetter` and `fallback` before the raw word. It preserves the exact
`Package.controlInhabited tm`, including supplied `tm.main` and
`tm.initialState`; its own start is the prelude control. The raw tape is the
length-preserving injective nonblank letter map. The existing executed prelude
pays one step for empty input and `N+2` for positive length; it preserves the
complete reflected encoded tape and orientation.

The package's run consumes an actual bounded native `EncodedRun` and the full
`TrCfg (haltList tm [answer]) target`. The full relation supplies the singleton
tape and blank tails before the actual output write. The emitter reads the
designated output track, applies `getD fallback`, then `outputLetter`; on a
proved halt row its result is independent of fallback. The live output bound
is `preludeSteps raw + B + 1`, and its stored count remains
`1 + (before.steps + preludeSteps raw)`. The distinct outer-none run adds one
to the live stored count and has bound `preludeSteps raw + B + 2`. Native `eval`
returns the same complete singleton. The distinct-store premise is retained
where the empty input-track observation needs it; it is not silently added to
all generic statements.

Retain the `Option Bool` input/`Bool` output fixture, 24 working symbols,
supplied true main/register, present delimiter `some none`, present false
`some (some false)`, empty input, exact prelude counts 1/3/5, complete orientation,
false output with true fallback, true output with false fallback, and the
separate one-write/next-none observations. The arithmetic 7-step/allowance-10
fixtures retain stored counts 9/11/13 and bounds 12/14/16. They are count-formula
fixtures, not an assertion that this halt-only fixture has a complete encoded
source run from arbitrary input to those outputs.

The conventional target executes `(T.write letter).move direction`. Its
nonterminal controls are normal and returning copies of source control; accept
and reject are terminal, with total `delta` on the nonterminal subtype and
cardinality `2 * card Q + 2`. Native moves cost exactly one target action;
stationary writes cost exactly two and include the actual rightward excursion.
Normal boundaries retain the whole native tape. `simulationTime` sums actual
selected command costs; the lifted native witness retains this count, bounded
by twice its stored source count. A proved stopped Boolean answer costs one
additional real action, ends with the entire source tape moved right, and has
bound `2*B+1`, including the zero-source-step case. Outer none is another
observer step.

Target trace bounds inspect every actual target prefix, including write
excursions and the final decision movement. Preserve `max N 1 + U` and its
paid-run specialization `max N 1 + (2*B+1)`. The generic `N` parameter does not
assert arbitrary starting tape support lies in those N cells. The polynomial
decider consumer specializes to its literal mapped input length. It preserves
fixed blank/start/bit injection and the polynomial `2 * d.time + 1`, actual
native and target witnesses, stopped Boolean evidence and complete target tape.
The explicitly supplied equality instance remains a fixed parameter. The
classical existence consumer stays explicitly noncomputable; no executable
enumerated transition-table export is claimed.

Preserve all conventional fixtures: zero-step false/true decision at1 and
outer none at2; four empty/present-false one-write cases at normal2/decision3
and outer none4; supplied true start against ambient false; right/left whole
tape return; write/erase whole blank tape with its real visit to cell1 and no
Boolean-output assertion; the exact position lists, visited sets and control
cardinality6. Existing native live2/none3 and genuine native-init Peek
live5/none6 remain different observations with unchanged expectations.

## Queries and direct clients

`QUERY_PLAN.json` lists exact retained query fragments and all new query names,
including their original commands and source lines. Preserve the current C146
350 readable, 19 expanded and 23 root observations, including all18 older
controller clients and the cleanup-prefix public type whose unused binder was
removed. Preserve the successful generic 80/4/4 and conventional 159/3/5 query
sets. Their concatenation is a planned **589 readable, 26 expanded, 32 selected
root observations**, without dropping repeats or changing original commands.
These are planned observations of installed modules, not new execution evidence.
Selected roots complement the required exhaustive module-origin audit.

Direct-client reading priorities are the entire ordinary fixture namespace,
the conventional fixture namespace and all eleven checked
`PolynomialBooleanDecider.printMove*`/classical bridge declarations. Read
`EncodedRun`, `runInTime`, `runInTime_steps`, `nextNoneRun`, `eval_of_run`,
`PrintMove.delta`, `finite_run_exact`, `decide_of_native_run`,
`Trace.paid_run_interval`, `printMove_run` and `printMove_run_with_space`
with their actual supplied instances and full endpoint types. The existing
expanded observations cover the principal default-sensitive boundaries; use
source definitions or further explicit printing if an actual emitted type
hides a consequential argument. Do not describe unprinted structure fields as
having been inspected.

The concrete conventional fixtures exercise `writeRun`, `decisionRun`,
`decide_of_native_run` (including zero time), actual move composition and actual
target trace observation. The generic decider bridge consumes the actual
`d.run` witness, rather than adding an assumed time field. The existing
rotation `ordinaryPolynomialDecider` remains an unchanged native client.
Instantiating the new bridge at that controller, or refactoring its ordinary
run through `OrdinaryPackage`, would be a later explicitly typed client change
to compile and read; no such new body is selected or claimed checked here.

## Normal-module validation order

Root first establishes the supported original-B/M baseline for all63 owners,
before installation. Keep original B
`bc95f503ccbf043136c6699992388f750270e8e6` and incorporated M
`ec4949a94ed70084d70f5b273fb0cc6dca8b2647`. No baseline is created by this plan.

1. Resolve the existing whole139 output-writer status through its actual
   receipts and retain its failures/unknowns. Preserve root's sole writer and
   sequential-probe discipline; do not copy or inject project products.
2. Validate the unchanged native dependency owners under their ordinary module
   names: `FiniteControl`, `FiniteStackToTape`, `TapeReflection`,
   `SingletonOutput`, `MarkedInput`, and `PolynomialDecider`, with their normal
   dependency closure. Existing source-identical products are usable only under
   the repository's supported provenance and integrity rules.
3. Compile new `OrdinaryPackage` after those dependencies, and new `PrintMove`
   with its Mathlib dependencies. Compile `PolynomialDeciderPrintMove` after
   `PrintMove` and existing `PolynomialDecider`. This exercises the proposed
   module separation that the combined research probes did not validate.
4. Compile the complete modified `Examples.TuringSimulation`, then retain and
   validate complete controller client modules (including
   `Examples.RotationCertificateFrontEndStreamMachine` and
   `Examples.RotationCertificateFrontEndStreamTapeMachine`) and certificate
   correspondence clients. No unchanged client body is replaced by checks only.
5. Compile the aggregate import graph. Read the planned declarations and
   selected roots from matching immutable source. Any no-output concatenated
   probe remains a development check and does not replace these module checks.
6. Complete matching whole-library validation and exhaustive audit, immediate
   nonrepairing verification, supported final comparison and the same existing
   Standards/Spec review loop. No acceptance result or reviewer approval is
   supplied by this plan.

## Documentation delta after an actual installation

The likely documentation change fits existing owners: append a bounded source
integration entry to `docs/research/fdsa-rotation-certificate-preparation.md`;
update only the five active CTB/coverage gates already maintained by root.
Identify the new63 scope and actual observed source/check status. Replace the
current statement that generic/conventional research remains outside60 only
after it is actually installed into the prepared scope. Record the already
observed C146 combined pass and the two research passes with their exact
receipts, while retaining all ordinary-module, whole-check and review gates.

Preserve every other decoded JSON value and all qualification counts, all96
controller domains, 84 independent cases and 81 positive closed fixtures in
their current accounting. Additional retained generic/conventional fixtures
are separate evidence; this extraction does not reclassify book rows or claim
NP, exact rotation diameter, a completed certificate interface, sharp space,
or a finite exported transition table. Requirements1–15 and all current
timing/controller/ordinary-I/O addenda continue unchanged. Delimiter
serialization and conventional certificate-class/NP correspondence remain
separate work. Keep every historical UNKNOWN, one complete checkpoint archive
per cutoff, and no local progress updates to issue558.

## Evidence and reading limits

`INPUTS.json` binds the selected successful sources/results/logs, their reading
records, fixed expectations, current60 owners and relevant local guidance.
All60 current source hashes were checked against immutable C146. The three
successful results report unchanged bound inputs and exit0. Root's generic
reading record and the conventional implementer's reading record were used
as prior output-reading evidence; this planner did not perform a replacement
independent review or reread every log line. The selected new source bodies,
fixed expectations, public contract and applicable owner boundaries were read.
The complete current60 source bodies were hashed, not all reread.

An initial overbroad filename search enumerated some `conaled-public` paths.
No contents there were read, and nothing there was written. All subsequent
reads were restricted to the named research/review records and the current
`conaled` sources. This incident is recorded rather than claiming no pathname
access occurred. The plan contains no dependency on those public working files.
