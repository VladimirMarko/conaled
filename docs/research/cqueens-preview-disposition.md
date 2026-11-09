# Cqueens preview: source comparison and remaining route dispositions

The corrected first-row reflection route has a complete available source
closure. The [portable comparison profile](../../experiments/certified-nat-checker/README.md#reflected-first-row-comparison)
reproduces its 27 modules and audits the actual source comparison, while reusing
the previously accepted natural-number checker client. The separate native
profile freshly builds its full 31-module executable closure and reproduces
the canonical original-source numerical acceptance, as recorded below. The broader preview
contains incomplete kernel experiments and a missing generated CSP proof. Their
contracts and failure evidence are recorded here without repairing or adopting
them. This is an intake and comparison result under #137, not a resumption of
#149 or a solution of the unfinished sixteen-queens theorem.

[Route inspection metadata](../../experiments/certified-nat-checker/evidence/route-inspection.json)
records exact checkpoint-233 member paths, hashes, inspection scopes and failed
run results. References below use its short IDs. These are preserved source
contracts and recorded outcomes. The comparison and native profiles compile
their selected closures; the kernel and CSP contracts are inspected statically.
The inventory is finite and tied to this snapshot, rather than a claim to have
accepted every historical experiment or independently rechecked upstream kernel
metatheory.

## Corrected reflection and source comparison

The selected `FirstRowReflection` is the corrected 10,494-byte source, SHA-256
`da7315a78be246379d44b8a96af917f1a6d251ef8a09fc6f966e27367103f1cf`.
The runner replays its three proof-only edits from the 10,397-byte predecessor
and verifies intermediate hashes. The old source failed with an unavailable
variable, an unexposed map lambda and unused simp arguments. Its failure remains
preserved. The corrected source was subsequently accepted by the supplied gate;
treating the earlier failure as its current status would be incorrect.

Reflection sends legal one-based columns q to `n+1-q`. Involution and distance
preservation require column membership because Nat subtraction truncates.
`moves_reflect_perm` preserves a permutation of legal choices, and subsequent
length equalities preserve every occurrence. They do not assert ascending-order
preservation. `paired_sum` accepts any natural-valued symmetric column weight,
doubles the lower half and counts an odd center once. `solutionsQ_empty_sum`
requires a positive board size: the zero-board source has one terminal empty
board whereas a sum over zero columns is zero. [reflection-corrected]

The source adapter uses the original `encode [q]`, mask and depth through the
exact masked evaluator. Its child-count law requires `n ≤ 16` and legal q.
It composes the Nat/Word16 refinement and original `stateCount_encode` theorem;
it does not substitute a hand-written reflected bit state. UInt64 saturation
and input checks retain the exact Nat fallback. Aggregation and doubling use
Nat. The final wrapper handles zero separately, applies the optimization to
positive n at most sixteen, and falls back outside that range. Universal
`cqueens_eq` therefore means equality to the original fixed-Word16 source for
all Nat inputs, not arbitrary-width mathematical counting. [reflection-source]

The new `ReflectionClient` reuses `CheckerClient.endpointSquare`, its identity
Nat representation, successor consumer and `Squares.compose`. The original
canonical/rejection cases remain imported. New cases use the generic paired-sum
law for odd/even constant weights, the zero sum, and a concrete failure of
unrestricted involution. The source comparison passes through the actual
endpoint law. No new shared interface, mandatory IR or alternate kernel is
introduced. [Statement review](../../experiments/certified-nat-checker/statement-review.md)
covers the new claims.

The archive records 23.36454244100605 seconds for the corrected complete native
gate: 24 fresh experimental modules/C outputs, link and external numerical
acceptance, using 21 prepared objects for seven original modules. The external
call took 7.666948686004616 seconds; peak RSS was 796,004 KiB. These are supplied
single-run measurements, not local repeated benchmarks. The corrected report
explicitly leaves concrete Lean acceptance, the stock numeral theorem and kernel
extension false. The comparison profile itself does not run C generation, linking,
native CLI or n16; the separate native reproduction is recorded below. [reflection-success]

## Fresh comparison evidence

The [recorded fresh validation](../../experiments/certified-nat-checker/evidence/comparison-validation.json)
identifies the measured code candidate and every runner/client input. The
comparison run compiled 29 archived modules: the complete 27-module source
comparison plus two modules needed to reuse the accepted checker client.
Together with `Squares`, `CheckerClient` and `ReflectionClient`, the exhaustive
audit covered 32 modules and 1,462 safe declarations, with zero unsafe exclusions
and only the three permitted axioms. The default checker profile was also
rebuilt with the extended runner and retained its 22-module/1,263-root audit.
Both runs used fresh private outputs, one compiler/thread, the 8-GiB virtual cap,
120-second per-process deadline and 20-minute total deadline.

The measured code precedes only the commit recording these measurements; final
candidate receipts belong to the review handoff. All eight black-box tests
passed: four selection/extraction controls and four reused executor/auditor
controls. This is fresh proof compilation and exhaustive audit, not a native
checker benchmark. No kernel or CSP route listed below was compiled by this run.

## Operational recognizers do not prove installation

`DefinitionPins` records exact internal name, empty universe parameters,
annotated type and stored definition body. `inspectDefinition` checks those
fields in an actual environment; `inspectProgram` combines the three counting
program definitions. This is useful finite recognition, not annotation
correctness or environment validity. [installed-guards, lines 34–199]

The Nat recursor recognizer checks stored rule lists, constructor metadata,
universe arity and instantiated annotated types/RHSs. Arithmetic recognition is
weaker: `ArithmeticChecks` checks eight `natOpStored` flags, whose contract is
definition kind, not an arithmetic body certificate or `NatOpGuard`. The source
explicitly preserves this distinction. `OperationalPins` combines those
operational premises. Its successful recognition cannot be relabelled as a
successful cached check. [installed-guards, lines 223–425]

The prefix recognizer uses `stored.consts.drop (length-visible)` because the
stored environment is newest-first. Merely inspecting a restricted `FEnv`'s
unchanged full `.env` field would inspect the wrong environment. Its extension
lemma proves the expected tail identity when a genuine extension equality is
supplied; it does not construct an install run or prove index uniqueness.
[installed-guards, lines 450–494]

The preserved upstream `InstalledEnv` carries an actual `InstallRun` from empty
environment and memo state. `GroupChecked` asks for the selected pending record's
original `checkPending` run from fresh state; out-of-bounds indices have no
pending obligation. `FullyChecked` includes installation plus every pending
record's check, and `fullyChecked_checkDecls` connects that package to the
actual fold. Thus one recognized record or successful local evaluator does not
provide `FullyChecked`. `checkPending_run` additionally requires verified mode,
`EnvWF`, lookup agreement, scoped inputs and `CSOKF`, and concludes a pure check
at some fuel. None of these premises comes from the column-reflection theorem.
[installed-api, lines 212–299 and 538–564; installed-simulation, lines 153–160]

The preserved last-mile assessment identifies a legitimate conditional route
through the upstream `groupChecked_of_run`. It also states the missing concrete
installation, annotation/source correspondence, exact query fuel and returned
state obligations. The original pending checker uses fixed fuel; eventual
success above an unspecified threshold is insufficient. An empty-state success
does not establish success in the state left by preceding annotation/inference.
These are source/contract gaps, not evidence that the generic soundness theorem
can be used to assert a closed host-Lean numeral. This slice supplies no such
instance and does not import the archived kernel owners. [last-mile]

## Complete failed selections remain failed

| Frozen selection | Recorded result | Contract inspected and disposition |
| --- | --- | --- |
| Original word112 | 79 accepted reports, 93 observed; Transposition failed; Adjacency unstarted | First failure is a transport/type mismatch at Transposition line 220. Retain the source key and failed scope. |
| Transposition-repaired word112 | 93 accepted, 112 observed; all 19 Adjacency reports rejected | Exact marker/key/payload routing still lacks a successful complete selection. Do not transfer prefix acceptance. |
| Equation-repaired Interpreter185 | Core2 and Cached6 passed; all 177 Interpreter reports rejected | Actual continuation equations fail at physical lines 3097, 3121 and 3137. No complete query, installed-check or normalization result follows. |

The inventory records each source fingerprint, report hash, module status and
resource result. Diagnostic log bytes were checked against the corresponding
report hashes. These are supplied failures, not reruns. Error-recovery
`sorryAx` in failed diagnostics is not accepted proof evidence.

`checkAdjacency` checks a high-data bound, the first-record definition marker and
whole-word copies for subsequent request records. Its intended conclusion
retains the full key and payload, with a positive marker stride even at zero
field widths. The final source-row transport still requires definition and
padding validity. The actual failed scopes concern the zero-bit Boolean goal,
unused simp arguments and addition-by-zero presentation; those errors have not
been repaired here. Even a repaired generic routing theorem would not itself
check a concrete queens certificate. [word-adjacency; word-transposition]

The Interpreter's iota contract explicitly supplies recursor/constructor/rule
pins, level arity, prepared-major run and sequential type/RHS query results with
their returned states. Its claimed result is an actual verified-mode stateful
operation. In the failed proof, distributing an unknown Boolean conditional
across state application was not definitional equality, and the final change
had not discharged preceding checks. Weakening the runtime, assumptions or
state order would be a different result. No such change is part of intake.
[interpreter-contracts, lines 492–681; interpreter-physical and diagnostics]

## Strong-CSP source and missing generated evidence

`StrongResidual.checkCertificate_sound` checks entries from an empty known list
and then the root proof. References require previous valid entries. The entry
structure supplies a problem and proof, not a proposed numerical count.
`checkChildren` matches every choice occurrence with a child, rejects length
mismatches and sums every repeated choice. Branching checks a permutation of
actual domains. Soundness needs the stated compatibility symmetry; it does not
replace multisets of choices with sets. [strong-checker]

The original-source bridge retains row tags and column labels. Its table/count
agreement requires the correct row count, duplicate-free source domains and
legal columns, checked by `checkTable`. Normalization separately checks singleton
removal and finite compatibility agreement for relabelling. These premises
explain why a generic CSP result alone is not the original source theorem.
[strong-source, lines 148–199]

The fixed target imports `StrongCSPGenerated` and expects its `source_cqueens`
theorem to prove actual original `cqueens 8 = 92`. No file with that generated
module name exists in the preserved archive. The latest handoff reports a
source-reviewed producer and support source, but no generated mathematical data
or executed producer result. The 25-owner source endpoint is also recorded
uncompiled. This is a specific missing proof artifact and unexecuted selection,
not an artifact-discovery failure and not a reason to manufacture a success.
No strong-CSP generator or certificate has been run by this intake. The separate
corrected reflection native route is reproduced below.
[strong-target; checkpoint-scope]

## Value assessment and finite completion boundary

The reusable value shown here is source-certified numerical evaluation,
reflection with multiplicity-preserving symmetry, exact guarded fallback, and
composition with an existing ordinary Lean client. These capabilities work
without owning a growing Lean fragment checker. The kernel candidates offer
more specialized operational caching and packed-check infrastructure, but their
current complete selections do not establish the installed end-to-end result.
A source-restricted adapter with an existing upstream proof contract remains a
smaller justified commitment. This evidence does not prove that a future kernel
extension has no value; it does not justify adopting one now.

For the preserved preview, this report supplies finite contract/status
dispositions for the named remaining routes. It does not promise to repair
failed proofs, generate missing certificates, reconstruct every textbook module,
or independently verify every upstream kernel theorem. The previous independent
checker experiment and accepted native Nat-checker client remain available;
there is no need to invent another helper ticket merely because a theorem is
generalizable. The full source-comparison reproduction and its precise receipt
are separate from the supplied external timing claim.

## Fresh native reproduction

The supervising originator required a local reproduction of the supplied native
acceptance as ISSUE137-SPEC-001. The `native` profile now rebuilds all 31 selected
sources, including the seven prerequisites whose objects the historical gate
prepared separately. The corrected reflection proof and scoped inverse-source
correspondence are unchanged. No archived script, prepared object or executable
is reused. The full fresh source audit reports 31 modules, 1,338 safe roots,
zero unsafe declarations and only `Quot.sound`, `Classical.choice`, `propext`.

The [durable measurement](../../experiments/certified-nat-checker/evidence/native-validation.json)
records candidate `ce54e975990b909831774fb6e3231cf7d5516a79`, all source and
output hashes, compiler/runtime identities and all 109 commands. The complete
run took 37.57 seconds. Source proof compilation took 10.35 seconds; exhaustive
audit execution took 1.89 seconds. Fresh C generation took 10.10 seconds,
including repeated frontend checking; C compilation took 7.72 seconds and
linking 0.47 seconds. These stages do not have the same boundary as the old
23.36-second historical gate, which excluded prerequisite object preparation.
No speedup over another route is inferred.

The executable accepted exactly these four arguments:

```text
ADWH.Chapter15.Queens.BitRepresentation.cqueens 16 = 14772512
```

Its stdout was exactly `ACCEPT ` followed by that canonical claim and a newline;
exit status was zero and stderr empty. The native process took 4.68 seconds and
peaked at 19,872 KiB RSS. The whole reproduction's maximum child RSS was
1,586,632 KiB, within the 8-GiB virtual-address cap. A zero-board claim with value
one passed. Wrong value, source label, operator, noncanonical numeral and extra
token cases each returned `REJECT` with exit one and empty stderr. Output hashes
and actual statuses are in the receipt, separate from the universal proofs.

Lean 4.35.0 has the same source commit as the historical compiler, but the local
binary differs. The local Nix `leanc` wrapper uses the shell's GCC, explicitly
bound through `LEAN_CC`. The receipt binds the native tools, headers/libraries,
27-path Nix compiler closure, seven dynamic dependencies and generated binary.
The executable digest is
`a529e8f771e71686558520fb0dcd0ee04c9edbc608fe4e1ad4cf56c88d038bc1`.
Two earlier attempts passed the proof audit then failed at native inventory
setup (command-path resolution and a Nix JSON warning). Both are retained;
neither was a proof failure or successful native reproduction. Caps were not
increased.

This observation trusts Lean code generation, C compilation/linking, the runtime
and host execution. It does not produce a stock-kernel numeral theorem, prove a
concrete Lean acceptance equation, or establish binary correctness. The existing
checked source bridge binds the endpoint to original fixed-Word16 `cqueens`;
the CLI has no evaluator-selection argument. The missing strong-CSP artifact
and failed complete kernel selections remain inspected findings, not successful
implementations. Optional kernel adoption, repair of those selections, the stock
n16 proof, #149 reconstruction and #107/#108 theorem selection remain outside
this task. Root and supervising originator retain the full-issue closure decision
and must review the exact final reproduction receipt.
