# Exact And root checkpoint

Source base: 8a1dea6af52405878701d040c1646791913f9698.
Pinned ConLeche: 8e166ca53cd1f864b63c13cc1d326d38316d00ea, clean private copy.
The unchanged preserved phase files compiled into private output before this run.
No shared checkout or dependency graph edits.

AndAcceptanceRoot.root proves exactly:
`nestRoot (fueledOps .verified 32) indsResult.1 ctx holes ctorResult.1 {} = .ok rootResult`.
The names refer to the original AcceptanceStages.Reference and
AndPositivityStages definitions. rootResult's exact ctorNfs push, field kinds,
crest and other NestState fields are retained. `post` names the exact state;
ctors_one and root_one are equations of actual upstream functions, not an
alternate checker. Small joins handle levels, hi, constructor substitution,
structural depth/fuel, inferred sort and closing the field telescope.

Historical initial run reported exit 0 and whole-file 0.837155s in the tool transcript.
The development runner subsequently overwrote AndAcceptanceRoot.log. The timings
below are historical transcript observations without their original retained log;
they are not the final reproducible validation/timing record. Exhaustive current
module audit: 107 safe roots, only Quot.sound/Classical.choice/propext.

| Declaration | Proof generation | Checked declaration insertion | Type rendering | Tree nodes |
|---|---:|---:|---:|---:|
| constructors | 9.468165ms | 180.794978ms | 1.620624ms | 6964 |
| root | 2.601852ms | 0.239047ms | 0.619402ms | 141 |

Generation measures type/proof elaboration, synthetic-metavariable synthesis and
instantiation. Insertion uses Lean.addDecl with Elab.async explicitly false;
it validates the proof against the declared type, including kernel checking and
normal environment-insertion overhead. It is not just Kernel.check inference
without expected-type comparison. Rendering separately pretty-prints the type
with pp.deepTerms.threshold=3 and caps displayed characters at1024. Node count
is Expr.sizeWithoutSharing, a tree count, not a DAG/memory-size measurement.
Import/startup and other lemma work are only in whole-file wall time.

Preserved failures: AcceptanceComposition-initial.log (symbolic Except.pure
unfolding gap) and AndAcceptanceRoot-option-failure.log (unsupported pp.maxDepth
option; declarations checked but file failed, not claimed as successful). The
second clean run corrects the option. No root timeout occurred with symbolic
composition. Historical timeouts cannot be attributed to kernel cost from this.

Statement review: bind_ok composes actual Except successes for arbitrary types;
ctors_one requires actual nodup/crest/type/sort/field/guard equations and retains
the full pushed output state; root_one sequences exactly one member's constructor
list and final empty tail. Concrete constructors establishes all premises from
existing certificates and small joins. The root is fully closed, with no checker
success premise or output-agreement assumption. No axiom/native_decide shortcut.

This checkpoint proves only the exact And positivity root. It does not yet prove
the complete And installer, Exists, helpers, actual emitted declaration family,
final environment, model construction or Cached.checkDecls acceptance. Root is
audited before expanding to those tasks. Development uses inherited pinned
upstream outputs; final fresh isolated dependency closure remains required.

## Retained reproducible run

Commit `b98c45a` was checked with global `Elab.async=false` and the same setting
on measured declaration insertion. Run ID `1794202357144968044-AndAcceptanceRoot`
retains inputs.json, the exact source, output.log and result.json in the #135
review evidence. Unlike the initial transcript observations, this log is not
replaced by later runs. Source hashes include the measurement helper and all
experiment sources. Whole-file time was 0.840400s; exit 0; the 107-root audit passed.

| Declaration | Generation | Checked insertion | Type rendering | Tree nodes |
|---|---:|---:|---:|---:|
| constructors | 9.034523ms | 0.955126ms | 1.583780ms | 6964 |
| root | 2.580351ms | 0.269323ms | 0.704991ms | 141 |

The global asynchronous-elaboration setting differs from the initial run, so
these numbers are separate observations, not evidence of a kernel speedup.

The complete And installer pass, including class reading, field-sort checks and
seed processing, also passed its 181-root audit in run
`1794202357988887396-AndInstallation`. Its final symbolic pass composition used
427 tree nodes, 3.423275ms generation and 0.479981ms checked insertion. This still
does not include the installer's recursor and projection-table tail.

For a repeatedly unfolded class-reading result, `checked_normal_form` records
both a reduced data definition and a kernel-checked equation from the original
expression to that definition. It uses proof-producing `cbv`; it does not execute
an unchecked acceptance test. The helper's separate normalization timing includes
checked definition/theorem insertion and code generation, and is labelled as
such. Kernel acceptance remains an equality of the actual checker operation.
A development failure from adding a generated definition without compiling its
IR is retained; using checked `addAndCompile` supplies the needed code-generation
registration. No upstream checker or main dependency changes were needed.

The exported cached-checker equation remains open in [#417](https://github.com/VladimirMarko/conaled/issues/417).
The pure-route model work does not establish it.

## Complete And installation checkpoint

`AndInstallerAcceptance.accepted` proves the actual pure operation
`checkDecl .verified (fueledOps .verified 32) [] eqEnv (.indDecl andPin 2) = .ok andEnv`.
`eqEnv` is the preserved equality basis environment. `andEnv` is the complete
predicted environment: the reversed stored And records followed by those equality
records, and exactly `[GraphEnvironment.andTable]`. Equality includes constructor
metadata, generated recursor type and rules, projection guards and the table.
There is no lookup-only or type-equivalence substitute for this final equality.

The recursor proof checks the stream constant, class normal forms, class
constructors, former types, generated prefix, generated constant, its definitional
equality to the stream type, and generated rules in the exact rule-less recursor
environment. `genRec_of_facts` sequences those actual operations symbolically.
`tail_of_facts` then composes index sorts, constructor insertion, recursor checks,
recursor insertion and projection-table checks. `block_of_facts` retains the
constructor/member uniqueness guard and actual pass result. The final declaration
proof also establishes ordinary-route dispatch, parameter count and block parsing.

[Committed measurement records](../../experiments/relative-graph/checkpoint-135-and/measurements.json)
retain source SHA256 identities, upstream revision, toolchain, invocation, run IDs,
all stage measurements and audit outputs. The earlier reproducible root run is
included separately with its original measurement-source hash. The final And
installer file compiled in 0.963 seconds and audited 177 safe roots. This is a
whole-file observation using prepared dependencies, not an isolated kernel timing
or a fresh dependency-closure validation. The records distinguish proof generation,
synchronous checked declaration insertion, type rendering, and normalization's
combined checked insertion/code generation. Expression tree node counts are
`sizeWithoutSharing`, not stored bytes, allocation or peak memory.

[Bounded failed attempts](../../experiments/relative-graph/checkpoint-135-and/failed-attempts.json)
retain exact attempted sources, identities, exits and capped diagnostics. Whole
recursor/type reductions exceeded generation heartbeats. A concrete composition
rewrite exceeded its wall limit without captured stage output, so that failure
has no attributed kernel cost. The successful symbolic composition is a new
attempt, not a reinterpretation of those failures.

Statement review for the checkpoint is [recorded alongside the sources](../../experiments/relative-graph/checkpoint-135-and/statement-review.md).
Exists, the native helper list, the actual emitted declarations, their complete
family environment and the relative model remain unproved at this checkpoint.
Final acceptance still requires the isolated fresh build and exhaustive upstream
and native dependency audits. Cached acceptance remains separately open in #417.

## Primitive stream continuation

`ExistsInstallerAcceptance.accepted` now checks the preserved Exists block after
And, producing exactly `GraphEnvironment.environment`, including its dependent
projection-table fields and levels. `PrimitiveAcceptance.accepted` composes the
actual pure Eq basis step with both installers from the empty environment.
The dependent witness/predicate positivity proof uses its computed walk fuel
1028 and keeps the complete output state. The same symbolic recursor and tail
assemblers apply without changed premises.

[Exists statement review](../../experiments/relative-graph/checkpoint-135-exists/statement-review.md)
and [source-bound measurements](../../experiments/relative-graph/checkpoint-135-exists/measurements.json)
record this later checkpoint. The native helpers and actual emitted family are
still outstanding here; this extends the earlier And checkpoint's scope without
turning either development run into final fresh validation.
