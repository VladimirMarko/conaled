# Cached missing-prerequisite diagnostics

This investigation concerns the diagnostic returned when the actual emitted
`graph_forward` loses its `Exists.elim` prerequisite. Its cached rejection and
position were already proved in #417. Normalizing the diagnostic text is a
separate question; this investigation changes neither the checker nor that
rejection theorem.

The selected checker remains ConLeche
`8e166ca53cd1f864b63c13cc1d326d38316d00ea`, Lean 4.35.0, at the original
`checkFuel = 2^62`. The three retained malformed-family controls and their
historical measurements remain unchanged. The new probe records are in
[checkpoint-418-diagnostics](../../experiments/relative-graph/checkpoint-418-diagnostics/manifest.json).

## The actual consumer

[CachedRejectionsMissing](../../experiments/relative-graph/CachedRejectionsMissing.lean)
uses `NativeHelper8.before`, the prefix without the actual `Exists.elim` helper.
It retains `EmittedForwardAcceptance.cv` and the full original emitted value.
Its pending record has position 11 and visibility 17.
[CachedRejectionsFamilies.missing_source](../../experiments/relative-graph/CachedRejectionsFamilies.lean)
identifies deletion of original declaration 11 from the actual canonical family.
[CachedRejections.missing_rejected](../../experiments/relative-graph/CachedRejections.lean)
proves that the exported cached checker returns its exact error at position 11.
The body/type mutations remain distinct controls at position 12.

The retained error is:

```lean
unresolvedConstsErrorL (strLitSupportedF (mkFEnv NativeHelper8.before))
  s!"value of {EmittedForwardAcceptance.cv.name}"
  EmittedForwardAcceptance.value
```

The formatter first tests whether String support is absent and a string literal
occurs. If so it returns a `notImplemented` string-support diagnostic. Otherwise
it tests for `sorryAx`, returning a different `notImplemented` diagnostic when
present; all remaining unresolved names produce `invalid`. These branches must
not be merged into one diagnostic category.

## Probe boundary

The accompanying runner copies the three `.lean.txt` probes into a temporary
directory and invokes Lean against an existing completed #417 closure. It checks
the historical candidate, upstream pin, compiler identity and the unchanged
control sources before probing. Its manifest records the reused object hashes
and provenance separately from the probe-source hashes. This is a focused check
with reused dependencies, not a fresh rebuild of the checker or the native
emitter.

`DeclarationProbe` queries the actual imported environment for declaration kind,
kernel value, equation-theorem discovery and compiler implementation replacement.
The source keyword `partial` alone is not the disposition's evidence.
`NormalizationProbe` deliberately attempts the literal-message equality for the
actual emitted body; expected failure is retained as a failed experiment, not
as an accepted declaration. `DiagnosticControls` executes separate runtime
category/text checks and proves only the downstream error-position observation.
Runtime output is not a kernel proof of scanner equality.

The result is the permitted **missing-interface disposition**, not a new
literal-message theorem. The actual imported declarations establish the boundary:

- `Expr.hasStrLitGo` is opaque. Equation discovery returns `none`. Its stored
  kernel value is a default inhabitant, not the recursive scanner computation;
  unfolding it is neither an exposed reduction rule nor a runtime-correctness
  argument.
- `Expr.hasStrLitGo._unsafe_rec` contains the recursive scanner and has
  `DefinitionSafety.partial`. The generic `isUnsafe` flag is false even here;
  the explicit safety classification matters. An exploratory equation query
  generated six candidate equations, each rejected by the kernel because a safe
  declaration must not contain that partial declaration. The final inspection
  reads its body and safety metadata without trying to install those equations.
- `unresolvedConstsErrorL` is a safe definition with `eq_1`; reducing the
  formatter still leaves the scanner test. `mentionsConstGo_spec` is a theorem
  for the different constant scanner. The implementation-replacement query
  returns `none`; that does not mean the scanner lacks compiled runtime code.

The final normalization probe fails with the exact residual branch
`if (Expr.hasStrLitGo … …).1 = true then ... else ...` on the original control.
All six runtime contrasts pass, including the actual message
`invalid: unknown constant in value of graph_forward`, unsupported strings,
`sorryAx`, ordinary unknown names, string priority and supported-string bypass.
The position observer theorem checks and its module audit reports six safe
roots with only `Quot.sound`, `Classical.choice` and `propext`. This observer
avoids changing the pin when a consumer needs rejection location; it does not
supply diagnostic classification.

[Results](../../experiments/relative-graph/checkpoint-418-diagnostics/results.json)
and the [complete probe log](../../experiments/relative-graph/checkpoint-418-diagnostics/probe.log)
retain four earlier attempts: an obsolete package-path startup failure, a
normalization heartbeat limit before restoring the historical local `mkFEnv`
evaluation rules, the rejected partial-equation generation, and a corrected
local name-constructor type mismatch. The timeout and type mismatch are not
evidence for the scanner boundary. The final three probes took approximately
0.92, 0.62 and 0.55 seconds, respectively; these are wall times for focused
invocations, not separate proof-generation or kernel-check measurements.

The runner's optional package relocation checks the unchanged historical Lake
manifest and each selected package Git revision. This run reused the main
checkout's matching external package outputs after the old worker paths had
been removed; their paths and revisions are recorded. Only the retained
checker/graph/native object closure is hashed here. External package outputs
are reused dependencies, not independently rebuilt or exhaustively rehashed.

Reproduce from the repository's direnv shell, using a new output directory:

```sh
python3 experiments/relative-graph/checkpoint-418-diagnostics/run.py \
  --upstream-run /tmp/conaled-369-orchestration/fresh-417-c4cbfde \
  --package-root /home/vlad/Code/conaled/.lake/packages \
  --output /tmp/diagnostic-418-new-run
```

The retained closure must be available. Follow the coordinator's serialized
CPU0/build-lock convention when running these probes.

## Proposed proof-visible interface

A total structural `hasStringLiteral : Expr → Bool` can provide visible equations
for every expression constructor. It must traverse fvar types, both application
children, binder types/bodies, all three let components and projection payloads.
String literals yield true; other leaves yield false. The old optimized scanner
would need a theorem at least of the form:

```lean
(Expr.hasStrLitGo {} e).1 = hasStringLiteral e
```

An arbitrary-memo variant needs a sound memo invariant. Existing
`Expr.mentionsConstGo_spec` in `Kernel/Inductives/StructParts.lean` demonstrates
that pattern for a different scanner; it does not establish the string result.
An unrestricted memo premise would be incorrect because skipped expressions can
hide strings.

With that bridge, the formatter contract can state three separate equations:
unsupported string first; otherwise `sorryAx`; otherwise ordinary unresolved
name. A future implementation might use the total scanner directly or prove an
optimized implementation equivalent. This report proposes neither an axiom for
the old partial function nor an automatic upstream pin change. A separately
proved total scanner would describe a new function until the bridge is proved.

A structured category observer plus an independently specified renderer could
avoid requiring literal text for downstream clients, but the current scanner
branch would still have to be connected to that observer. Merely renaming the
error cannot establish whether it is `invalid` or `notImplemented`.

## Preservation and scope

The original failed normalization attempt
`1794215737285461386-CachedRejectionsMissing` and successful exact-formatter
attempt `1794219732618624102-CachedRejectionsMissing` remain in
[the #417 failed attempts](../../experiments/relative-graph/checkpoint-417-rejections/failed-attempts.json)
and [measurements](../../experiments/relative-graph/checkpoint-417-rejections/measurements.json).
Their source hashes, proof-generation/kernel-check timings and exhaustive audit
evidence have not been reassigned to this investigation. See the original
[statement review](../../experiments/relative-graph/checkpoint-417-rejections/statement-review.md)
and [acceptance report](relative-cached-acceptance.md).

The new artifacts are diagnostic experiments outside the top-level Lean module
inventory. They introduce no library API, accepted scanner implementation or
checker completeness claim. #148 retains ownership of the separate execution
refinement/pin-port work; #195 retains reusable measurement tooling. No work on
#149 or #107/#108 follows from this disposition.
