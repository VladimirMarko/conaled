# Resumed dependent-authoring repair: structural comparison

This is partial evidence for [#107](https://github.com/VladimirMarko/conaled/issues/107),
starting at `a95a5efd8370b9005fcf4a3b2bdac5f0dfc3bff2`. It is not a successful
repair, a general associativity derivation, or a frozen interface for #108.
The [prior checkpoint](dependent-congruence-repair.md) and the #106 archive
remain unchanged apart from a link to this comparison.

The bounded experiment confirms that **retaining a fixed open operation makes
its repeated application structural, but does not by itself identify that
operation with a newly constructed named operation**. The newer guarded source
boundary already provides the latter comparison for its own concatenation.
Its recipe differs from the legacy one. That makes a deliberate migration worth
considering before further investment in legacy semantic-annotation coherence.

## Checked comparison

The isolated [experiment sources](../../experiments/dependent-congruence-resumption/README.md)
apply existing rules rather than adding an author API. They use stock heartbeat
limits, existing source constructors, and the current toolchain.

| Case | Result | Remaining boundary |
| --- | --- | --- |
| Fixed concatenation template | Constructs the actual typed environment `y, p : x = y, z, q : y = z`; source substitution composition compares applying then reindexing with applying the composite argument map. | The template was fixed in the original context. |
| Dependent-tail caller | Retains the generic `q : y = z` and adds `b : fiber x`; no path is specialized to reflexivity. The general composition caller also accepts projections from arbitrary typed telescopes. | Does not normalize a newly reconstructed command's annotation. |
| Template computation and congruence | Reuses generated J beta and substitution congruence. The latter consumes an actual generated argument conversion. | The compared result remains in the original pulled-back motive. |
| Fixed transport template | The same generated substitution-composition rule applies. | A separate theorem is needed for fresh construction. |
| Fresh named transport | Existing `transport_code_reindex` supplies that separate all-model comparison. | Its proof contains the transport-specific presentation argument. |
| Fresh named legacy concatenation | Existing `concat_raw_reindex` compares raw syntax. The retained diagnostic rejects using `rfl` for the analogous semantic annotation comparison. | This is a missing derivation in this experiment, not an impossibility result. |
| Guarded concatenation | Existing `Tm.concatSub` supplies a generated equation to freshly reconstructed concatenation under arbitrary typed substitution. | It eliminates the right path; legacy concatenation eliminates the left. |
| Guarded contextual command | Existing `Command.comparison` constructs both typing derivations and their generated equation for arbitrary finite dependent tails. | It is not a translation of the legacy associativity argument. |

No ordinary call in these probes supplies a manual model-code equality. The
fixed-template comparison achieves that by keeping its result in the
pulled-back type. It does not make the stronger old-client requirement vanish.
The diagnostic separately displays the old client's actual desired equation:

```text
reindex(concat p q, σ).code
  = concat(reindex p, σ, reindex q, σ).code
```

Both sides retain arbitrary input paths and an arbitrary typed substitution.
Their raw expressions already agree. The unresolved comparison involves the
semantic codes of the two J presentations. A theorem about their interpretations
in ordinary groupoids alone would not prove the quantified annotation equality,
which ranges over every supplied contextual model.

The fixed template remains parameterized by its original context and point.
This experiment has not built a global operation library over one universal
argument context, nor proved that every freshly reconstructed command equals an
application of such a library. Doing that would require the missing bridge,
including the construction and comparison of its dependent argument contexts.
Calling an arbitrary substituted term a template does not supply that bridge.

## Subsequent work that changes the choice

[#315's source-boundary assessment](dependent-judgment-representation.md)
already adopted model-independent guarded judgments for later constructor and
author trials. Its `TransportReindexing.lean` derives fresh transport and
concatenation equations. `Templates.lean` derives command comparison with both
operand typings. These are existing checked mechanisms, not a proposed future
frontend. The probes here check their actual current callers.

They do not silently recover the old recipe. The same assessment explicitly
records that guarded concatenation eliminates the right path and the legacy
source eliminates the left. Their ordinary-groupoid observations agree by
separate semantic theorems; that agreement cannot identify selected higher
certificates in arbitrary models. The requested legacy associativity witness
therefore cannot simply be replaced with a theorem about the guarded operation.

The other approved inputs have narrower reuse:

- `Applications/Elaboration/Syntax.lean` separates source substitution from
  interpretation and proves their compatibility. Its contexts are lists of
  fixed sorts, so it supplies no dependent J presentation comparison here.
- `MixedSetting.pullbackEquiv` and its section/composition theorems construct
  comparisons for Set-family presentations. They do not identify the
  universally annotated legacy J commands. Reusing their design is different
  from applying their theorem.
- Existing groupoid route consumers still test label-sensitive transport and
  source-derived transport composition. A direct functor composition theorem
  would bypass the missing source associativity derivation.

## Recommended decision: a bounded client migration

Prefer authoring the known regression through the already adopted guarded
boundary, while preserving its mathematical recipe and recovering its existing
consumers. This is a proposal requiring a scope decision, not work already done.
It changes which public interface #108 would test. It does not require a general
Agda translator, a shared AST, a universal frontend, or retirement of `Typed`.

The migration's acceptance should explicitly require:

1. Construct a guarded **left-path** concatenation recipe with the retained
   dependent tail, or translate the relevant legacy recipe with its erasure
   and interpretation preserved. Merely using the existing right-path operation
   and matching its ordinary-groupoid value is insufficient.
2. Complete the same general source associativity argument, retaining arbitrary
   `p`, `q`, `r` and dependent binders. Construct its reflexive branch and source
   conversions; do not inject target associativity as a source proof.
3. Derive substitution and argument congruence for that recipe, including
   freshly reconstructed applications and dependent tails, without caller
   model-code equations. Exercise reuse in transport composition.
4. Interpret that same retained argument through the guarded model soundness
   route and recover general ordinary-groupoid and labeled C4 observations.
   State any translation back to legacy `Typed` separately: no such general
   translator currently follows from this experiment.
5. Keep the old first proof, ordinary/mixed consumers, faithful/ineffective
   observations and #106 archive intact. Retain direct interfaces wherever
   useful. Record the exact relationship between old and new selected witnesses.
6. Finish statement review, fresh-source build, exhaustive axiom audit,
   independent reviews, supported-operation diagnostics and a reviewed public
   handoff before #108. Select no fresh theorem during this repair.

This preserves #107's mathematical and consumer obligations but would revise
its implementation-specific requirement to finish the archived `Typed`
derivation through that interface's existing soundness. The new derivation
would instead use guarded source judgments and their already constructed
soundness, with an explicit old-client recovery obligation. That change must
be decided openly; it cannot be disguised as satisfying the old freeze.

The alternative is to retain the original acceptance unchanged and complete
reusable legacy presentation coherence. Its next obligation is precise:
compare the pulled-back concatenation telescope, motive and branch with the
fresh `ConcatFrame` construction, factor the endpoint maps, and apply J
substitution. That result would serve retained legacy callers regardless of
frontend choices. The experiment does not show this route impossible or bound
its remaining effort. It does show why fixed-template composition alone is
insufficient to justify choosing it as a cheap repair.

## Statement review and validation

The successful probes are applications of existing generated rules and
comparison theorems. Their quantified inputs are typed paths, substitutions
and telescopes; none assumes the desired fresh-concatenation equation. The
congruence probe intentionally requires a generated argument conversion.
The nonempty-tail example is constructed from the existing generic context,
not postulated. Its source types retain dependence on the earlier endpoints.
The guarded comparison's assumptions are source judgments, not semantic
annotations. These checks establish the stated relative callers, not a new
calculus adequacy result or a whole-repository audit.

Both successful files were checked separately with `direnv exec . lake env lean`.
The two missing guarded dependency targets were built with stock Lake first.
Every named declaration in the probes was inspected with `#print axioms`; the
retained outputs contain only permitted foundational axioms or no axioms.
The deliberately failing file reports the expected non-definitional annotation
comparison. The experiment README records exact reproduction commands.
No integrated Lean source was changed. No fresh full-library build, exhaustive
project audit, independent review, or #107 acceptance is claimed by these
focused checks. Parent orchestration owns review of this partial checkpoint.

Work consisted of constructing these callers, checking the stronger fresh
operation endpoints, and inspecting the existing alternative. One initial
rewrite needed `eliminationSub` unfolded before the existing generic raw
substitution theorem applied. The guarded caller needed the contextual
namespace qualified to avoid its structural namesakes. These are elaboration
repairs, not mathematical obstructions. No productivity ratio was measured.
