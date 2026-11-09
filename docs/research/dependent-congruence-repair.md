# Dependent congruence repair: incomplete implementation

Current status (2026-11-09): the owner has resumed #107. The checkpoint and
validation below remain historical evidence, not a completed repair or freeze.
The pause allowed time for better abstractions and possible frontend alternatives
to manual DSL transcription. The [revised scheduling decision](next-assessment-work.md#resumed-repair-and-revised-dependencies)
retains #108's independent test but removes a favorable retest as a blanket
prerequisite for #103's technical smooth construction. Older pause/entry-gate
language below is superseded by that decision.


This is framework-authored work for [#107], starting at
`429c7cc0418ccb6665520bce63422103cc60b61f`. It does not complete the general
associativity derivation or freeze an interface for #108. The #106 archive,
its manifest and its evaluation are unchanged. The independent retest must
wait for the successful repair and review required by #107.

## Implemented operations

`StructuralCongruence.lean` adds two derived operations:

- `SubEqDeriv.pairingConverted` extends a generated substitution conversion
  with a generated term conversion in a common type. It handles the casts
  between the two substituted annotations and that common annotation.
- `TmDeriv.substitutionCongrAt` applies a generated term to converted
  substitutions and presents both resulting annotations in a common type.

The common type is not inferred. Callers still provide equality of the left
raw type and the common raw type, and equality of both semantic type
annotations with the common annotation. These premises align presentations;
the generated substitution and term conversions justify the source conversion.
Semantic equality alone cannot change distinct raw judgments.

`CommandCongruence.lean` derives `PathCommand.argumentsCongr` by substituting
the command's generic J term. `genericJRaw_sub` proves that substituting the
endpoint and tail arguments cancels the generic term's ambient weakenings.
The operation accepts arbitrary ambient substitutions and finite dependent
tails. It avoids reconstructing two instantiated J typing derivations merely
to compare their arguments.

`ConcatenationCongr.lean` uses these operations for conversion of the first
argument of concatenation. This adapts the proof-local congruence from the
archived #106 attempt; it is not an independent proof-author result.
`TransportCongr.lean` now uses the same pairing operation for its endpoint
comparison, which is consumed by the existing transport-composition proof.

## Checked cases and statement review

`Examples/DependentCongruence.lean` exercises the public helpers with an
actual J beta conversion, a substituted reflexivity term, and a second
substitution component whose type depends on the first. It also retains the
archived associativity specialization with first path reflexive and arbitrary
second and third paths. Its explicit statement is an inhabitant of the nested
source identity, not equality of target composite arrows. Substitution of that
conversion is checked for arbitrary generated substitutions.

Statement review found no additional logical premise or constructor. Pairing
requires a generated conversion of the base substitution and a generated
conversion of the component. Command application requires a generated
conversion of its arguments and the original command's checked motive and
branch. The conclusion remains generated source conversion. The raw
substitution theorem concerns syntax only. The examples' beta premise is
constructed, so their use does not assume the desired conversion.

The reflexive associativity case does not quantify over an arbitrary first
path. It therefore does not satisfy #107's general regression requirement.
The existing general transport proof and interpretation clients remain in the
public import closure; no new general associativity interpretation is claimed.

## Remaining obstruction and alternatives

The unresolved obligation is still the model-parametric annotation comparison
between a substituted concatenation and a freshly constructed concatenation
of substituted arguments. After removing annotation casts and composing
substitutions, the left side reindexes J along the composite of its original
endpoint substitution with the ambient substitution. `Model.j_sub` instead
uses the canonical map of the pulled-back path telescope. It needs a
factorization through that map, followed by comparison of the pulled-back and
fresh telescope, motive and branch presentations. Raw concatenation reindexing
and the new argument-congruence helper do not prove those comparisons.

The direct annotation probe reproduces the shape recorded in #106 cycle 35.
The generic-term route succeeds for congruence within one command, but does
not identify commands built in different context presentations. No failure
here establishes impossibility or the need for an additional logical rule.

The derived helper layer was chosen for these completed pieces because it
reuses the existing source rules and soundness and has both concatenation and
transport callers. It is insufficient for the full repair. Two alternatives
remain open:

- Continue the derived layer with a reusable comparison of pulled-back and
  fresh dependent-context presentations, then discharge the concatenation
  naturality obligation and complete the archived general branch.
- Represent reusable operations as fixed open source templates with explicit
  argument substitutions, so reindexing is substitution composition. This
  needs checked construction of dependent argument environments and a precise
  relationship to the existing named operations. It has not been implemented
  or validated here.

Neither alternative authorizes semantic equality reflection, a new logical
rule, a toolchain change or higher production heartbeat limits. A broader
frontend or model redesign would require the scope decision described in #107.

## Work and completion boundary

The implementation work included extracting dependent pairing casts from the
archived congruence, deriving generic J substitution cancellation, integrating
that operation into concatenation congruence, and checking dependent callers.
Debugging included explicit endpoint parameters that elaboration could not
infer and equality transport in the raw and annotated term presentations.
The direct annotation-naturality probe remains unsolved. No effort ratio or
fresh-author saving was measured.

These results suggest an operation-application interface that can serve a
future proof frontend: the author supplies typed arguments and source
conversions, while the implementation cancels weakenings and aligns casts.
A compiler frontend can use the same principle without sharing this AST.
The missing context-presentation comparison is a separate requirement; hiding
it behind a record field would only pass the obligation back to the caller.

The general source associativity proof, its ordinary-groupoid and labeled C4
applications, complete root/projection abstraction, final diagnostics and
handoff updates, passing full-spec review, and the reviewed public freeze
remain outstanding. The existing handoff is unchanged and must not be read as
a #107 freeze. No next independent theorem was selected or prepared.

## Approved continuation plan

The project owner approved the following plan after the originating session
reviewed candidate `40e9b785be9217b6d6e2e8621d82562781d25bab`. Work is paused
after committing this partial implementation and plan. This checkpoint is not
acceptance of #107 and is not the frozen handoff for #108.

The architectural assessment is that the helpers provide useful internal
factoring, with real transport and concatenation reuse, but do not yet provide
the intended proof-author interface. `pairingConverted`, `substitutionCongrAt`
and `argumentsCongr` still require callers to supply annotation alignment.
Comparing arguments of one fixed command does not compare a substituted
command with one rebuilt in a different context. The retained substitution
example substitutes an existing conversion; it does not establish agreement
with fresh named operation construction.

On resumption, keep #107's acceptance criteria and change the next design step:

1. Test a small structural design before adding more wrappers. The preferred
   first experiment represents reusable operations as fixed open source terms
   applied through typed argument substitutions. Investigate whether application
   reindexing can be handled by substitution composition, using the existing
   `subTyComp_code` and `subTmComp_code` laws. Construct and check the dependent
   argument environments; do not assume that a template representation removes
   their coherence obligations.
2. Compare that experiment with a reusable comparison of pulled-back and fresh
   dependent-context presentations in the current representation. Exercise both
   approaches on the same known transport and concatenation cases. Preserve
   failed attempts and explain the choice using caller obligations, reuse and
   maintenance locality, rather than code length.
3. Require an actual author-facing result: application under arbitrary typed
   substitution, including genuinely dependent tails, with generated beta and
   congruence and no manual model-code equalities at ordinary proof call sites.
   The structural implementation must discharge the relevant comparisons.
   Moving the same obligations into caller-supplied record fields does not meet
   this criterion. Keep raw equality, source conversion and semantic annotation
   equality distinct; no host-proof injection or equality reflection is allowed.
4. Use the successful structural design to complete general associativity and
   its ordinary-groupoid and labeled C4 interpretations. Preserve the existing
   transport proof and direct clients. Apply EDD/statement review, full fresh
   validation and exhaustive audit, then resolve the ordinary review findings
   and obtain originator review before freezing the public handoff.
5. Only then start #108 with a new unexposed author and a different theorem
   selected after the freeze. Do not select or prepare that theorem during
   these experiments. #103 remains gated on the independent retest assessment.

The template approach is an unvalidated design hypothesis, not a decision to
rewrite the core. This approval covers the bounded comparison within #107;
a new logical rule or substantially wider redesign still requires the scope
decision specified there. Retain the current helpers as internal partial work
where useful, without treating their existence as a commitment to their final
interface. No further implementation is part of this pause checkpoint.

## Validation and unresolved review findings at the pause

The implementation session was `01a16033-7143-7ca3-93b2-5daae6954694`.
Its reviewed range was `429c7cc0418ccb6665520bce63422103cc60b61f` to
`40e9b785be9217b6d6e2e8621d82562781d25bab`. The originating session verified
that all seven changed files matched that candidate before adding this plan.
The Lean source is unchanged from the checked candidate.

The recorded `direnv exec . ./check.sh` run passed all 477 modules and the
exhaustive audit with only `propext`, `Classical.choice` and `Quot.sound`.
Standards review passed. Spec review failed with three unresolved findings:

- SPEC-1: the general associativity source derivation and its general and C4
  interpretation applications are missing.
- SPEC-2: substituted-versus-fresh annotation alignment, root/projection
  comparison and reindexing under dependent tails remain incomplete.
- SPEC-3: the final diagnostics, handoff commands and reviewed public freeze
  remain outstanding and must follow the successful repair.

The originator's architectural assessment also withheld acceptance. Committing
this checkpoint preserves work and the approved next experiment; it does not
resolve these findings. No full build was repeated for this prose-only plan
addition. The #106 evidence remains unchanged.

[#107]: https://github.com/VladimirMarko/conaled/issues/107
