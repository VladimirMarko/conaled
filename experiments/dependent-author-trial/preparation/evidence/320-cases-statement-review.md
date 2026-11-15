# Private reference cases for #320

Scope: `Examples/DependentAuthorTrialCases.lean`, consumed only by private
preparation and eventual integrated validation. The module imports both private
references and existing `Sigma.Native`; it changes no frozen public interface
and selects no task. No author has been dispatched by this helper.

## Statement review

- `native` is the constructed full `NativeType.model Nat (fun n => Fin (n+1))`;
  `stable` supplies its constructed stable Sigma capability. Thus the model and
  capability parameters are inhabited. Native identity is lower-truncated;
  these cases make no higher-model or beta-only-model claim.
- The baseline source specializations use `NamedCaller`'s complete length-three
  telescope: z, q : y = z, and b : fiber x. `comparison` calls the reference's
  `dependentWeakeningComparison`, and `comparison_sound` applies all-rule
  `termSound` after explicit alignment of the result type. Its quantifiers are
  specialized to actual source derivations and a concrete model, with no
  assumed comparison or selected-result equation.
- Baseline `certificate_valid` calls the reference's `certificateValidity`;
  `extension_selected` calls `extensionSelected` with the constructed stable
  capability. Both explicitly equate recursive interpretation with the exact
  section carried by the twice-substituted derivation's semantic index. The
  private `selectedCode` extracts that index, which is the twice-substituted J
  section; it is not a choice of some inhabitant of the identity family.
- `inputsOf` evaluates the named caller's actual annotations. `tail_length`
  checks length three. `populatedTail` constructs an element starting at the
  earlier base value 3, taking the actual interpreted selected point for the
  endpoint and z, reflexive paths, and zero in the varying positive finite
  fiber. `tail_inhabited` records nonemptiness. Private `weaken_value` and
  `variable_value` apply `castCode_eval` to justify the native projection
  equations hidden by the baseline's annotation casts; they add no axiom.
- Candidate assumptions are exactly point typing, a length-three tail over the
  path context, and value typing over the tail total. `assumptions_valid`
  constructs all three semantic witnesses from these concrete inputs; neither
  the requested equality nor a validity conclusion is assumed.
- Candidate `certificate_valid` consumes the reference's `certificateValidity`
  under those satisfied assumptions and the two dependent weakenings.
  `extended_certificate_valid` consumes `extendedValidity` in the constructed
  Sigma extension. The claims concern full term judgments, not only evaluation
  equality of old expressions. `comparison_valid` separately interprets the
  reference's `dependentWeakeningComparison` on the same inputs.
- Candidate `selected_certificate` identifies the evaluated command with the
  exact native J section over the full telescope, with motive Id(p,p) and the
  reflexive branch over the root pullback. It explicitly checks decoding at
  the pulled-back family. `extended_selected_certificate` uses the reference's
  `extensionSelected`, then this selected-section equation, to retain that
  section after both dependent weakenings. Its context and family are kept in
  the `Value.term` result. Native proof irrelevance means this case cannot
  distinguish higher identity witnesses; the stated lower scope is essential.
- Constructor `sigma_composition` specializes `Stable.sigma_comp` to
  A(n)=Fin(n+1) and B(n,i)=Fin(i.val+1), using shift and double. The independent
  order calculation gives 3 for shift-after-double at 1 and 4 for the reverse.
  `selected_index` consumes `Native.bounded_split` and retains 2 : Fin 4;
  `bounded_beta` consumes the same nonconstant-motive section beta theorem.
  These are separate constructor-capability checks, not extra author tasks.

## Development and validation

The first reference imports were unavailable while the coordinator's builds
were still running. Later local errors were reserved-word syntax, insufficient
unfolding of native annotations/decoding, and theorem declaration syntax. They
were host/proof-script issues, not evidence against the mathematical contracts.
Raw intermediate diagnostics remain in `validation/320-cases*.log` outside the
source checkout. The two initial proposition aliases caused defProp warnings;
the final source uses theorems with explicit equality statements.

Final commands and exact input hashes are in `320-cases-validation.json`.
`320-cases-build04.log` is the final focused build after the coordinator's last
reference comment changes. `320-cases-audit-final.log` records the focused
exhaustive project axiom/source audit over both reference imports, this module,
and their project import closure, using the existing ProofAudit implementation.
The enclosing coordinator still owns final immutable candidate validation,
public-entrypoint integration, independent Standards/Spec review, and dispatch.
This focused evidence does not claim completion of those gates.
