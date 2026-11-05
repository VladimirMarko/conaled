# Baseline author outcome

Proposed complete submission: `attempts/Submission.lean`, namespace
`DependentAuthorTrial.Baseline`. The wrapper passed with exit 0 and verified
public inputs before and after checking. SHA256:
`2415929c8fdb7e2d5e4c6c5fa1664e2a0daf119b89009c0c8e9719009326dcf9`.
The submission is byte-identical to the checked `Attempt04.lean`.
Mathematical acceptance remains pending coordinator replay, statement review
and exhaustive audit.

## Coverage

| Required declaration | Implementation and retained content |
|---|---|
| `calibration` | `PathCommand.rebuildConversion` for an arbitrary admitted command and one typed base substitution. `calibrationLeft` and `calibrationRight` separately retain its substituted and freshly reconstructed source operands. |
| `certificateCommand` | `PathCommand.make` with `Motive.reflexivity` at arbitrary `hΓ`, `hA`, `hx`, `hT`, `hQ`, `hp`. Its motive is `Id_Q(p,p)` and its branch is exactly `refl(p[r])`. The public motive constructor forms `rootTail`, substitutes Q and p, forms reflexivity, and converts by the symmetry of `TyEqDeriv.identitySub`. Its `motive.branchTyping` retains the required branch derivation. |
| `certificate` | The command's `genericTerm`, hence the actual `genericJRaw` expression and selected `jCode`, at the command's identity motive. |
| `valueTwice`, `certificateTwice` | Two successive applications of `TmDeriv.sub`, with arbitrary typed simultaneous substitutions σ and τ. |
| `valueTypeComparison`, `certificateTypeComparison` | `TyEqDeriv.subComp` for Q and `Id_Q(p,p)`, respectively. |
| `valueComparison`, `certificateComparison` | `TmEqDeriv.subComp` for p and the selected J expression. The equations retain the converted selected annotations in the composite family. |
| `certificateAligned` | Converts the actual twice-substituted certificate with `certificateTypeComparison`. Its raw term remains the twice-substituted J. |
| `firstWeakening` | Forms the full path-and-tail context with `CtxDeriv.path` and `CtxDeriv.telescope`, forms its certificate family and constructs weakening into that context from its extension by the family. |
| `witnessVariable` | The generic variable k in that first extension, with its type written as the weakened certificate family. `Expr.sub_var_rename` aligns the raw substitution notation with the variable rule's renaming notation. |
| `secondWeakening` | `secondFamily` forms identity over the weakened certificate family with both endpoints equal to k. Weakening is constructed from `firstContext` and that dependent family. |
| `dependentWeakeningCertificate`, `dependentWeakeningComparison` | Direct applications of the generic certificate typing and comparison to the two constructed weakenings. No substitution typing is assumed for these instances. |
| `valueValidity`, `certificateValidity` | `interpretTm_agrees` on the actual twice-substituted derivations, retaining the exact selected value and selected J annotation. This invokes the recursive checked interpreter whose return value is a semantic section. |
| `certificateTypeValidity` | Interprets the actual source family comparison with `typeSound`; all source premises remain quantified. `interpretedCertificateTypeComparison` additionally states equality between the two checked family interpretations. |
| `extensionSelected`, `extensionValue`, `extensionType` | The same selected-data and dependent-family statements for every full `Typed.Model` with an explicit `Sigma.Stable M.toStructuralModel` parameter. |
| `extendedCertificate`, `extendedValidity` | Reuses the original source certificate unchanged for the full model's exact old-language reduct, and checks its interpretation against the exact selected J annotation. |

`valueComposite` and `certificateComposite` retain the composite-substitution
source operands. `interpretedCertificateComparison` compares the checked
interpretation of `certificateAligned` with `certificateComposite` through
`termSound` of the source comparison.

## Statement review and checked applications

The generic statements quantify over arbitrary finite dependent tails and
arbitrary semantic indices constrained only by their source derivations.
There is no extra semantic-equality assumption, UIP, equality reflection or
native-equality restriction. The source certificate is a J node; reflexivity
occurs in its required branch. Substitution order is σ followed by τ, with
composite raw substitution `fun n => (σ n).sub τ` and code `compCode s t`.
The second added source family is identity over the first witness k, not a
copy of the original value family. The checked declaration types retain these
indices and selected sections.

`workedCertificate`, `workedDependentWeakening` and
`workedDependentComparison` instantiate the generic declarations using the
public `NamedCaller` source context with its z, q and fiber tail. They use the
generic results directly and show that the required source inputs can be
constructed. These are disclosed calibration sources, not independent
higher-model evidence.

The full elaborated-type and transitive `#print axioms` output is preserved in
`attempts/checks/Attempt05/lean.stdout.log`. Every local mathematical
declaration reports only `propext` and `Quot.sound`. The auxiliary
`statement-review-output.txt` removes qualified-name prefixes for readability;
the archive is the exact evidence. Some concrete-instance output expands to
large types, so tool display was truncated. The source and full output remain
preserved. Coordinator acceptance and its repository audit are still required.

## Attempts and assistance

- `Attempt01`: calibration, exit 0. Preserved before held-out authoring.
- `Attempt02`: first held-out construction, exit 1. Two theorem bodies referred
  to section variables absent from their statements. Lean reported unknown
  identifiers for those references; this was a scoping failure.
- `Attempt03`: explicit `include` binders restored those source premises;
  checked interpretation and composite operands added, exit 0.
- `Attempt04`: concrete dependent-tail applications added, exit 0.
- `Attempt05`: declaration and axiom inspection of the same construction,
  exit 0.
- `Submission`: exact copy of Attempt04, exit 0.

All source attempts used the required wrapper. No mathematical hints,
environment repairs or contract clarifications were requested or received.
No actual prior mathematical exposure or accidental boundary exposure occurred.
The activity and session metadata records identify the consulted files,
commands and unavailable telemetry.

## Author obligations and limits

The author retained explicit context, family, term, telescope and substitution
code indices in the generic binders. The reusable `Motive.reflexivity` API
already performs the branch's semantic alignment from the source equality;
`TmDeriv.convert` similarly derives the certificate's alignment through
`typeSound`. No additional model coherence was postulated. The one local raw
syntax alignment was rewriting weakening substitution into renaming for the
variable rule. Interpretation conclusions explicitly spell the nested
`subTmCode` and selected `jCode` annotations.

The available API comments and constructor types were sufficient for this
submission. No documentation gap blocked completion. Elaborated types of the
concrete applications expand substantially, which makes diagnostic reading
more cumbersome; this is an observation about this encoding and inspection
method, not a mathematical obstruction.

Typed has no object-language Sigma constructor. Supplying a stable Sigma
capability extends the available semantic model structure while leaving the
old Typed interpretation reduct exact. The unchanged source derivation and
its checked interpretation therefore suffice for this arm's reuse contract.
This submission neither authors a Sigma source term nor proves constructor
capabilities, higher-identity coverage or a beta-only extension theorem.

No mathematical obligations are knowingly left unresolved in the proposed
submission. Exact stopping reason: the requested source construction,
applications, interpretation claims, checked final artifact and coverage record
are complete and handed to the coordinator for independent acceptance.
There was no resource failure or external interruption.
