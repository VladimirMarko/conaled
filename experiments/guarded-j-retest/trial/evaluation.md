# Guarded J author trial evaluation (#323)

Both fresh authors completed the calibration and selected nested-J contract
without proof assistance or changes to the frozen interface. Coordinator replay
of each exact submission passed in its original frozen handoff. The integrated
copies are byte-identical; no author proof was repaired during evaluation.
Independent final review remains required before ticket acceptance.

## Provenance and controls

The interface freeze remains `e376ba585603ae8f2c174d5ceaab374242942cbd`.
The approved dispatch candidate was `9677e0c83074d6af4bce3f8f8d0a54126981c15b`,
including the corrected exhaustive private-reference audit. The verbatim
approval, dispatch, initial settings, exposure and completion records are in
this directory. Both author sessions used configured `gpt-6-astra`, `medium`.
`author-settings-final.json` examines only the two recorded own-trial log paths;
it finds one turn context per author and no later settings change. These are
configured identities, not a hidden serving revision or sampling record.

Each author received a fresh context and only its arm's public source and
compiled closure, exact prompt and common protocol. The baseline read the public
nested-J examples; the candidate read the supplied `Command.reflexivity`
implementation. Both were told calibration had prior completed solutions and
that nested-J ingredients were public. Neither reports reading a completed
#320 submission, the other arm or private references. This is a fixed-order
calibration then held-out trial, not two independent first exposures. Isolation
is procedural on a shared host. No subagents, proof hints, stopping budget,
resource failures or contract changes were reported. Missing handoff README
files were noted by both; they used the supplied environment directions.

`baseline/` and `candidate/` preserve the entire author attempts directories,
including intermediate source, wrapper command/status/output records, activity,
outcome and metadata. `archive-manifest.json` hashes that snapshot before any
coordinator replay. `coordinator/` records separately named exact replay attempts.
`verify_records.py` checks evidence hashes, author/integrated/replay byte identity,
replay exits, attempt totals and unchanged public sources/compiled closures.
It does not claim to export a complete interaction transcript. Full author
transcript/token accounting was unavailable in the author records; no token
or effort quantity is inferred from wall time or line counts.

## Observed attempts

Counts below are derived from immutable wrapper result records sorted by their
start timestamps in `attempt-summary.json`. They include calibration, inspection
and submission runs; they are not counts of failed proof ideas.

| Arm | Wrapper runs | Exit zero | Nonzero | Recorded sequence |
|---|---:|---:|---:|---|
| Baseline | 6 | 5 | 1 | Attempt01 calibration; 02 failed conversion rewrite; 03 repaired host annotation; 04 full contract and type inspection; Submission; 05 exact submission plus axiom inspection |
| Candidate | 9 | 6 | 3 | Attempt01 calibration; 02 congruence inference failure; 03 explicit signature; 04 namespace ambiguity; 05 omitted substitution binder; 06 explicit binder; 07 worked comparison; 08 statement/axiom inspection; Submission |

Candidate Submission is byte-identical to Attempt07. Attempt08 adds inspection
commands; it is not an extra mathematical revision. Baseline Attempt05 likewise
inspects the completed Submission. All runs remain preserved, including each
nonzero exit. These small, nonrandomized, single-author-per-arm observations
support neither causal productivity nor human usability claims. No timing
comparison is used to rank the interfaces.

## Statement review

The intended objects are selected certificates eta := J(refl(p[r])) and
kappa := J(refl(eta[r])). Their types are respectively Id_Q(p,p) and
Id_{Id_Q(p,p)}(eta,eta). Neither output may be replaced by plain reflexivity.

| Obligation | Baseline submission | Candidate submission |
|---|---|---|
| Calibration, arbitrary tail and root map | `calibration`, typed `inner`, `rootMap`, `calibrationBranch` | `calibration`, `inner`, `calibrationRecipe`, `rootMap`, `calibrationBranch` |
| Full selected outer type and exact recipe | `outer`, `outerTerm`, expanded `selectedRecipe` | `outer`, `outerTyping`, `selectedRecipe` |
| Root equation and aligned typed operands | `rootLeft`, converted `rootRight`, `rootBeta` via `typedEquation` | `rootLeft`, `rootRight`, `rootBeta` |
| Arbitrary valid dependent substitution | `substitutedLeft/Right/Beta` indexed by `SubDeriv` | `substitutedLeft/Right`, `comparison` explicitly require `Sub`; raw `substitutedBeta` is syntactic congruence |
| Constructed dependent weakening | `dependentWeakening`, `workedLeft/Right/Beta`, `workedSound` | `dependentWeakening`, `workedLeft/Right/Beta`, `workedComparison` |
| All-model interpretation | `comparisonSound` plus exact-root `selectedRoot` | `comparisonSound` retains both typing judgments and equality under satisfied assumptions |
| Stable Sigma reuse and selected family | `extensionSelected` explicit nested semantic code, `extensionFamily` dependent Section | `extensionLeft/Right/Beta`, `extensionAssumptions`, `extensionSelected` with exact expression/family evaluation and reduct |

Baseline's source root comparison retains the public presentation's generated
identity argument map: root composed with identity, followed by the chosen
substitution. Its branch operand is converted with `TyEqDeriv.subComp`. The
semantic cast and `reflexiveCompose` rewrite align the complete family; no
requested alignment is assumed. `selectedRoot` separately supplies exact-root
semantic beta. `extensionFamily` explicitly retains the full nested family,
while `extensionSelected` retains the chosen nested J code. The stable capability
is unused in those baseline expressions because old code is reused on the exact
old-model reduct, as specified in the baseline guide.

Candidate's source equation is an `Equal` derivation, distinct from its separate
`Tm` judgments. Equation substitution uses congruence and therefore does not
need a validity proof for the substituted syntax alone. Its typed operands,
`comparison`, interpretation and extension theorem explicitly require valid
`hσ`; the failed Attempt05 was not accepted. The constructed weakening uses the
restricted inner certificate's family. Sigma reuse embeds source assumptions
and each derivation and proves exact old expression and family evaluation plus
reduct equality. No equality reflection, UIP, desired-output assumption or new
model law appears in either source.

`Examples.GuardedJAuthorEvaluation` consumes both actual submissions in the
native Nat/Fin(n+1) model with the three dependent NamedCaller binders. It
constructs inhabitants of the full tail, root pullback and weakening context,
proves every guarded source assumption valid, and specializes the typed
comparisons and exact selected retention. Its final `selectedCommand` theorems
check definitional equality between each author's outer command and the
corresponding private reference, for arbitrary inputs. This is stronger recipe
comparison than observing equal endpoints in the native model. The native
cases themselves supply only lower-truncation evidence; all-model claims come
from the generic author theorems.

## Burden and decision

The repair supplies guarded `Tm.rootTail` from the existing point/telescope
premises, `Tm.reflexivitySub` for the branch family conversion, and
`Command.reflexivity` for the selected J recipe. The candidate author used
those calls for calibration and composition. No raw root rule, explicit root
premise conjunction, telescope recursion or identity-substitution conversion
proof was authored. The baseline already had a public root-tail rule and did
not incur raw root recursion either; the removed burden is relative to the
previous guarded interface and #320 failure, not an invented baseline deficit.

The remaining guarded work includes raw finite congruence cases to substitute
the equation, operation/theory inference, namespace disambiguation, explicit
Lean section-variable retention, and source assumption embedding for Sigma.
The baseline retains raw/semantic indices, a root-composed-with-identity
presentation, family conversion, cast annotation and a dependent rewrite.
Those burdens are visible in the exact proofs and failed attempts. Neither
arm eliminates all host proof plumbing.

Preparation work is separate: coordinator helper development/calibration,
matched private proofs, native fixture construction, handoff build/closure
checks, evidence-wrapper tests and repair of the mis-scoped private audit.
Model work is the existing full contextual semantics and stable Sigma reduct;
no new model was built by an author. Source work consists of the preserved
derivations and selected recipes. Host work includes the Lean elaboration and
conversion failures above. Author work is only the immutable records from the
fresh dispatched sessions; coordinator replay, reference comparison and native
specialization are post-trial evaluation. None is folded into author effort.

The trial supports retaining the frozen repair: the prospective guarded caller
completed the specified contract and exercised the intended root and branch
helpers. It does not justify a broader promotion, a higher-model result or a
usability claim. Congruence authoring remains a specific follow-up candidate;
no silent helper repair was made after freeze. #320 artifacts remain immutable;
#107 stays paused, #108 unselected and #260 inactive. Final independent review
and candidate validation govern acceptance; no issue has been closed here.
