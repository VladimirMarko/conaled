# Unassisted assoc baseline: incomplete at the budget limit

The independent baseline stopped after the frozen 40-cycle budget. It did not
produce the selected general `foundation-core.identity-types.assoc` source
derivation. It produced a checked reflexive-first-path specialization, a typed
general motive, and several checked components of the general reflexive branch.
This is an incomplete transfer and inconclusive evidence about feasibility in
the frozen fragment. It is evidence that this author did not complete the port
within this budget. No unsupported logical rule or impossibility was proved.

The protocol, selected upstream revision, and accepted API HEAD are unchanged.
Scope review PASS and the fresh-session provenance supplied by the orchestrator
are recorded in `attempt-log.md`. Author session:
`01a15f76-ecf1-7da1-bc56-717ed6849978`. No implementer help, reviewer feedback,
private notes, or theorem-specific external helpers entered this attempt.
No direct-Lean comparison was undertaken. There were no commits, pushes,
tracker writes, or changes to tracked source/API files.

## Evidence and replay

`work/partial.lean.txt` contains the final checked partial artifact, byte-identical
to `cycles/40/Attempt.lean.txt`. It is text so it cannot enter the production
Lean source scan. The original attempted files, including failures, are retained
as `cycles/NN/Attempt.lean.txt`. Each cycle from 4 through 40 has a command record
and full output. Cycles 1–3 were read-only investigations recorded in the ledger
before the capture runner was written. Their original terminal output was not
separately saved. No failure has been erased by restoring a working version.

To replay an archived attempt later, copy its text to a scratch `.lean` file
inside this checkout and run `direnv exec . lake env lean <scratch-path>`.
This is a replay instruction, not an additional baseline check. The current
baseline is closed to proof edits. `run.py` records command output and exit
status in JSON; its own shell exit is not the Lean exit. Read `exit_code` in
each record. The exact pinned shell and prepared caches were used.

The final manifest covers the protocol, upstream evidence, requirements,
attempts, diagnostics, runner, declaration inventory, ledger, and this report.
The archive and manifest digests are announced separately to avoid a
self-referential digest. Files outside `baseline106/` are excluded from the
archive. No production integration is claimed.

## What checked

The final partial file checked successfully in cycle 40. Its named source
derivations include:

- `assocGoal`: formation of the intended identity between paths for arbitrary
  composable `p`, `q`, and `r`.
- `concatEndpointsCongr` and `concatCongrFirst`: proof-local generated
  substitution and J congruence for changing the first concatenation argument
  along a supplied source conversion.
- `assocReflexiveEquality`, `assocReflexive`, and
  `checkedReflexiveStatement`: the intended source identity when the first
  path is reflexivity, with the other two paths arbitrary.
- `Frame.motive` and `Frame.tail`: the general associativity motive retaining
  the four dependent entries `z`, `q`, `w`, and `r`.
- `Frame.concat_root_normalized`: computation of the inner concatenation in
  the general reflexive branch.
- `Frame.right_root_beta`: computation of the right-associated side under
  the general reflexive substitution.
- `concatRebuildConversion` and `rebuiltMotiveRaw`: existing generic source J
  rebuilding instantiated for concatenation, and equality of the rebuilt and
  fresh command's raw motives. Raw agreement does not settle their annotations.

Cycle 40 also ran `#print axioms` for all 58 explicitly named local declarations
listed in `partial-declarations.json`. The results contain only `propext`,
`Classical.choice`, and `Quot.sound`. This selected-root inspection is not the
repository's exhaustive audit of generated/private roots. No full fresh build
or exhaustive repository audit was run, because the selected transfer was not
complete. No placeholders occur in the final partial artifact. Failed scratch
files contain unsolved goals and are not completed proofs.

## Source correspondence and statement review

The upstream declaration quantifies over four points and three composable
paths and concludes an identity in the path type from the first to the fourth
point. The initial cycle-4 obligation and `assocGoal` preserve those endpoints,
parenthesizations, arbitrary paths, and identity level. The universe/type
parameter remains external, as agreed in the protocol. There is no internal Π
or universe extension.

The inspected upstream proof has a reflexive-first-path clause with the later
paths retained. The partial development follows that structure: the general
motive retains the later points and paths, and the checked specialization
derives its identity by generated concatenation computation and congruence.
It does not close the target identity using ordinary groupoid associativity.
The upstream argument is preserved in this checked specialization, but no
complete Agda-to-Lean proof-step correspondence can be claimed until the
general branch and J application exist.

The explicit `checkedReflexiveStatement` in cycle 39 verifies the specialization
as a generated term of the intended iterated identity. It assumes only a
generated context, points and two composable paths; it does not assume the
desired identity. This is a partial EDD case, not completion of the candidate
by restricting its inputs. The named congruence helpers require a source
conversion of their input paths and return a generated source conversion.
Their specialization is exercised by `assocReflexiveEquality`.

The frame's context, term, telescope and normalization declarations were
reviewed as bookkeeping components of that same statement. Their equality
claims distinguish raw syntax equality from semantic annotation equality and
generated source conversion. Raw root lemmas identify the substituted moving
point and first path; projection and root-code lemmas align their annotations.
The beta components invoke the existing generated rule. The helper `refl_heq`
compares reflexivity annotations only after its context/type/point equalities
are supplied. None supplies source identity from a semantic equality alone.

These checks do not establish the intended semantic applications or rule out
all vacuity. No C₄ translation/trivial-family application or arbitrary-groupoid
consumer was connected to a completed `assoc` derivation. Those planned cases
remain unfulfilled. The final artifact is partial, not EDD green for #106.

## Unresolved connection

Cycles 29 and 30 preserve the exact branch obligation and the failed attempt
to use the fresh reflexive specialization. Normalizing the nested identity
type was insufficient: the branch's terms are concatenations after a typed
substitution, while the specialization constructs fresh named concatenations.

The frozen `concat_raw_reindex` proves equality of the relevant raw forms.
The attempted `concatCodeReindex` in cycles 34–35 exposes the corresponding
annotation equality. It is not definitional. Applying `M.j_sub` directly fails
because the current substitution is a composed endpoint substitution, while
that theorem expects the dependent path-tail map. A factorization and
comparison of the rebuilt tail/motive/branch presentations would still be
needed along this route. Cycles 36–38 confirm that generic source J rebuilding
exists and raw motives agree; they do not close the annotation comparison.

This identifies an unresolved proof-local obligation, not a proof that an API
change is necessary. A different caller or more local bookkeeping might work.
The baseline did not insert a host proof, silently add a rule, or repair the
framework. At cycle 40 it stopped under the predetermined budget.

## Reuse and incremental effort

The frozen generated calculus, named values, concatenation, beta, generic J
congruence, typed substitution, raw reindexing, interpretation infrastructure,
and first-port examples were reused unchanged. The proof-local endpoint and
concatenation congruence helpers were written during this attempt. They appear
applicable to other nested concatenation proofs, but that reuse was not tested
beyond the retained specialization.

Projection/root bookkeeping was adapted from the public frozen
`TransferRoot.lean` pattern, extending its tail to retain `w` and `r`.
The inner-concatenation root normalization was adapted from the public
`ConcatReindexBeta.lean` specialization. These are declared source inputs and
adaptations, not independently invented machinery or newly supplied help.
The upstream MIT notice remains in `evidence/LICENSE.md`.

The 40 cycles comprise three initial investigations and 37 recorded command
cycles. Primary labels for the latter are: seven translation, seven
investigation, eleven debugging, nine helper, one application, and two
validation cycles. These labels describe purpose, not exclusive effort
measurements. Six recorded commands were source searches/reads; 31 were Lean
checks, of which 17 failed. `cycle-summary.json` identifies the failed cycles.
Cycle 6 includes a preparatory Python invocation outside direnv that failed
before editing; its Lean check repeated the earlier obligation. Cycle 29 also
hit the default heartbeat limit while formatting a type mismatch; later
checks used a local 800000-heartbeat setting. No tooling or API pin changed.

Framework construction and framework repair during this baseline were zero
by constraint. Dependency discovery, helper writing, translation and debugging
are visible in the snapshots and command ledger. Command timestamps are
available, but no person-hour or token-effort total was measured. Line counts
and build wait time are not used as effort estimates.

This one incomplete experiment does not establish that selective porting is
unviable, or that new helpers would reduce another fresh author's effort. The
intended benefit of a single general source proof across models remains
prospective here. The direct-Lean comparison, independent evaluation,
recommendation, and any assisted work are deferred until after this immutable
archive. This report does not close #106 or waive its completion gates.
