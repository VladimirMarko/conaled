# Local10021 — independent Standards review, round1

Reviewer: `/root/persistent_accounting_review/standards`, 2026-11-03.
This reviewer did not author the implementation and did not read the other
axis's report. This is the Standards axis of the retained10021 review loop,
not a new implementation loop or a third coordinating review.

**Outcome: Blocked. Static code/architecture findings:0. Unresolved validation
findings:1, High.** No formal acceptance or chapter advancement is established.

## Exact scope and requirements

Both bounded and original integration bases are
`3dd930c3e3989f3e5530463f3ac937a629551335`. Candidate is
`577be121e074ddb5de6727a7481c115cb61b3b27`, branch
`pfds/persistent-accounting-review-r3`, in the isolated checkout
`/workspace/scratch/ca9a61d0bf30/validation-persistent-accounting`.
Read-only Git inspection confirmed the candidate HEAD, clean tracked/index/
nonignored state, and merge base equal to the supplied base. The nonempty
three-dot diff covers all11 files and5 commits, with no exclusions:

```text
git diff 3dd930c3e3989f3e5530463f3ac937a629551335...577be121e074ddb5de6727a7481c115cb61b3b27
git log 3dd930c3e3989f3e5530463f3ac937a629551335..577be121e074ddb5de6727a7481c115cb61b3b27 --oneline
```

Complete commit scope, oldest first:

- `dc16a3b457b0393bb94188269fa3749deef39657`
- `c6f96cfc6d3ef6f715e72206c1b69359af4928fc`
- `eedaeca6fc2fcc3f73cb92630dc8d8acf2bd50f8`
- `eb61c35f911ad0fac36758c878559eaf5f795cfa`
- `577be121e074ddb5de6727a7481c115cb61b3b27`

The governing saved requirements are `requirements/REQUEST.md`,
`requirements/REQUEST-union-v2.md`, and
`requirements/persistent-debit-foundation.md` version1, SHA256
`2a89d7818d73e0b1b118ebf7d902a75afb2b6e25afaae6b9c7842d229964922f`.
The complete dispatch and candidate manifest were inspected. The user's local
tracking/checkpoint exception supersedes the GitHub destination in AGENTS;
no external tracker operation is required or performed here. Necessary shared
foundations are permitted, while Chapter2 remains the earliest unaccepted
chapter and the parent10017 source/work correspondence remains open.

## Standards applied

Applied candidate AGENTS, README development environment/build/audit/proof
boundary, architectural-quality, domain guidance, root GLOSSARY, ADR index and
ADRs0001/0006/0010, language-direction, code-review and heuristics, shared review
procedure, and example-driven-development including its worked example.
No root CODING_STANDARDS or CONTRIBUTING document was present. The only other
AGENTS found belongs to an unrelated toolkit-authoring experiment and is outside
this scope. No standalone orbifold material or upstream Felix construction was
used as a proof/design reference.

The architectural assessment inspected all changed source/client declarations,
not only the author narratives. Relevant unchanged code included
`Resources.Measured`, `Resources.Workload`, the potential-accounting interface,
and public-entrypoint/audit ownership. The three implementation handoffs retain
intended statements, independently calculated expectations, public theorem
connections, failed rounds and corrections; these are development evidence,
not substitutes for this independent review or the audit.

## Unresolved finding

### PERSIST-ACC-STD-VAL-001 — High — own exact-candidate acceptance evidence is missing

**Status:** unresolved; validation blocker.

**Location/evidence:** the complete candidate identified above;
`validation/persistent-accounting-candidate-r3.json` explicitly records that
its own full validation has not run. The isolated candidate has no
`.lake/verification.json`. The supplied successful record is the focused
`validation/persistent-accounting-r3.json`, not the stock full acceptance
command. Its inherited3dd foundation is also awaiting its separate acceptance
gate. No successful exhaustive audit or final candidate verification for577
was supplied or observed.

**Applicable rule:** README, Build and audit; ADR0010; and
`docs/agents/review-loop.md`, Validation of the candidate. Integrated Lean
acceptance requires the clean isolated candidate's stock
`./check.sh --candidate HEAD`, exhaustive proof audit and matching success
record, with `./check.sh --verify-candidate HEAD` immediately before acceptance.
Missing required evidence prevents a passing review. Module-focused success
and transferred ordinary outputs cannot establish complete integration or
absence of forbidden transitive axioms over all audit roots.

**Concrete consequence:** accepting577 now would certify a scope that has not
passed the project's full source/import/build/audit gate. This is an evidence
gap, not a claim that one of the inspected proofs is false.

**Required resolution:** retain this finding while root completes the applicable
dependency gates and the exact577 stock candidate command in its frozen isolated
checkout. Preserve the terminal log and matching verification record and return
them to this same review pair. Perform immediate final verification before
accepting identical bytes. If any source/candidate changes are needed, provide
both axes the complete fixed-base correction scope and retained findings.
Do not close this finding using focused checks, a predecessor's approval or
copied compiler outputs.

## Static architectural and methodology assessment

### Ordinary interfaces and explicit requirements

`Applications/Resources/Persistent/History.lean` uses Mathlib's ordinary
`Quiver`, `Quiver.Path` and `Prefunctor`, preserving arbitrary vertex/arrow
universes and parallel edges. Reachability is explicitly reflexive; finite
history closure is a separate predicate. Path/history laws do not impose
decidable equality, a finite vertex universe, a chronological order or
acyclicity. Union/intersection add only their needed decidable vertex equality.
Transport is stated as forward history preservation, without an unjustified
reflection or image-closure claim.

`Persistent/Debits.lean` keeps allocation data, discharge/realization data and
the three laws separate. The optional `Discipline` is a proposition bundle,
not a compulsory execution backend. Unrestricted allocation sets remain usable
for provenance. Finite-support observations require decidable debit equality
where needed; graph-free cardinality and freshness helpers do not inherit an
irrelevant Quiver parameter. Allocation-origin existence uses II+III, uniqueness
adds I, and the numerical support bound uses Paid plus finite scope closure.
This fits the architectural requirement to expose only necessary structure.

Support unions, multiset cardinalities, finite sums, disjoint allocation unions,
set images and finite-set maps reuse standard library operations. `PaidWithin`
is clearly a weaker scoped witness condition; the global bound is also derived
from the stronger source-local law through `paidWithin_of_closed`. The separate
`PaidWithBoundary` retains an actual supporting discharge in logical history.
Injective renaming preserves freshness and support/cardinality, while the
weaker provenance/payment maps correctly need only an ordinary function.
No parallel graph library or speculative large interface is introduced.

### Shared execution and preserved observations

`Persistent/Realization.lean` supplies a small step adapter to the unchanged
`Resources.run`, with already realized support as state and an ordinary Nat
charge. `realize_run_balance` and `realize_run_identity` concern the same
state trajectory. Initial support stays explicit, and its position in the
identity is appropriate for accumulated realized support. The existing Nat
potential theorem has the other boundary orientation; this addition does not
replace it or silently equate the two meanings.

`Persistent/Observation.lean` connects list observations to finite-node sums
through exact duplicate-free enumeration. It separates the graph-free exact
identity from Paid/history-closure or explicit-boundary upper bounds. Boundary
credit and initial realized support remain distinct arguments. The adapter
uses existing executor composition in its clients, and injective transport
preserves the same run's state and charge. No additive finite-set cardinality
instance or false additive reweighting is introduced.

The direct Nat cost and finite-set observation are appropriate to this bounded
source argument. General graph/debit parameters and preserved ordinary clients
provide reuse without requiring unrelated categorical or execution machinery.
The unchanged resource interfaces retain their existing contracts.

### Connected cases and statement-review discipline

All five new client modules were read in full:

- `Examples/PersistentHistory.lean` retains actual distinct arrows, nonempty
  cycle/loop paths, reflexive history, a failed antisymmetry conclusion,
  closed/open scopes, graph transport, multiple inputs/results and crossing
  identity labels. Its path, history, transport and closure conclusions use
  the corresponding public results.
- `Examples/PersistentDebits.lean` establishes the separate laws for parallel,
  forked and cyclic graphs before applying the generic bounds. It exercises
  unique provenance, the allocated/unrealized partition and general injective
  renaming. The invented-debit, duplicate-allocation and incomparable-payment
  counterexamples keep the laws nonvacuous and distinct.
- `Examples/PersistentRealization.lean` connects expected costs3 and2, final
  support, composition and renaming to `realize_run_cost`, state/balance laws,
  `run_append` and `realize_run_map`. The independent finite calculations
  distinguish union cardinality from additive observation multiplicity.
- `Examples/PersistentObservation.lean` applies the generic bound to the same
  source-valid Fork data and Nodup enumeration. Repeating an occurrence gives
  cost5 while preserving the finite scope/budget4 and violating Nodup. The
  open-cycle client uses the public boundary theorem and retains internal
  payment0, boundary1 and cost1; initially realized support separately yields0.
- `Examples/PersistentSourceBoundary.lean` reuses actual source observation
  theorems for successful repeated force and handled retry. The comparison is
  explicitly about one body-entry observation. Two attempts with zero cache
  writes remain a counterexample to treating arbitrary body work as one
  address-valued debit.

The proofs preserve independent expected observations while repairing
elaboration, finite-set normalization and lint errors. The handoffs distinguish
those errors from mathematical counterexamples and retain actual failed rounds.
The explicit private-alias unfolding in the final focused correction leaves
the statements and public-theorem connections intact. No new source axiom,
admission, native proof shortcut, proof-budget increase or linter suppression
was found in the inspected diff. This static observation does not replace the
transitive proof audit.

### Integration and public scope

`SquareApplications.lean` imports all four core modules and five clients.
The existing `ProofAudit.lean` imports that entrypoint and selects project
declarations by module origin, including private/generated logical declarations.
The candidate does not modify the audit, check tooling, dependency pins or
existing measured executor. The module layout fits ADR0001 and ADR0010.

`docs/research/pfds-persistent-accounting.md` explains the public APIs and their
mathematical limits. It explicitly retains task10017's concrete incidence,
primitive-cost, memoization/work and timing correspondence. The final wording
about an external supporting discharge correctly leaves temporal order to that
future correspondence. It does not infer chronology from cyclic history or
claim book/chapter completion, arbitrary body-work bounds or host-runtime costs.
No manuscript text or research PDF is added to the source diff.

## Validation evidence inspected

Read-only identity comparison independently established:

- All11 candidate file hashes match the exact manifest.
- All67 recorded focused formal/configuration input hashes match the candidate.
  Queued, start and final captured maps agree, and the record reports both
  queued-input and final-input stability.
- Combined r3 is terminal `finished`, exit0, at
  `eb61c35f911ad0fac36758c878559eaf5f795cfa`. Its raw log ends with successful
  completion of875 Lake jobs. The nine named new module targets are covered.
- The diff from that checked commit to577 changes only
  `docs/research/pfds-persistent-accounting.md`.

The inspected focused record SHA256 is
`801806ab88e673ebaa73be8fc3e6e2f1767871850a92dd6548e6a4e678b5b5e0`;
the raw log SHA256 is
`997451a3e8ab5380aefd07db74c971740c35f72b39f1fafdd6b1ad6ad2515fba`.
These findings permit reuse of matching development evidence. They do not
remove PERSIST-ACC-STD-VAL-001. The supplied ordinary-output transfer also
explicitly copies no approval record.

No compiler, candidate check, optional test, cache mutation, Git/index/ref
change, source edit, tracker change or external write was performed by this
reviewer. Only this assigned report was written. Source inspection and
identity/hash reads are review evidence, not a validation gate.

## Final disposition

Base: `3dd930c3e3989f3e5530463f3ac937a629551335`.
Candidate: `577be121e074ddb5de6727a7481c115cb61b3b27`.
Standards outcome: **Blocked**.
Static findings: **0**. Unresolved validation findings: **1**.
Worst issue: **High**, PERSIST-ACC-STD-VAL-001.
This reviewer remains available for the same loop's evidence or full-scope
correction continuation. No completion or acceptance is granted.
