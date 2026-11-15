# Local 10023 — independent Spec static continuation, round 3

**Outcome: Blocked.** The complete candidate has no newly identified source or
mathematical specification finding. Retained High source finding
`SIGNED-POT-SPEC-001` remains closed. Retained Blocking validation finding
`SIGNED-POT-SPEC-VAL-001` remains unresolved: the successful focused build does
not supply this candidate's own full build, exhaustive proof audit, matching
candidate verification record, or immediate final verification.

This is the existing signed-potential review loop's static continuation on
2026-11-03. It is not formal acceptance, an operational-toolchain approval, a
review of prerequisite tickets 10013/10018, or chapter/book completion.

## Reviewer, independence, and activity boundary

Reviewer: `/root/chapter02_continuation_plan`, assigned the independent Spec
axis by `/root/direct_toolchain_validation_plan`. Before proceeding I confirmed
that I authored none of the six candidate files or their proof corrections.
My earlier operational Spec report is outside this formal source scope.

I read the complete six-file candidate and the full fixed-base diff, the saved
requirements, pinned guidance, earlier reports from both axes and their
reconciliations, implementation statement reviews, and the supplied focused
evidence. Read-only Git and file/hash inspection established identities. I ran
no Lean compiler, build, test suite, audit, candidate verifier, network request,
runtime probe, process operation, or cache operation. I changed no source,
dependency, controller, tracker, shared finding record, or earlier report. This
report is the only artifact written by this continuation. No nested review loop
was started.

## Immutable scope and evidence identity

| Item | Independently checked value |
| --- | --- |
| Candidate / isolated HEAD | `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` |
| Fixed review base | `5e048f781aa04be9ce993f1e7455bdc82df22bff` |
| Merge base | `5e048f781aa04be9ce993f1e7455bdc82df22bff` |
| Candidate tree | `d3dcf94916de5ccaf3df357e06192e69c4e0cf33` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/signed-potential` |
| Cleanliness | Empty `git status --porcelain=v1 --untracked-files=all` |
| Complete diff | Six files, five commits, 529 insertions, 23 deletions; no exclusions |
| Diff expression | `git diff 5e048f781aa04be9ce993f1e7455bdc82df22bff...3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` |
| Previous reviewed candidate | `d24c443ba22019613b1ce646d6eed7279c791ad6` |

The five commits are `679786087f589caadbe7cc97a1537b6679ec8522`,
`9c47a052ef96b528a85660d4c632704ca03144fe`,
`d24c443ba22019613b1ce646d6eed7279c791ad6`,
`956c4b06abe8d54f78a6166690c12453115f8304`, and the candidate above.
Neither the previous review candidate nor a correction commit replaces the
fixed base.

The dispatch is `session/reviews/signed-potential-3cf-dispatch-r3-042.md`, SHA256
`5751a89ec4aafc91b9c58edc069b98f47c1041cd58d8c04219200b4d2d8e75e9`.
The manifest is `session/validation/signed-potential-review-r3-042.json`, SHA256
`f7f850ebdbf5e7a229108955db55421a8eeae01608fb598f24a7ed563306d3ef`.
Both hashes were checked. The manifest's identity assertions were independently
compared with the actual candidate and retained files, rather than used as
substitutes for that comparison.

All six file hashes agree between the committed blob, isolated file, and
manifest:

| Candidate file | SHA256 |
| --- | --- |
| `Applications/Resources/Potential.lean` | `690b48d41dc0b4b21a62e29d1a67c8b0494b3a0ca9de378e07cca82f415f961e` |
| `Applications/Resources/SignedPotential.lean` | `c839b1e32b3182c5789d05934ea253139d91c338917c1207616fe0043b0ce222` |
| `Examples/PotentialTransport.lean` | `d56fcf0f72cd4aac8615427391fc9e1a807485753ffd185a22e77df9f2db0056` |
| `Examples/SignedPotential.lean` | `6d72c5e1ee5f64ce258f6496389434a9bdd0944fe576773cb41bd828ba9ba9b3` |
| `SquareApplications.lean` | `d5f96d925f272187870e3831a33d2f2ee544ddabb149978fbe9ef65dbd8bb581` |
| `docs/research/pfds-signed-potential.md` | `e7ebb2dd51fec8706a0bba38da9e9a6c0a2eb3aa3a688c5b80a66e6f7cb8dfe5` |

The two example files differ from d24; the other four files are byte-identical
to that reviewed candidate. I retained matching earlier analysis after checking
those identities and still assessed the complete intended six-file scope.

## Governing requirements and retained review evidence

The complete saved requirements are authoritative for this continuation. The
user's later Nix exception changes the environment launch requirement, not the
compiler/dependency pins, mathematical scope, review axes, audit, or acceptance
requirements. The native runtime transition does not turn a historical QEMU
run into the same validation run.

| Requirement in `session/requirements/` | SHA256 |
| --- | --- |
| `signed-potential.md`, version 1 | `bb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81` |
| `REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `REQUEST-direct-toolchain-041.md` | `16845edec15c311e0cfd5ed5d4f5c4feb61e7ad96545653d5b872309d26464bc` |
| `REQUEST-environment-handoff-042.md` | `200789123c60ae137967f881207194412eecea72ba2fc80247978075bd6a4602` |
| `REQUEST-native-toolchain-042.md` | `d76dc8dcf771a227779628de91e75c4b63a2898b95e7b30035de83537dae5195` |

I applied the candidate's AGENTS, README build/audit section, code-review skill
and heuristics, shared review loop, example-driven-development skill and worked
example, architecture/domain guidance, language direction, glossary, ADR index,
and ADRs 0001, 0002 and 0010. All 14 manifest-pinned guidance files match the
candidate, isolated checkout and d24 identities. In particular, statement review
checks actual types, hypotheses, coercions, boundary terms and connected cases;
a closed Lean goal alone would not establish that the intended mathematics was
formalized. `docs/language-direction.md:180` also requires prior concrete
specializations to retain their guarantees when a foundation is generalized.

The earlier independent reports and reconciliations were read in full. Their
hashes agree with the retained receipts:

| Report in `session/reviews/` | SHA256 |
| --- | --- |
| `signed-potential-spec-r1.md` | `63de2736975bbf679e6b4c70fc33b3e5acb45e6466780fc580daefa25329efbd` |
| `signed-potential-spec-r2.md` | `ba71260458cbb3d6fbe358112f47e696018852c7ee3fe947f440fbf3f702b463` |
| `signed-potential-standards-r1.md` | `a629a56cd96e248d070c655881a5fd2fc95b5f263e4abf7c5dfa299bf577dd61` |
| `signed-potential-standards-r2.md` | `b37e8559278160c113914806eb9b6426daf4130521e7afb98438c5860cee9deb` |
| `signed-potential-coordinator-r1.md` | `34f95a71ef5f0f3c68b273605ab8a805ab59ad11d93a6d07a4998be777b6655b` |
| `signed-potential-coordinator-r2.md` | `009aa206bbf655582e0f4e1632e25ced8c8ac7b2be62c624ca5bc80f2ae0e94f` |

I also read the existing `signed-potential.md` finding record and the complete
implementation, transport-client, root-integration and noncomputable-correction
reports in `session/research/`. The current intended-statement correction note,
`session/research/signed-potential-proof-corrections-042.md`, has checked SHA256
`3f83fe3d10caba8da50b9a1c2cb888aecb209c5b3acf141dc23c7237b049dd99`.
These author reports inform the intended meanings; they are not independent
approval or substitutes for actual validation evidence.

## Whole-scope mathematical assessment

### One executor, the actual trajectory, and separate charge observations

`Potential.lean:12` generalizes the existing `budget` recursion in place. A
step still selects the next state through its first projection, and each charge
uses the current state before that transition. Observation type C and charge
type D have independent universes. Only D needs Zero/Add for this definition.
There is no second executor, parallel budget recursion, invariant hierarchy,
or record whose premise already assumes the desired whole-run bound.

`budget_append` at line 17 keeps the second segment's initial state equal to
the first actual run's final state. Zero/Add on C are sufficient for referring
to that run; AddMonoid on D supplies charge identities and association. It does
not unnecessarily demand associativity of the unobserved C totals.
`budget_map` at line 27 uses an additive monoid homomorphism on the same
trajectory, without asserting that an arbitrary function preserves addition
or order. `budget_congr_state` at line 37 requires pointwise equality of next
states and imposes no algebra on either step-observation type. These laws
support the intended transport without defining another evaluator.

I read the unchanged `Measured.lean` and `Workload.lean`: measured bind combines
observations in execution order; `run` recurses through that bind; `reweight_run`
is the existing additive transport law. Their base/candidate bytes match.

### Exact and ordered telescoping have the intended premises

`run_potential_exact` at `Potential.lean:79` requires AddMonoid alone. The local
premise is quantified over actual commands and states:

    stepCost + potential(nextState) = potential(currentState) + charge.

The conclusion retains `runCost + finalPotential = initialPotential + budget`.
The induction prefixes the tail identity with the current cost, reassociates,
applies the local identity, and reassociates again. It does not swap summands,
cancel terms, invoke positivity, or introduce a hidden order/commutativity
assumption. Empty workloads use the additive identities. The ordered-word
client described below exercises precisely this noncommutative claim.

`run_potential` at line 52 uses AddMonoid, Preorder and monotonicity of addition
on both sides. Prefixing the tail inequality and suffixing the current-step
inequality require those respective monotonicity facts; the proof then uses
transitivity and association. It neither assumes nonnegative costs/charges nor
strengthens Preorder to a linear order. The earlier correction of which pinned
addition lemma supplies each side is preserved, with no changed premise.

`run_cost_le_of_nonneg_final` at line 93 adds exactly nonnegativity of the
potential at the actual final state. That permits `cost <= cost + finalPotential`
before applying the ordered telescope. It does not infer this condition from
signed charges, silently remove initial potential, or require positivity at
all states. The explicit negative-final counterexample shows why this premise
is substantive and satisfiable examples show the positive use is not vacuous.

### Existing natural-number specializations retain their meaning

The fixed-base comparison preserves the explicit statements and argument
orders of `charge_iff_signed`, `run_cost_le`, `run_zero_potential`,
`budget_constant`, `budget_le_constant`, `run_constant_charge` and
`initial_potential_matters` (`Potential.lean:46` and 104 onward). In particular,
the signed comparison in `charge_iff_signed` uses Int casts rather than
truncated Nat subtraction, and the constant-budget convention remains
`k * is.length`. The Nat cost-only wrapper discharges the new final-state
condition with `Nat.zero_le`.

I independently confirmed that BinaryCounter, SymmetricCosts, RandomAccess.End,
FIFOContracts, PotentialAccounting, FIFOContracts examples and
RandomAccessEndCosts examples are unchanged from the fixed base and occur in
the focused input closure. Their existing uses of the generalized telescope,
constant budget and append law retain the intended statements. In particular,
FIFOContracts still derives a public bound from its actual local accounting
witness and behavior simulation (`FIFOContracts.lean:35`, 52, 69 and 79),
retains initialization credit once, and transports bounds with an additional
monotonicity premise. The formerly noted possibility of ambiguous dummy zero
in `abstractBudget` is not an outstanding source failure: the unchanged client
is included in the successful focused build. No speculative annotation was
added to its implementation.

### Savings, debt, and explicit remaining obligations

`SignedPotential.lean:17` defines savings charge as cost plus final potential
minus initial potential. `potentialCharge_balance` and
`run_potentialCharge_exact` require AddCommGroup and connect that formula to
the shared exact telescope. The Add/Sub requirements of the raw definition do
not imply a false group identity for Nat subtraction; the laws have the
stronger group premises explicitly.

`debtCharge` at line 41 has the opposite boundary sign: complete cost plus
initial debt minus final debt. `debtCharge_eq_potentialCharge_neg` at line 46
relates it to savings at negative debt. `run_debtCharge_exact` at line 54 reuses
that savings result and rearranges the group equation to

    runCost + initialDebt = finalDebt + totalDebtCharge.

It does not repeat the trajectory induction or delete unpaid terminal debt.
Both source and API note identify this as an identity for the supplied
observations. They leave logical-work allocation, persistent sharing, actual
runtime correspondence and payment before forcing as separate obligations.
No bound for arbitrary aliases or completed persistent debt method is claimed.

### Connected cases and independent expectations

The cases retain the numerical expectations fixed in the requirements before
implementation. Each relevant whole-run accounting claim connects to a public
general law; detached arithmetic reductions are used for actual finite
observations, not offered as substitutes for those connections.

| Case and source | Independent expectation and public connection assessed |
| --- | --- |
| `Examples/SignedPotential.lean:20`, IntSavings | Two cost-1 steps visit 0, 3, 0; charges are 4 and -2, total cost and budget 2. The actual result is stated separately. `run_potentialCharge_exact` supplies the budget connection. The prefix retains potential 3; release from initial state 3 has cost 1 and budget -2, exposing the required initial boundary. The cost-only example supplies actual final nonnegativity. |
| Same file, line 80, NegativeFinal | The step really returns state -1 with cost 1 from state 0. Charge is 0, so exact balance is 1 + (-1) = 0. The public exact law is used while terminal nonnegativity and the proposed cost-only bound are explicitly refuted. No inconsistent hypothesis makes the counterexample vacuous. |
| Same file, line 106, FractionalSavings | Real costs are 1/2 each and states 0, 3/2, 0; charges are 2 and -1, total 1. The public exact theorem proves the total budget; the generic cost theorem receives the actual terminal nonnegativity proof. These are genuine fractional Real examples. |
| Same file, line 135, DebtSign | Complete cost 1/2 and increasing debt 0 to 1/4 give savings charge 3/4 but debt charge 1/4. The debt theorem retains final debt 1/4; complete work exceeds new charge until it is paid. Release has debt charge 3/4 and the two-step budget is 1. |
| `Examples/PotentialTransport.lean:18`, Counter | The original `incWithCost` is reweighted by `Nat.castAddMonoidHom` to Real. `reweight_run` preserves its final bit list and maps its measured cost, for arbitrary n and starting bits. The original `flipCost_potential` supplies the lifted local law, then the generalized telescope and terminal-nonnegative cost corollary apply. Four increments still have writes 1, 2, 1, 3, total 7, final state `[false,false,true]`, final potential 1, and budget 8. |
| Same file, line 88, OrderedWords | A step emits its first token and keeps the suffix as potential. Two steps from `[1,2,3]` emit `[1,2]` and retain `[3]`. `run_append` and the public exact telescope keep emitted prefix before remaining suffix in `FreeAddMonoid Nat`, where arbitrary exchange of terms is unavailable. |
| Same file, line 117, IndependentCharge | Step observations are Nat but charges are words. The actual state increments from 0 to 1 to 2; `budget_append` uses that intermediate state and yields word `[0,1]`, rather than charging the initial state twice. |

I checked the original measured counter implementation and its local law at
`BinaryCounter.lean:176` through 253. The Real client has no replacement
increment algorithm, fabricated measured pair, canonicality assumption, or
whole-run conclusion passed as a premise. `realBudget` at line 34 uses
`budget_congr_state`, `budget_map` and the retained Nat `budget_constant` on the
same trajectory. Its type annotations distinguish the Nat sum from the outer
Real cast. Ordered transport is used only with its explicitly proved premises.

### Public integration and documentation

I read the complete `SquareApplications.lean`; its only task delta adds the two
new example imports at lines 29 and 30. Those imports reach the new resource
core through ordinary modules. No existing public import was removed. The
complete `docs/research/pfds-signed-potential.md` describes the actual minimal
structures, explicit argument conventions, signs, boundary conditions and
connected uses. Its stated limits match the code and requirements.

These are static integration findings. The focused command does not build the
entire public entrypoint or execute its coverage/policy checks and exhaustive
audit. Reading the import list cannot close that validation obligation.

## Proof corrections and retained source finding

The complete d24-to-3cf diff changes only proof expressions in the two example
files. It qualifies ambiguous simp-list names as `Resources.bind` and
`Resources.pure`. It also changes the counter proof's intermediate budget to
`((budget ... : Nat) : Real)`, rewrites `Resources.budget_constant`, and
simplifies the resulting Nat casts. With independent charge codomain D, merely
putting `2 : Nat` inside a function did not force the budget's codomain to Nat
when the surrounding expected type was Real. Fixing the inner type retains
the intended natural-budget transport rather than changing the target.

No public theorem statement, hypothesis, operation body, expected value,
boundary term, or transport connection changes between d24 and 3cf. The
current proof repair follows the actual recorded diagnostics, and the failed
d24 and 956 runs remain separate failures below. No source-policy exception,
proof-budget increase or weakened gate appears in the six-file diff. Absence
of a new forbidden transitive proof dependency still needs the exhaustive
audit; static inspection is not represented as that audit.

**`SIGNED-POT-SPEC-001` — High — Closed, retained.** The two fractional Real
step definitions at `Examples/SignedPotential.lean:109` and 139 retain their
`noncomputable` qualifiers. I independently rechecked the pinned provider
`dependency-store-041/mathlib/Mathlib/Basic/Real/Basic.lean`, SHA256
`f15de163c14198d9b60aeb8ac845b4540c198bbb2e80d6153d0dbc8a6c08936f`:
Real inverse at line 86, Inv at 113, DivInvMonoid at 476 and Field at 481 are
noncomputable. The qualifiers therefore preserve the intended mathematical
specifications without demanding executable Real division. The changed proofs
do not remove or bypass that correction. The 956 native log actually built
this unchanged signed-example file successfully; the matching 3cf focused
build replayed it successfully. Closure is supported by both the unchanged
source correction and matching focused evidence.

The parallel retained Standards source finding names the same former issue;
this report does not replace that axis's independent disposition.

## Actual focused evidence and its limits

I inspected the complete `session/validation/signed-3cf-native-r2.json` and
log. The JSON's SHA256 is
`72a00fc096d8711659e9671d60f54208c6d4c06128237c493d66d25bc1214e45`;
the log's checked SHA256 is
`6afb42222951a284d8e740844eeed7cffab46201ac5a280e0b5a5b047f085952`.
The record identifies native execution, exact requested/resolved candidate
3cf, start `2026-11-03T17:03:40.625809+00:00`, end
`2026-11-03T17:14:27.232243+00:00`, terminal result observed, command exit 0,
wrapper exit 0, clean checkout, and unchanged inputs. Its acceptance field is
explicitly false.

Queued, starting and final snapshots are equal. I read the complete unique
snapshot, including project identity, source/configuration map, manifest,
dependency revisions, controller identities and runtime description. All 44
recorded source/configuration hashes independently match both the 3cf
committed blobs and current isolated files. All five recorded controller/input
hashes match their retained files. The supplied dependency snapshot records the
nine expected pinned revisions with clean checkouts, including Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. I did not run the toolchain or
modify/reacquire dependencies to repeat this evidence.

The actual command is `lake build` for these eleven targets:

- `Applications.Resources.Potential`
- `Applications.Resources.SignedPotential`
- `Applications.Resources.BinaryCounter`
- `Applications.Resources.SymmetricCosts`
- `Applications.Resources.RandomAccess.End`
- `Applications.Resources.FIFOContracts`
- `Examples.PotentialAccounting`
- `Examples.FIFOContracts`
- `Examples.RandomAccessEndCosts`
- `Examples.SignedPotential`
- `Examples.PotentialTransport`

The log ends with successful completion of 935 Lake jobs. That count includes
dependencies and is not a whole-project coverage count. The log explicitly
replays several matching targets and builds `Examples.PotentialTransport` in
this run; this is incremental focused evidence, not a claim that every target
was freshly compiled. It contains module-system migration warnings and does
not represent a warning-free build. The recorded scope includes the four
changed resource/example Lean files, but not `SquareApplications.lean` or the
API note. Those two are bound to the whole candidate by the independently
checked six-file identity, not by the focused source map.

Historical failures were also read and their JSON/log hashes checked:

| Run | Genuine retained outcome | JSON SHA256 | Log SHA256 |
| --- | --- | --- | --- |
| `signed-d24-direct-r1` | QEMU/direct focused exit 1, ending 16:00:25.552628 UTC; ambiguous `bind`/`pure` and unresolved counter budget proof | `1793a0aa7342cdd198925a0ce1d81edc00c81ac978b4eff61ae362ce7aa4904e` | `f5f22a7c680a2893f2d690a45c28b581eb37c83f0421d465b5fe3203a6bf2367` |
| `signed-956-native-r1` | Native focused exit 1, ending 16:57:58.284673 UTC; SignedPotential examples built, but rewriting the still-Real budget as the Nat constant budget failed | `38a8bc2652981b68d773bf31ac6da494890ffe8dbb75fcc45e511325bb8b5fc2` | `b8c9d4ecfc1aae47d4132e31f0031950a58a7e5f1dff5dc5200d212df59231ad` |

Their failure statuses are preserved. Older retained draft failures or unknown
terminal results are not retroactively converted into success. The current
native focused evidence supersedes the old claim that a compiler could not be
run at all; it does not supersede the acceptance requirements.

## Unresolved finding and required continuation

**`SIGNED-POT-SPEC-VAL-001` — Blocking — Unresolved, retained.**

Requirement locations: `session/requirements/signed-potential.md:141` through
the completion paragraph; candidate `AGENTS.md:30`, `README.md:145` through
192, and `docs/agents/review-loop.md:68` through 82. These require normal
public/source-policy coverage, the candidate's own full stock check and
exhaustive audit, a matching successful `.lake/verification.json`, both
independent axes over the complete scope, and immediate stock
`--verify-candidate` before acceptance. Other applicable README tests require
their own evidence or an explicitly justified matching reuse disposition.

The former focused-build part of this finding now has genuine matching success
evidence. The remaining full/audit/record/final-verification obligations are
still absent from this dispatch. The manifest explicitly records no own full
build/audit completion and no own verification record. The separate fresh full
901 prerequisite run concerns a different candidate and cannot close this
finding. An operational-toolchain pass likewise cannot supply it.

Required next action belongs to the existing coordinator/root: after the
resource constraints allow it, validate the immutable 3cf candidate with its
own applicable stock full candidate check, using fresh mode where required by
README and the runtime/cache transition; preserve the genuine complete audit
and matching verification record; retain the required regression evidence or
document applicable identity-based reuse; return those artifacts to the same
review loop; and perform immediate stock final candidate verification before
any acceptance. If source or relevant inputs change, bind the resulting
candidate and reassess the complete fixed-base scope. No new permission or
weaker substitute gate is proposed here.

## Scope boundary and final counts

This bounded algebra prerequisite is consistent with the saved union-of-book-
and-thesis requirements and the permitted cross-cutting exception. It accepts
no Chapter 5/6 algorithm or exercise, supplies no persistent forcing theorem,
and does not advance Chapter 2's earliest-unaccepted frontier or accept the
unresolved predecessor foundations. Source alignment here uses the preserved
requirements and statement-review evidence; it is not a claim of a new
page-by-page inspection of an absent book attachment or complete book coverage.
Local tracking and immediate durable checkpoint obligations remain with root.

| Spec disposition | Count |
| --- | ---: |
| Newly raised source findings | 0 |
| Retained source findings closed | 1 High: `SIGNED-POT-SPEC-001` |
| Unresolved validation findings | 1 Blocking: `SIGNED-POT-SPEC-VAL-001` |
| Open High / Medium / Low findings | 0 / 0 / 0 |
| Overall outcome | **Blocked** |

The report is complete for this static continuation and is frozen when its
SHA256 is sent to the coordinator. Further evidence belongs in a new retained
continuation, not an unrecorded rewrite of this assessment.
