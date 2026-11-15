# XP01 Spec development review — original scope continued

## Current disposition

**Overall: Blocked. The latest complete Spec source assessment is bound to `12cb14fc98b8617b3b625620da8e60936daba340` (T), after the two source corrections to original development candidate `5ffa882bbcb34c1c533710a0c980423484e5a77d`. This is not final approval or acceptance.** The exact mapped-example correction has been assessed in full without a new Spec finding; actual successful successor compilation remains pending. Attempt3 exited 2 in native launcher argument parsing before Lean/Lake ran, so it provides no compiler or source-validation result. Zero XP01 actual public types and no complete candidate check/audit, final two-axis approval or immediate verification are credited.

This current disposition supersedes the earlier source-only and focused1–2 states retained below. **XP01-DOC-001 and XP01-ELAB-001 are resolved for this Spec axis at `cfa413e247c084245a270ae7bcc91fd9ea24b002` (E) and retained by exact source identity at T. XP01-ELAB-002 remains Open pending actual successful matching compilation.** The frozen requirements, original six-path unit, connected cases and required existing clients remain the review scope throughout. The entire preceding 111-line report is preserved in `provenance/xp01-spec-development-20261104/report-before-correction2.md`.

Reviewer: `/root/chapter02_spec`, independent nonauthor of these changes. This work leaves the completed Chapter 2 and pending exact Foundation Spec reports unchanged. Foundation terminal continuation retains first priority. No process was polled, no compiler/check/audit command was run, and no source, branch, dependency, output cache, ticket or global control was modified by this reviewer.

## Original scope and immutable lineage

The frozen requirements are `reviews/potential-requirements.md`, 116 lines/7,148 bytes, SHA-256 `545b5d2ff4a93594f2b1ca245594233bdfcf461b8f4fe14b3bbe698e6ad1aa2f`. The existing loop is recorded in `reviews/potential-round1.md`; this is a continuation rather than a replacement review.

| Identity | Exact commit and meaning |
| --- | --- |
| Original XP01 base B | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Original XP01 draft X | `c28ba71863d2a35ee1c3a089caa90464e4cca692` |
| Historical combined review base | `1aabd512284fe86254278ac631eda061d311050b` |
| Accepted Chapter 1 R | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Pending exact Foundation F | `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |
| Unaccepted development incorporation Z | `4b5dbfa07288acc73f25c27838d3fb2f78e77d71` |
| Initial XP01 development D | `5ffa882bbcb34c1c533710a0c980423484e5a77d` |
| First correction E | `cfa413e247c084245a270ae7bcc91fd9ea24b002` |

I independently checked that B→X and Z→D→E retain the same six changed paths: `Applications/Resources/Potential.lean`, `Applications/Resources/FIFOContracts.lean`, `Examples/MappedPotentialAccounting.lean`, `SquareApplications.lean`, `docs/research/fdsa-potential-accounting.md`, and `docs/research/fdsa-reconstruction-map.md`. All other Z paths are byte-preserved. At D, Potential, FIFO, the mapped example and the new note are exact original X blobs; root and map preserve the full Z incorporation. E changes only two proof bodies in Potential and one documentary qualifier in the map. All six complete D files were read; the complete E diff and relevant contexts were independently assessed, with exact identity retaining the unchanged source. Per-file blob IDs, SHA-256 values and read ranges are in `provenance/xp01-spec-development-20261104/source-and-read-ledger.json`.

The preliminary F+X merge `fa17cf8e0362be37ea6eff169db9f2f3233fab9d` remains historical. Its clean preflight stopped before any compiler command when four exact-Z residual files reappeared across commands. Their bytes were preserved; an ordinary merge subsequently incorporated Z. I read the actual failed preflight and merge records and verified the resulting ancestry/path identities. This neither accepts Z nor reclassifies the earlier stopped preflight as a build failure or success. Protected R/F/Z/X refs remain exact.

The integration route remains F → combined XM01/XD01/XQ01/XU01 → XU02 → XU03 → complete C2 → C3. XP01 does not enter or delay that route. Its eventual acceptance must incorporate accepted prerequisites and pass all applicable gates. Accepted Chapter 1 evidence is preserved, not reopened by this source extension.

## Instructions, primary source and evidence boundary

I read the applicable AGENTS, implementation and code-review skills, shared review loop, architectural-quality/domain rules, example-driven rules and worked example, glossary, ADRs 0001/0010, language direction, and the existing potential-accounting architecture note. The complete frozen requirements, Chapter 19 obligation inventory, both original potential preflights and the development compatibility preparation were read. README 161–248 was reread at the exact candidate; its complete earlier reading is retained by unchanged source identity. Routine source changes do not introduce a fresh-build trigger; the normal complete candidate check/audit and immediate verification remain separate mandatory acceptance gates.

The supplied book PDF hashes to `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`, and the supplied extracted text to `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333`. The complete Chapter 19 text was read using literal-newline lines 9082–9310. An initial Python `splitlines()` range was displaced by PDF control characters and is not credited as that read; the correct newline range was read afterward. To settle the lost Greek/minus glyphs, I rendered and visually read PDF page 234, printed page 228. Equation 19.1 is actual time plus final potential minus initial potential; the telescoped sum retains both boundary terms. The page makes zero initial potential and nonnegative final potential relevant to the cost bound, allows local invariant assumptions, states the distinct two-input formula, and explains pure observers. The source render is preserved in this review's provenance.

The actual book method supports the intended unary signed and invariant-local statements. The prior pinned AFP inspection is retained as attributed preflight evidence: archive SHA-256 `d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a`, `Amortized_Framework0.thy` SHA-256 `905899004289e7a68601a2f416ba33926135f31288c2396a0ae1abcac7133eff`. No original theory seed is available in the supplied workspace; I do not claim a fresh full theory read or Isabelle rebuild. Parent confirmed this boundary. No AFP proof is a Lean dependency, and I found no specific unresolved correspondence claim needing unavailable theory contents. This does not create a general fresh external-proof review gate.

Pinned Mathlib APIs were read directly at `56a005855ea17e0b0958f73ec801ae140b0a1679`: AddZero/AddMonoidHom definitions, additive covariance and generated monotonicity naming, natural additive casts and the FreeMonoid representation. Exact excerpt ranges and file hashes are recorded. These reads establish the source interpretation of existing premises; they do not substitute for actual elaborated types.

## Complete mathematical assessment

The design reuses `Resources.run`, `Measured.bind`, `run_invariant` and additive observation maps. The generalized `budget` follows the same actual state trajectory and reads charges independently of raw work. It introduces no second executor and does not replace actual charges by repeated initial-state charges.

| Frozen requirement | Independent Spec assessment |
| --- | --- |
| 1. Reuse existing execution and observations | Measured/Workload source is exact Z; generic proofs and examples connect to that actual executor. No operational semantics is hidden in the accounting layer. |
| 2. Independent raw C and charge D | The recursive budget needs only zero/addition on D. Append uses raw zero/addition for `run` and an additive monoid on D, with the actual intermediate state explicit. No raw associativity is silently required by the state calculation. |
| 3. Preserve natural-number contracts | All eight retained Nat wrapper headers are byte-exact from B through D and E. The retained initial-credit counterexample also has its exact complete header, including the inner let. FIFO's only source change types its raw zero as Nat, preserving the intended specialization. |
| 4. Additive budget transport | `budget_map` transports only the charge observation via an explicit additive homomorphism. Its induction uses zero/addition preservation along the same states. There is no runtime, monotonicity or order-preservation claim. |
| 5. Invariant-local boundary laws | Exact and inequality theorems quantify arbitrary operation/state/raw/accounting types, preserve P through actual successors, and assume the local law on P. Inequality uses associativity and the stated two covariance directions, preserving operand order. Equality requires no order. |
| 6. Valid final-potential removal | `run_invariant` supplies P for the actual final state; nonnegativity then permits dropping only final potential. Initial potential stays in the conclusion. Zero-initial conclusions explicitly specialize it to zero. |
| 7. Signed telescoping | `budget_amortized` uses an additive commutative group, so source subtraction is signed and justified. The exact budget equals mapped total work plus final potential minus initial potential; negative charges remain allowed. |
| 8. Minimal domains and universes | Independent universes and no payload equality/order, inhabitation or finiteness. Generic inequality has no commutativity, cancellation or linear-order strengthening; subtraction is confined to the group theorem. |

For the core inequality, the cons proof starts from `(currentWork + tailWork) + finalPotential`, associates to add current work on the left of the induction hypothesis, then adds the actual remaining budget on the right of the local law. It ends at initial potential plus current charge plus remaining budget. This is valid in the stated noncommutative additive monoid. The exact proof follows the same order using congruence. The cost-only theorem adds mapped total work to `0 ≤ Phi(final)` on the left, then composes with the boundary inequality. These are the precise sides repaired in E; no stronger mathematics is required.

### Connected cases and counterexamples

The arbitrary binary-counter real theorem derives from the local `flipCost_potential` identity via `Nat.castAddMonoidHom`, the mapped generic exact law and `budget_map`. Actual `incWithCost`, `run`, `counter_run` and `advanceWithCost_eq` connect this to existing counter execution. It is not merely a cast of an already global Nat result. Four increments obtain numeric value 4 and exact work 7; the arbitrary zero-start theorem keeps the final number-of-ones potential.

The initial-credit model clears a natural state at work 1 and assigns integer potential `2*s`. The first charge from state 1 is −1; the next is +1. Actual two-step work is 2, charge budget is 0, and initial credit is 2. The boundary theorem and examples refute both deleting initial credit and adding the initial charge twice. Their focused2 failures concern proof elaboration, not a mathematical inconsistency in those equations.

The fractional model is a total step: valid states 0 and 1 alternate with work 1, while an invalid state incurs work 100. `Valid s := s ≤ 1` is inhabited and preserved. Real potential is one half at state 1 and zero otherwise; actual successive charges are 3/2 and 1/2. Intended one/two-step budgets are 3/2 and 2, and the generic arbitrary zero-start bound follows from the invariant law and zero initial potential. The invalid-state example refutes the corresponding 100≤1/2 local bound. Validity is material and cannot be erased to repair `by decide`.

The ordered FreeMonoid example records the actual word `[1,2]` and invokes the generic exact zero-potential law. It exercises the order-sensitive interface without assuming commutativity. The mapped module has one public named theorem, 14 private named helpers and 16 anonymous examples; those are source categories, not kernel declaration counts. Every private/anonymous statement remains reviewed source and required compilation/audit scope; the explicit public-type program does not reduce that scope.

Later binary two-input/history ownership and persistent-alias questions remain outside this bounded unary exception and open in chapter tickets. The book distinguishes them. No dynamic-table, queue, splay-tree, skew-heap or pairing-heap formalization is credited from these examples; all Chapter 19–23 algorithm-specific obligations remain mandatory.

## Natural-number compatibility

I read complete Measured, Workload, BinaryCounter, SymmetricCosts, RandomAccess/End and SharedDemand modules, the complete changed FIFO module, and all five required existing example modules. All eleven unchanged files are exact Z/D/E blobs. The tracked-Lean name search was inspected, including unrelated local budgets, and found no explicit positional `@budget`/wrapper use requiring a hidden API repair. This is a tracked-source check, not a claim about unknown downstream code.

The counter still counts actual writes, including terminal extension; arbitrary Boolean seeds retain numeric and accounting contracts. Symmetric source charge and structural work remain distinct, with their original potential/initial-credit bounds. FIFO retains Nat instrumentation and actual sequence refinement, existential accounting certificates and sequential initial credit. Its single annotation fixes the newly independent raw-cost parameter without changing behavior or profile values. Random-access end costs still connect actual recursive work and returned representation to the counter boundary. SharedDemand accounts finite remaining work at actual cache states with zero new charge; memoized values and work claims stay distinct.

The eight exact retained header identities cover `charge_iff_signed`, `run_potential`, `run_potential_exact`, `run_cost_le`, `run_zero_potential`, `budget_constant`, `budget_le_constant`, and `run_constant_charge`. The separate `initial_potential_matters` complete proposition is also retained. Source equality is reported as source evidence, not as prior unseen elaborated-type equivalence. Actual focused2 subsequently compiled the corrected generic core and required Nat clients as detailed below.

## Findings and actual focused evidence

### XP01-DOC-001 — resolved for Spec at E

At D, reconstruction-map lines 524–529 described `Resources.erasureSquare` as the only existing public-interface adjustment. In the full current map this was inaccurate because XP01 generalizes `budget` and `budget_append`. I independently confirmed the Standards finding from the full map and source. E begins that sentence “For Chapter 1”; all following universe/semantic/assumption explanation is unchanged. This resolves the factual scope issue without changing mathematics or acceptance status.

### XP01-ELAB-001 — resolved for Spec at E by source and actual core build

Attempt1 actually closed exit 1 at clean unchanged D. Its complete 56-line/8,001-byte outer log, SHA-256 `c6c10d379ced0abb312ea08e533135705d2edb1864d6d08076875cbc517337c2`, reports wrong-sided additive monotonicity at Potential old lines 71 and 148. Only `Examples.SymmetricLists` among the six requested targets actually Built (6.7s); dependent `Ran` entries were not credited.

E replaces three proof terms across two affected theorems: left covariance for the induction hypothesis, right covariance for adding the remaining budget, and left covariance for adding mapped work to the nonnegative-final inequality. There was no distinct old-line-67 compiler diagnostic; its adjacent same-body occurrence was corrected consistently. I read the complete diff, affected proof contexts, complete author handoff and pinned covariance definitions, and verified all 17 package artifact hashes and before/after source copies. All 18 complete Potential headers and all definitions, imports, options, instances, hypotheses and operand order are unchanged.

Attempt2 actually closed exit 1 at clean unchanged E. Its complete 152-line/12,511-byte log, SHA-256 `8fbbdc6d017240e7984585a02ae04afa3d8ed3ca5a46f3767144c5d7558c84a4`, explicitly records Potential Built (3.2s). This actual succeeding core evidence resolves XP01-ELAB-001 for Spec. It does not make the failed aggregate successful.

### XP01-ELAB-002 — Open

The same attempt2 log contains 20 diagnostic headers across eight existing mapped-example proof sites: simplification does not identify the private charge function, unqualified `bind`/`pure` resolve ambiguously, `Valid 0` is not unfolded for decidability, and the resulting terms prevent arithmetic normalization. The sole failing target is `Examples.MappedPotentialAccounting`. The exact signed/fractional values, invariant and initial-credit counterexamples and generic theorem connections remain coherent. Repairs must preserve those statements and definitions; no weakening is needed.

Attempt2 explicitly Built `Examples.PotentialAccounting` (2.2s), `Examples.FIFOContracts` (1.0s), `Examples.RandomAccessEndCosts` (3.4s), and `Examples.SharedDemand` (2.3s), with their changed core dependencies. `Examples.SymmetricLists` retains its actual attempt1 result; attempt2 has no new Built line for it. Both attempts used the qualified native launcher with one Lean thread and private project outputs. Complete outer/native/secured records were read; original native files and preserved copies match, and native output is an exact contiguous part of the outer logs. All warnings shown are module-system import advisories; I do not infer a blanket accepted-baseline classification.

The author is preparing the next exact example correction. No live output, future success or terminal result is inferred here. Failed aggregates remain failed historical evidence.

## Prepared explicit public-type program

I independently reconciled the fully read `provenance/xp01-public-statements20-prepared-20261104/Statements.lean`: 1,002 bytes/28 lines, SHA-256 `ea75026303b461b1bb676e060aaac51e37797cbb2afd3d6356c08ba28c7eb01f`. It imports Potential, FIFOContracts and MappedPotentialAccounting and prints with `pp.universes`, `pp.explicit` and `pp.fullNames` true. The 20 `#check @` names are exactly all 18 public Potential declarations, `Resources.FIFOContracts.abstractBudget`, and `Examples.MappedPotentialAccounting.Counter.real_boundary`, including all eight retained Nat wrappers. There are no duplicate or missing names in this intended explicit public surface.

This is prepared source accounting only: **zero XP01 actual public types have been read or credited**. After the exact successor successfully builds, a matching program run needs actual complete closed output and exclusive qualified pre/post relevant-input observations. Both axes must read every actual type. Qualified build lineage, not a list of hashes alone, establishes the intended input basis. This program does not replace compilation or exhaustive audit of private, anonymous and generated declarations.

## Remaining gates and saved receipt

The original scope is retained. XP01-ELAB-002 needs its exact correction assessment and actual successful focused evidence; all 20 actual type outputs remain pending. Eventual incorporation of accepted prerequisites, complete immutable candidate check and exhaustive permitted-axiom audit, both final independent axes, and immediate `./check.sh --verify-candidate HEAD` remain mandatory. Nix alone is waived; compiler/Lake/dependency pins, narrow native adapter, proof restrictions and normal-versus-fresh rules remain unchanged. No fresh rerun is invented from this ordinary source change.

The source/read ledger records full immutable identities, all eight requirement assessments, exact retained Nat headers, primary-source boundaries and read ranges. `terminal-and-correction1-assessment.json` preserves both complete failed outcomes, all author package hash checks and stable finding dispositions. `prepared20-surface-assessment.json` preserves the exact program inventory and zero-credit boundary. `current-boundary.json` binds these records. Parent-owned checkpoints provide durability. The existing Chapter 2 total of 1,735 actual-qualified public names plus 28 retained-base names is unchanged; this XP01 work adds no Chapter 2, Foundation145 or potential110 credit.

## Correction2 continuation at T — same original scope

The exact successor `12cb14fc98b8617b3b625620da8e60936daba340`, parent E, changes only `Examples/MappedPotentialAccounting.lean`: 166 lines/6,932 bytes, SHA-256 `2c83479daec51deb21ec95e26af816bc0dfaa682fdb5ee76ee28cdf1e681386a`. I read the complete successor, full 61-line diff, complete author readback/receipt, diagnostic map and before/after identities. All 13 manifested package hashes, source copies and the full-index immutable Git diff match. Every other E path is byte-preserved; the Z→T scope remains exactly the original six paths.

An independent declaration comparison confirms all eight definition headers/bodies, seven named theorem headers and sixteen anonymous statements are unchanged. Exactly eight proof bodies change: the private InitialCredit boundary and seven anonymous proofs. The five imports, option/instance surface, contexts, expected values and proof obligations remain exact. This preserves the independently counted one public named theorem, fourteen private named helpers and sixteen anonymous examples; no kernel count is inferred.

The InitialCredit proof now exposes the same charge definition as the explicit lambda `fun _ t => (1 : Int) - 2*(t : Int)` before applying the same `budget_amortized` theorem. This is definitional unfolding inside the proof, with actual state-dependent charges and both boundary terms preserved. Qualifying `Resources.bind` and `Resources.pure` in five reduction lists selects the same already-read executor. The three signed calculations still rewrite through their boundary theorem; the two fractional budget examples still derive their expected values from the generic boundary, rather than replacing the requirement with unrelated arithmetic facts. Four `norm_num [Valid]` proofs establish exactly `0≤1`; they add no instance and admit no invalid state. The invalid-state counterexample, arbitrary-list invariant bound, counter transport and ordered FreeMonoid cases retain their original statements and connections.

Attempt3's complete four-line/327-byte log, SHA-256 `f036d60c526f7886bc2b50149feba30de545d64aeaf86d65bf544c5b2947931b`, and complete request/start/result/secured records were read. The command omitted `run`/`--project` and supplied the checkout as `--state`; argument parsing rejected it before native execution. Actual exit was 2, source T stayed clean and unchanged, and no native record was created. This is retained as a launcher failure, not a mathematical or compiler failure and not successful validation. Root owns the corrected newly named attempt4; no result is inferred here.

XP01-ELAB-002 is therefore source-corrected but remains Open pending actual succeeding evidence. The twenty-name prepared program and its order are byte-identical, with only the mapped source hash changing; zero actual types are credited. The full original mathematical/primary-source/Nat-compatibility assessment is retained, and all final acceptance gates remain. `provenance/xp01-spec-development-20261104/correction2-and-launch3-assessment.json` binds this continuation, the exact old/new declaration accounting, complete package verification and preserved launcher outcome. No earlier C2 or Foundation evidence is altered.
