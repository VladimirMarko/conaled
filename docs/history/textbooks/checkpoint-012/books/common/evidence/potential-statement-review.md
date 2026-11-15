# Potential integration: intended mathematics and statement review

The governing full integration baseline is `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`.
This is assigned implementation within the coordinator's existing loop, not an independent acceptance decision.

## Missing connection before implementation

The three-head merge retains PFDS's generic same-carrier Potential API, state-budget congruence, and signed savings/debt layer. The separately retained FDSA XP01 donor defines mapped invariant-aware telescoping and signed mapped budgets, absent from the merged owner. Neither API subsumes the other. Existing donor cases already express the intended mathematics; no artificial failing case is required.

## Intended public contracts

Use the mapped invariant-aware exact and inequality proofs as the single induction core. Derive global mapped laws with the invariant True, and preserve generic PFDS same-carrier statements using the identity additive homomorphism. Retain state-budget congruence, weaken budget_map to AddZero, retain all Nat APIs and both signed presentations. The raw work carrier needs only AddZero for mapped run laws; the target needs associative unital addition, and inequality additionally needs a preorder and addition monotone on both sides. Exact laws do not require commutativity, cancellation, or order. Signed subtraction requires an additive commutative group.

The valid-state closure and initial-state premise must follow every induction step. Only the actual final potential must be nonnegative for the PFDS cost-only law; the FDSA invariant-domain bound is a separate convenient sufficient condition. Neither theorem may discard initial credit. Charges follow changing actual states and may be negative.

## Retained discriminating cases and their intended connections

- FDSA arbitrary-state BinaryCounter real boundary: cast the local write/potential balance, then use run_potential_map_exact and budget_map. Expected four-step work seven with one retained final bit, and no canonicality or zero-start premise for the universal law.
- FDSA initial credit: raw Nat work two, Int charges minus one then plus one, budget zero. Uses budget_amortized; refutes dropping initial credit or repeating the first charge at the wrong state.
- FDSA fractional invariant: valid states zero/one alternate with work one, charges three-halves/one-half. Uses invariant-aware exact and inequality laws. State two disproves the unconditional local law.
- FDSA ordered-word observations and PFDS OrderedWords: consume mapped/global exact laws without commuting addition.
- PFDS Counter realRun_transport and realBudget: observe the same actual final state and counted work through reweight_run, budget_congr_state, and budget_map; same-carrier telescope reaches the same mapped core.
- PFDS SignedPotential: negative intermediate charges are allowed; negative terminal potential invalidates the cost-only conclusion; opposite-sign debt retains terminal debt. These exercise the named signed laws and actual-final-state premise.
- Existing Nat consumers: BinaryCounter, DynamicFrontArrayCosts, FIFOContracts, FoldedPrune, GuardedBuild, PricedPrune, RandomAccess.End, SymmetricCosts, and the potential/FIFO example clients.

## Boundaries

No claims of compiled runtime, persistent credit sharing, forcing correspondence, multiple-input amortization, or whole-book acceptance. Root owns public imports, isolated full candidate build/audit, independent Standards/Spec review, and durable save.

## Validation and final findings

Pending focused compilation. See the final handoff and command receipts in this directory.

### Completed statement review

The six mapped/invariant declarations retain the XP01 donor's explicit argument order and assumptions. The two PFDS generic telescopes retain their public statements; their proof terms are now applications of the mapped laws with `AddMonoidHom.id C`. `budget_map` needs only `AddZero` on its two charge carriers. The retained `budget_congr_state` has no algebraic premise on either raw observation. FIFO's Nat annotation resolves the unused raw observation without changing its semantics.

The induction keeps `P` on the initial and every successor state; closure supplies the tail premise. Both exact and inequality laws retain the initial and final potentials in execution order. The inequality proof uses the target's left and right monotonicity explicitly; no monotonicity premise on the observation map is inferred. The source addition is never reassociated. Signed mapped charges use the existing additive-group subtraction, and named savings/debt laws reach this core through the generic wrapper. No extra signed bridge was added because existing connected clients already consume the shared owner.

The donor counter theorem still quantifies all Boolean lists and all natural iteration counts. The validity counterexample at state two prevents mistakenly claiming its fractional local law globally. The unchanged PFDS negative-final-potential example prevents dropping an invalid final boundary; the debt example preserves outstanding terminal debt. Private donor cases remain Lean declarations for the normal exhaustive audit. No hypotheses were weakened merely to obtain compilation, no expectation was changed, and no admissions or new axioms were introduced.

### Focused validation outcomes

- `focused-core.json`: exit 0, 34.20 seconds. Potential plus mapped, reweighted, and signed client modules compiled (905 scheduled jobs, including dependencies).
- `focused-nat-consumers.json`: exit 0, 38.82 seconds. All nine selected existing Nat client targets compiled (652 scheduled jobs, including reused dependencies). Target source hashes remained unchanged during this run.
- All retained core/example input hashes still match the first build receipt. The new mapped example is byte-identical to XP01 donor source. PFDS's SignedPotential owner and both assigned PFDS examples are unchanged.
- `git diff --check` on owned paths: exit 0.
- Ordinary Mathlib-module import suggestions were emitted. They did not indicate a failed proof or changed pin and no broader module migration was attempted.

These are focused live-checkout development results. The coordinator still owns the isolated candidate build, exhaustive audit, public import closure, independent review, final identity check, and durable save. Compiler ownership has been released.
