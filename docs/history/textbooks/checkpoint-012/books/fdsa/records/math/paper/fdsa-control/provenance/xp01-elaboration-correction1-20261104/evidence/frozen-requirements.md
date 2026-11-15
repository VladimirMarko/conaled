# FDSA-XP01 — exact requirements for shared potential accounting

Recorded 2026-11-02 before Lean implementation. This is a bounded cross-cutting
unit under the user's explicit exception. It prepares common accounting used
by Chapters19–23; it does not activate or accept those chapters.

## Governing scope and source

The full governing request is `../REQUEST.md`; all conaled requirements and
the local-ticket/no-GitHub/durable-checkpoint overrides remain in force.
Use the existing implementation/review loop, example-driven development,
minimal-capability architectural guidance, immutable candidate validation,
exhaustive proof audit and independent Standards and Spec review.

Primary source is FDSA July27,2026, Chapter19 printed pp.227–232, especially
the potential method and equation19.1, with later signed/logarithmic
applications in Chapters20–23. Book SHA-256:
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The source inventory is `../research/chapter19-obligations.md`, especially
C19-011–016. The pinned AFP `Amortized_Framework0.thy` has SHA-256
`905899004289e7a68601a2f416ba33926135f31288c2396a0ae1abcac7133eff`;
its exact archive identity is recorded in that inventory. Reference statements
were inspected; no source proof is imported as an axiom and no AFP rebuild is
claimed. The implementation is an extension of conaled's actual interfaces.

Starting shared candidate: `c80eec92f5458eccfd1c34c8314d666c2a1e3847`.
Worktree: `conaled-insertion-costs`, branch `work/fdsa-list-foundations`.
Tracked/index state is clean at this base. Combined shared-foundation review
base remains `1aabd512284fe86254278ac631eda061d311050b`. The frozen Chapter1
validation checkout must remain untouched. No unrelated user file is included.

## Required results and compatibility

1. Reuse `Resources.Measured`, `run`, `run_invariant`, `reweight` and the
   existing trajectory-dependent `budget`. There must be no second executor,
   state framework, duplicate natural budget, or source-specific global
   timing typeclass.
2. Generalize `budget` so the step's raw observation type and the charge type
   may differ. The definition needs only zero/addition on charges; it must
   evaluate charges at the actual successive states of the supplied step.
   Generalize its append law with the genuinely necessary algebra only.
3. Preserve the behavior, call shapes and conclusions of all existing natural
   accounting clients. Add explicit annotations at any formerly inferred raw
   cost literal, rather than allowing an unresolved/accidental carrier choice.
   `Resources.FIFOContracts.abstractBudget` is one identified compatibility
   site. Existing counter, symmetric-list and FIFO clients remain required
   validation targets.
4. Prove additive transport of budget observations through an explicit
   additive homomorphism, if used by the retained connected clients. An
   algebraic cost map alone must not be presented as a runtime claim or an
   order-preserving map unless the latter property is separately established.
5. Prove mapped telescoping with an explicit additive map from raw work `C`
   into accounting observations `D`:

   `h(totalWork) + Phi(final) <= Phi(initial) + trajectoryBudget`.

   Support local laws restricted to an invariant, preserving that invariant
   along the actual execution. Retain an exact-equality version. Require only
   associativity/zero and appropriate left/right order compatibility for the
   additive boundary statements; do not impose commutativity, cancellation,
   a field, linear order or real numbers where the proof does not need them.
6. Recover an upper bound on actual mapped work only with an explicit
   nonnegative-final-potential premise, or a premise proving nonnegativity on
   preserved valid states. Retain initial potential in the general result.
   Derive the zero-initial form by specialization, without silently assuming
   every starting state is initialized.
7. For an additive commutative group of accounting observations, express the
   source signed amortized charge `h(work) + Phi(after) - Phi(before)` and
   prove that its trajectory sum equals mapped actual work plus final minus
   initial potential. Negative charges are permitted. This statement must not
   use truncated natural subtraction.
8. Keep arbitrary request/state universes and avoid incidental equality,
   inhabitance, finiteness or order assumptions on payload/state types. No
   new axiom, admission, partial definition, unsafe proof, native evaluation
   shortcut or kernel-check bypass is permitted.

## Connected cases and statement review

Develop these through public general results, with independently specified
mathematical expectations. They do not replace universal proofs or full gates.

- **Existing counter transported to Real:** use actual `incWithCost` execution
  and its existing local `flipCost_potential` law. Derive the exact real-valued
  accounting identity for arbitrary starting bits and any number of increments,
  preserving both boundary potentials. The generic mapped theorem, not merely
  casting the already-proved global result, must be exercised.
- **Negative charge and initial credit:** a concrete natural-work transition
  with nonnegative potential can have negative signed amortized charge. A
  short composition must demonstrate both the actual work and the state-based
  charge sum through the general result. Its initial potential must explain
  the bound; deleting that term should give a concrete false inequality.
- **Fractional potential with a validity domain:** a small total measured
  transition with a real-valued half-unit potential has a nonempty invariant
  on which the local law holds. Show a valid run through the invariant-aware
  result and an invalid-state counterexample if needed to demonstrate why the
  local premise cannot be dropped. Keep this as an accounting client rather
  than an alleged implementation of a later book algorithm.
- Retain the existing natural accounting examples. Review all new statements
  for quantifier order, satisfiable invariants, cost/value separation, signed
  versus natural arithmetic and the exact trajectory followed by each budget.

## Limits and acceptance

This unit covers shared unary/sequential accounting. It does not prove the
later algorithms, their potentials or complexity bounds. A binary merge uses
two input potentials and needs an operation-history/ownership argument;
arbitrary persistent aliases do not acquire such an argument from `run`.
The corresponding Chapter19 and heap obligations remain open.

Record source correspondence, class assumptions, concrete compatibility edits,
remaining gaps and connected cases in the reconstruction notes. Integrate the
example module through the public entrypoint. Validate a committed immutable
candidate using the normal source checks, applicable focused builds, full
guarded build and exhaustive proof audit; obtain both independent review axes
on that same candidate, and verify its identity immediately before acceptance.
Checkpoint drafts truthfully without assigning validation or acceptance credit.
