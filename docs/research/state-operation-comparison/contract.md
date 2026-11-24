# Frozen state-operation comparison contract

Frozen before implementation of #519, at base
`8dd63d2df5ff8cef5967493dd21de10ee66d5574`. This is a bounded implementation
comparison by one author, not an independent productivity trial.

Native inputs are the existing FreeMonoid Nat prefix action on X = List Nat,
Y = List Nat × PUnit, the explicitly supplied listPair equivalence X ≃ Y,
observer lengthObserve, state point [4] identified with ([4], unit), and result
constant 17. The independent binary operation on Y concatenates first components
and returns unit in the second. Its supplied side equations are associativity
and two unit laws for ([], unit). The state point is not this unit. No equation
identifies the result constant with the point observation.

All three routes must construct a binary operation on X, recover the whole
supplied operation through the chosen equivalence, transport associativity and
both unit laws, and recover ordered concatenation and length observations.
The original native action and observation Combination remains available unchanged.
Actual shared operation names require an explicit preservation/agreement equation;
carrier equivalence alone supplies none. Prefix distribution over both arguments
must be rejected, including alternative carriers with exact recoveries.

Routes, fixed before implementation:

1. Direct native conjugation with explicit recovery and side-law proofs.
2. A small operation transport helper for a supplied equivalence and an operation
   on tuples of a supplied index type, with exact tuple recovery. Native binary
   extraction and law transport remain callable without a signature. Reuse
   Mathlib algebraic transfer where its operation/law hypotheses fit.
3. Mathlib first-order language structures, with only binary concatenation and
   its nullary unit initially. Reuse inducedStructure, inducedStructureEquiv and
   HomClass.realize_term; derive open-equation transport and specialize the same
   recovery/laws. No new universal signature framework or extra mixed axioms.

After these interfaces are implemented and frozen, select a further independently
supplied operation of a different arity. Record the selection and any interface
changes; do not rewrite the initial contract or hide failed attempts. Compare
reused proof obligations and remaining native/signature caller work.

If the resulting operations can form native FIFO Ops, check an interleaved client
(enqueue 8, enqueue 9, delete, enqueue 4) from [] against independently specified
state [9,4] and head some 9. Also recover all native command runs and retain the
original relational Simulation under its original, noninvertible hypotheses.
Do not require equivalences for existing relational clients or migrate them.

The Boolean/list/independent-result-constant and universal singleton/invariance
rejection clients from #437 remain checked. Any extra side equation is explicitly
supplied or proved for the concrete independently supplied operations. State exact
universe, computability, modeled-cost and measured-execution boundaries. Full
integrated audit and independent Standards/Spec review are required.
