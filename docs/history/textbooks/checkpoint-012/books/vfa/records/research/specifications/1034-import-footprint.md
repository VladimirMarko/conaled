# #1034 — Narrow foundational import dependencies

This is a bounded cross-cutting correction within the existing Preface/Perm
implementation/review loop, motivated by the user's request for an alternative
to impractically slow emulated tooling and the measured native import footprint.
The user allows cross-cutting work; later chapter formalization is not started.

## Exact change and intended mathematics

Replace only the first-line `import Lean` with `import Init` in `Squares.lean`
and `Dependent.lean`. Preserve every other source byte, including module names,
namespaces, definitions, theorem statements, hypotheses, proof bodies and
checked examples. The intended representations, commutative squares and split
family mathematics remain exactly those of the existing source. No new claim,
axiom, admission, unsafe behavior, resource theorem or source algorithm is added.

The read-only assessment and scratch experiment are recorded in
`validation/1034-import-footprint-plan.md` and
`validation/1033-native-environment/import-footprint-experiment.json`.
Existing clients and `Verification.lean` supply retained connected cases; no
new example is required merely to mirror an import edit. The scratch result
establishes compilation of Squares' unchanged body under Init, not all callers
or Dependent's untested body. The forthcoming checks own those obligations.

## Boundaries and acceptance

Preserve actual metaprogramming imports in graph syntax, declaration records,
emission and audit, and retain specific application tactic imports. Do not infer
an external dependency closure or a universal speedup from the local graph count.
If an actual downstream failure reveals an owning import, diagnose it and make
the smallest justified correction in the existing loop; do not silently widen
this initial two-line scope or restore incidental framework exports without
evidence. Record any changed candidate and carry findings forward.

Checkpoint039, containing the independently accepted native runtime, was saved
before these source edits. Record the clean original source baseline and fixed
enclosing review base. Capture the changed candidate, check all six original
foundations with the documented foundation checker using isolated outputs, then
run the full required fresh and separate guarded candidate checks, exhaustive
audits, managed ProofAudit prerequisite and regression. Preserve actual results
and all required candidate records; the smaller check cannot replace them.

Both independent formal axes must assess the full changed candidate, reusing
unchanged prior analysis explicitly. The fixed enclosing review base remains
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; the previous candidate is
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`. Root final verification and the uploaded
acceptance checkpoint remain mandatory. This correction itself accepts no VFA
chapter and makes no claim about the original integrity incident's cause.
