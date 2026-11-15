# FDSA-XU06 starting state and coordination

Recorded 2026-11-02 before Lean edits. Root read all three completed preflights
and the retained original placement plan/assessment before freezing the scope.

## Clean baseline and exact requirements

- Checkout: /workspace/scratch/845aa1048b05/conaled-permutation-placement.
- Branch: work/fdsa-permutation-placement.
- HEAD and fixed review base: a5341221bd3e28d76e3b8ad2bc1683a74621ad5e.
- Branch/path absence was checked before creation through the pinned Nix
  development shell. The resulting Git status was empty.
- Only .lake/packages points to the existing pinned dependency checkouts.
  No .lake/build exists; project outputs remain separate.
- Machine record: permutation-placement-start.json, 640 bytes, SHA-256
  690b13823046df17b871103c4e1da7be5c758afd21d99ce14b307d3cac4ebcd6.
- Full frozen requirements: permutation-placement-requirements.md, 15,590 bytes,
  282 lines, SHA-256
  1769c0550a448d9a5de06b4e926006318723887397f65d4dfabf687bdbef6902.

There are no unrelated files in this new checkout. The main checkout's
unrelated historical ZIP stays preserved and excluded as previously recorded.
No source/compiler/cache/gate state was changed in the active Chapter 1 checkout.
All inherited shared drafts remain unaccepted.

## Public surface and source ownership

The frozen requirements fix exactly five new public results:

1. PermutationOrder.uniformOn_inter_restrictedOrder_eq
   positions hnd hcomplete A E hInvariant xs.
2. PermutationExpectation.beforeCount_relabel priority A π σ hA.
3. PermutationPlacement.indepFun_beforeCount_restrictedOrder
   positions hnd hcomplete priority A hΠ.
4. PermutationPlacement.lintegral_beforeCount_mul_order
   positions hnd hcomplete priority hinj A g hΠ.
5. PermutationPlacement.integral_beforeCount_mul_order
   positions hnd hcomplete priority hinj A g hΠ.

After checkpoint 0037 is successfully saved, root may release non-overlapping
source authoring under this already authorized task:

- Architecture contributor: only Applications/Probability/PermutationOrder.lean,
  its new invariant-event section and necessary imports/header. Keep all prior
  proof bodies and declarations unchanged.
- Root: Applications/Probability/PermutationExpectation.lean's deterministic
  law, the new Applications/Probability/PermutationPlacement.lean, public root,
  source-use document, reconstruction map and all local control coordination.
- Main-case contributor: only Examples/PermutationPlacement.lean. Cover the
  actual Fin3 four cells, new independence, positive/signed weighted and ordinal
  applications, coefficient-bound use, both conditional directions, zero events,
  and the placement-dependent-weight boundary. Use the existing expectation
  fixture. Do not import the new boundary module.
- Boundary contributor: only Examples/PermutationPlacementBoundary.lean.
  Cover the new theorem's empty/full/singleton/tied/Empty and bare-LT boundaries,
  infinite ENNReal weight, generic current-law/integrability specialization,
  and the actual nonconstant two-atom order-marginal counterexample. Retain
  existing global-head/adaptive limitations through their public declarations.
  Use existing fixtures or small local parameters; do not depend on unfinished
  main-case declarations or import the new main module.

Contributors read the complete frozen requirements/start record before edits,
keep work in their assigned file, and stop before handoff. They report complete
file identities, intended claims, case connections, statement assessment and
limitations. No contributor runs a compiler, checker, project hash helper,
Git mutation, remote operation or gate/cache/configuration action while the
Chapter 1 gate runs. Source assessments after authoring are bounded checks
of stopped bytes and do not substitute for either final review axis.

## Recovery and acceptance boundary

The pre-code checkpoint retains the three full preflights, exact frozen
requirements, clean branch/ref, original plans, all earlier source/history
and local tracking. Additional-worktree edits must be committed before the
next checkpoint because uncommitted patch capture covers only main.

Chapter 1 remains active; gate 80227 continues unchanged. Its old candidate
cannot accept the cost-model repair. This shared unit neither delays the
minimal Chapter 2 path nor closes any chapter obligation. All focused/full
validation, exhaustive audit, both final reviews and immediate verification
remain pending on the eventual matching candidate and accepted inherited base.
