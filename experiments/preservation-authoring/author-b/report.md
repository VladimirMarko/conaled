# Author B trial evidence

Frozen candidate: `dc3aad963f49759623728b28dbdb15490ee1567a`.
Start: 2026-10-29T18:50:54Z. Finish: 2026-10-29T18:54:14Z. Total wall time: 200 seconds.
Order completed: B shared, B direct, A shared, A direct. Both tasks completed under identical route assumptions, with no admissions or new axioms. No tracked files changed.

## Attempt timing

These timestamps measure compiler invocations, not isolated thinking time. Setup and public reading ran between start and the first compiler invocation, together with authoring the first file; a pure setup subtotal is unavailable. Cache copy took about 8.94 seconds according to the tool. Nix initialization is included in the first compiler invocation. Shared-first order and subsequent source reuse affect comparative interpretation.

| Attempt | Start UTC | Finish UTC |
|---|---|---|
| BShared01 | 2026-10-29T18:51:45Z | 2026-10-29T18:51:47Z |
| BDirect01 | 2026-10-29T18:52:03Z | 2026-10-29T18:52:04Z |
| BDirect02 | 2026-10-29T18:52:13Z | 2026-10-29T18:52:14Z |
| AShared01 | 2026-10-29T18:52:26Z | 2026-10-29T18:52:27Z |
| ADirect01 | 2026-10-29T18:52:37Z | 2026-10-29T18:52:38Z |
| AllAudit01 | 2026-10-29T18:52:52Z | 2026-10-29T18:53:05Z |

BShared01, BDirect02, AShared01 and ADirect01 compiled successfully on their first actual Lean source submission. BDirect01 was a setup failure: Python unavailable outside the Nix shell, followed by nonexistent source-file error. No failed Lean proof attempts occurred. Initial source discovery also guessed one wrong file path. Failures are retained in `assistance.txt`, the unique log, and conversation tool transcript. No file was overwritten to hide failure.

## Task B statement review and author obligations

Both `twice` declarations quantify over arbitrary contexts, context representations, family A and representation RA, term a with its certificate, substitutions σ and τ with their certificates. The result representation is `reindexRep RA (s.compose t)` and semantic term is `tmSub (tmSub a σ) τ`. No decoder injectivity or additional hypotheses appear. The twice-substituted semantic term agrees definitionally with substitution by `compSub σ τ` in this split family model.

Shared route: learn `CtxRep`, `TyRep`, `TermCert`, `SubCert`, `reindexRep`, `tmSub`, and composition order; apply `ac.reindex (s.compose t)`. It adds no explicit cast or proof obligation beyond the supplied certificates.

Direct route: construct two fields. The code runs `t.code`, then `s.code`, then `ac.code`. The commutation proof forms the context equality from `s.commutes` and `congrArg σ (t.commutes ...)`, transports it through A with `congrArg A`, explicitly casts the decoded value, rewrites with `ac.commutes`, then uses native `transport_section`. This helper was already public; it eliminates an equality by cases. The direct route uses `compose` in its result type as required, but does not call it or `TermCert.reindex` to build certificate fields. One explicit cast expression is written; no new transport helper or wrapper is added.

Each route includes context carrier `Nat × Bool` with decoder `Prod.fst`, family `n ↦ Fin (n+1)`, identity fiber representation, certified zero section, and successor substitution that flips the redundant bit. The concrete result performs two successors and preserves a full `Fin (p.1+1+1+1)` decoded equality to zero. Distinct true/false representations decode equally, witnessed by checked examples. The result uses the corresponding universal construction. These cases demonstrate satisfiable assumptions and preserve the finite-index witness, rather than projecting to its Nat payload.

A unary scalar bound can express a consequence of the output but does not construct an element of the correctly reindexed family or prove the dependent decoded equality. This task needs the equality between decoded contexts, the family action on that equality, and the retained Fin witness. It makes no claim about non-split categorical coherence.

Imports: each B file imports only `Dependent`. Public reading included its implementation, so this is a public-API/source usability trial, not blind independent discovery of its proof.

## Task A statement review and author obligations

Both routes state precisely `∀ t ∈ some '' encodedReachable, (t.map Prod.fst).getD 0 ≤ 1`. Their target is the entire image, not an assumed bounded subset. The none case is outside this specified image and is not used to weaken the theorem.

Shared route: derive optional-image coverage by unpacking its witness; compose it with `encoding_coverage`; supply `State.effects`, the requested optional observation, identity budget map, monotonicity, relation comparison, budget 1 and the native `reachable_effects` bound to `Refines.bound`. The comparison unpacks the actual intermediate tuple and its encoding equality. No cast or helper definition was required.

Direct route: unpack both image witnesses and substitute the encoding equalities; apply `(reachable_effects s hs).le`. This proof is shorter and needs only image witnesses, definitional reduction, and native recovery invariance.

Each route proves `recorded ∈ reachable` from `recovery_can_finish` and `ReflTransGen.single`, then proves membership and the bound for `some (1, (true, true))` through its own universal theorem. Publication and acknowledgment remain distinct Bool components of the tuple; the optional encoding retains both. The scalar observation forgets those components. A reachable acknowledged state proves possibility only. `interrupted_run` and `interrupted_no_ack` in the public source admit indefinite interruption without acknowledgment; no fairness, scheduling progress, physical persistence, or crash durability follows from this bound.

Imports: each A file imports only `Applications.Interaction.EvidenceBounds`, which already imports the bound theorem. Concepts additionally required on the shared route are covered refinement, relational composition, monotonicity and comparison, while the direct route uses native invariant and image elimination. Public optional-coverage example was read before authoring the A shared proof.

## Validation and limits

`direnv exec . lake env lean` compiled each retained successful file. `AllAudit01.lean` combines those exact successful sources, imports `ProofAudit`, and runs `#audit_project_axioms`; the complete diagnostic is retained. Audit passed: 37,994 kernel-safe declarations, 21,467 theorem declarations, 877 project modules, transitive axiom union only `propext`, `Classical.choice`, `Quot.sound`. The individual axiom prints show no axioms for both B constructions and A direct, and the three permitted foundational axioms for A shared.

This scratch validation uses the isolated copied dependency/build cache and is not a fresh whole-repository rebuild or candidate-acceptance record. No nested implementation reviews were launched. Host contention is uncontrolled. Exact model serving revision, token counts, separate cognitive effort and tool-free author time are unavailable. No external model/API spend, private proof hints, designer consultation or other-author record reading occurred. Task protocol and parent prompt are retained separately.
