# Prospective targeted dependency-cache recovery

Read-only source reconnaissance, 2026-11-04. This is not the active setup recipe,
a validated project root list, a cache deletion plan, or a completed cache run.
Current pinned dependencies and all validation inputs remain unchanged.

The supplied unmodified kit supports repeatable `setup --module MODULE` and
`cache --project PROJECT MODULE_A MODULE_B` selectors, using dotted module
names. The official pinned Mathlib Cache CLI additionally supports paths and
globs; its default no-root request starts from Mathlib.lean. The kit supports
only its documented dotted-name subset.

Cache/Hashing.lean uses Lean parseImports' for cache-eligible source imports and
HashMemo.filterByRootModules recursively selects roots plus cached imports.
Cache/Main.lean applies that selection to retrieval. Targeted retrieval still
computes its hash memo from the full Mathlib root, so full pinned dependency
sources remain necessary. This can reduce requested artifacts, not necessarily
source hashing or all setup work.

A future validated root list must collect cache-eligible external imports from
EVERY integrated conaled module, including ProofAudit, and auxiliary fixtures.
Do not pass SquareApplications as if this cache planner traversed arbitrary
downstream namespaces. Cache/IO.lean isPartOfMathlibCache filters namespaces.
Core Init/Lean/Lake requirements remain in the complete official distribution.
The kit Mathlib smoke additionally needs explicit Mathlib.Tactic.TypeStar when
using selected roots; targeted setup omits that smoke if it is absent.

The kit requires at least256MiB available before a targeted request; this is a
preflight floor, not a predicted cache size. Its offline unpack has no root
selection arguments. Keep Lean4.35.0, Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679
and all nine exact manifest source revisions. No savings or complete conaled
root list has been certified, and no current cache artifact is marked safe to
delete by this note. Actual full formal checks and regressions remain required.

Sources inspected by the independent advisor: supplied conaled_native.py,
Mathlib Cache/README.md, Cache/Hashing.lean, Cache/Main.lean, Cache/IO.lean, and
the current project/checker/audit fixture import roots.
