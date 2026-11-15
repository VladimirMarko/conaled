# XT04 pre-code scope and baseline

Requirements version 1 is frozen before implementation. Exact requirements:
`tree-accumulator-invocation-requirements.md`, SHA-256 `1c97ae18eb32c4ea582e8ee38162fe7963f3ba54394c919e91b7bd92c1b90477`.
Clean baseline record: `tree-accumulator-invocation-start.json`, SHA-256
`57151b60914e5fa5988cd4c08502cc11b6a6377c76f2c801ee78cc7a9c17da7a`.

Initial head/base: `b0fce71fa00b2ff6250b09002176bdc75baf1f46`.
Branch `work/fdsa-tree-accumulator`; checkout `conaled-tree-accumulator`.
Git status was empty under the pinned Nix environment. Only pinned external
`.lake/packages` is linked; no project output is shared. No XT04 source edits,
compiler result or acceptance evidence exist at this freeze.

Root read all three complete source/API/mathematical preflights, whose exact
identities are in the requirements, and directly checked the retained Isabelle
recurrence and arbitrary-suffix theorem. The source uses right-before-left
dependent invocation, primitive cons and the actual returned suffix. The
selected construction composition separately uses XT03's measured fold;
XD01 and XT02 are not dependencies. The raw Add-only observation generalization
is exercised by transport/product and ordered-invocation cases, while natural
costs use the declared source entry tariff.

Accepted repaired Chapter 1, XT01 and XT03 are required before integration or
acceptance of this full unit. All original bases, scope, history and findings
must remain recoverable. The existing Chapter 2-first sequence is unchanged.
Old gate 80227 remains the only compiler/checker activity; no second compiler,
checker or project hash helper runs. Preserve and upload checkpoint 0033 before
implementation. Preflights are not final reviews or acceptance.
