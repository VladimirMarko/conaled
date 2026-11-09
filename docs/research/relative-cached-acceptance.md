# Cached acceptance of the canonical emitted graph family

[`CachedEmittedAcceptance.accepted`](../../experiments/relative-graph/CachedEmittedAcceptance.lean) proves the concrete endpoint requested by [#417](https://github.com/VladimirMarko/conaled/issues/417):

```lean
ConLeche.Cached.checkDecls .verified []
    EmittedEnvironment.declarations.toArray =
  .ok EmittedEnvironment.environment
```

The proof uses ConLeche revision `8e166ca53cd1f864b63c13cc1d326d38316d00ea`, Lean 4.35.0, the original `checkFuel = 2^62`, and the empty pin list. The input is the canonical fourteen-record family: three primitive blocks, nine actual native helpers and the two emitted theorem records. The output contains the exact twenty constants, index and projection metadata. Neither the older handwritten graph family nor an unspecified successful environment replaces this artifact.

## Exact operations and clients

[`CachedFamilyInstallation`](../../experiments/relative-graph/CachedFamilyInstallation.lean) composes the existing cached Eq certificate with the checked And and Exists installers and eleven value-record steps. The dependent Exists table retains its carrier universe, predicate-dependent second projection and stored field sorts. Each pending record preserves its declaration kind, position and visibility counter. Every pending check starts with a fresh memo against its recorded prefix of the final index; states within each check are threaded explicitly. `CachedEmittedAcceptance.checkedArray` packages all eleven checks into the pinned `FullyChecked` interface and supplies the exact final-environment join.

The [pure route](relative-emitted-acceptance.md) and this cached route produce the same explicitly named environment. They are separate checked equations. Pure success and the one-way cached simulation theorems were not inverted to construct cached success. No claim of general algorithm equivalence, binary-driver correctness, checker runtime bounds or agreement on all rejected executions follows.

[`CachedAcceptedEmission`](../../experiments/relative-graph/CachedAcceptedEmission.lean) applies upstream cached soundness and existing model conversion. Its `model_exists` and selected `model` retain explicit `SetTheory V` premises; the operational acceptance equation needs no such premise. `closedTruth` instantiates the existing application of both actual emitted theorem records at this cached-derived model. The general source and emission comparisons retain their encoding, denotation, universe and assignment compatibility assumptions.

[`CachedRejections`](../../experiments/relative-graph/CachedRejections.lean) proves three unconditional exported errors for changes to the actual emitted family. Replacing the forward body by a loose bound variable fails at position 12. Replacing its type by `Sort 0` fails the theorem proposition test at position 12. Removing the actual Exists.elim helper leaves the emitted forward body unresolved and fails at shifted position 11. The last error retains the checker's exact `unresolvedConstsErrorL` term because its partial string-literal diagnostic traversal cannot be kernel-normalized to a literal message. These are cached equations, including modified installation and all earlier successful checks, rather than runtime observations or isolated guard claims.

## Proof construction and retained evidence

The proof decomposes actual transitions using existing field, walker, binder, memo and installed-environment equations. Generic positive composition lemmas require successful component operations and exact intermediate states. Memo insertions use the post-body maps. The instantiation cache keeps its original capacity 32000000 and actual overflow behavior. Concrete applications prove the reached branches; they do not assume arbitrary capacity bounds or prime caches externally.

The final matcher assembly needed an explicit equality of whole operation records before projecting their inference and conversion fields. Earlier concrete joins generated small proofs but exceeded kernel normalization limits. Preserving the original conditional in a symbolic wrapper and applying that equality made the checked assembly small. This is an observed proof-construction result, not a general complexity theorem. The backward theorem reuses those generic seams with its own eight lambda binders, four Exists.intro arguments, exact beta comparison and memo states.

The checkpoint records below are historical bounded scopes. Their formerly outstanding obligations are completed by the endpoint above:

- [And former](../../experiments/relative-graph/checkpoint-417-and-former/statement-review.md), [constructor](../../experiments/relative-graph/checkpoint-417-and-constructor/statement-review.md), [pass](../../experiments/relative-graph/checkpoint-417-and-pass/statement-review.md) and [installer](../../experiments/relative-graph/checkpoint-417-and-installer/statement-review.md).
- [Exists installer](../../experiments/relative-graph/checkpoint-417-exists-installer/statement-review.md), [family installation and first nine pending checks](../../experiments/relative-graph/checkpoint-417-pending/statement-review.md), and [private matcher](../../experiments/relative-graph/checkpoint-417-matcher/statement-review.md).
- [Malformed-input controls](../../experiments/relative-graph/checkpoint-417-rejections/statement-review.md) and [complete-family statement review](../../experiments/relative-graph/checkpoint-417-complete/statement-review.md).

Each checkpoint retains source hashes, bounded attempts and capped failure diagnostics. Generation, synchronous checked declaration insertion and rendering are measured separately. Normal-form insertion timing also includes result-definition/equality insertion and code generation. `sizeWithoutSharing` counts expression-tree nodes, not bytes or allocations. Skipped counting is explicitly marked not measured. Early uninstrumented timeouts remain unclassified. No failed proof-construction attempt is presented as a checker rejection.

## Reproduction and acceptance boundary

The portable runner rebuilds a fresh pinned ConLeche clone plus the native and graph dependency closure in a new directory. It reuses external package outputs such as Mathlib, not historical native, graph or selected ConLeche objects. From any working directory, with an absolute checkout path and a new absolute output directory:

```sh
direnv exec "$checkout" python3 "$checkout/experiments/relative-graph/reproduce-acceptance.py" --plan
flock "$build_lock" direnv exec "$checkout" python3 "$checkout/experiments/relative-graph/reproduce-acceptance.py" --run-dir "$new_run_directory"
```

The plan only inventories modules. A real run requires a clean committed candidate. It records source hashes, compiler, pin, module order, commands and results in `provenance.json` and `logs/`. Its `complete` field becomes true only after the exhaustive closure audit and final identity checks. Limits are 120 seconds and 1 MiB diagnostics per native/graph module, 7200 seconds and 16 MiB for the upstream build, and 600 seconds for the closure audit. The audit checks every kernel-safe declaration in the built closure, reports upstream unsafe implementation exclusions, and rejects unsafe local source or forbidden logical axioms. It permits only `Quot.sound`, `Classical.choice` and `propext` as logical dependencies.

Run `test-reproduce-acceptance.py` through the same shell and build lock for runner/audit controls. Plan assertions include the cached endpoint, model client and rejection modules. The ordinary main-repository commands remain `./check.sh --candidate HEAD` followed by `./check.sh --verify-candidate HEAD`. They complement the isolated fresh closure; neither substitutes for the other.

The committed measurements document focused development checks. Final fresh closure, main candidate verification and independent Standards, Spec and supervising originator reviews must be matched to the frozen candidate before acceptance. Development reuse is not such a receipt. The main dependency graph and #107/#108 repair and fresh-author ownership gates remain unchanged.
