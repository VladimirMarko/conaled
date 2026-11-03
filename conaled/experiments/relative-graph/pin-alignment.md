# ConLeche alignment and the ConRon port boundary

Issue [#134](https://github.com/VladimirMarko/conaled/issues/134), inspected
2026-10-25. The selected ConLeche revision remains
`8e166ca53cd1f864b63c13cc1d326d38316d00ea`. It is a strict descendant of the
release revision `67f04630d88718e81aa4d07ab64501f68f105398`; the existing graph
experiment already used the newer of the two investigated revisions.

## History and selected route

In a full upstream clone, the following returns 0; exchanging the two revisions
returns 1:

```sh
git merge-base --is-ancestor \
  67f04630d88718e81aa4d07ab64501f68f105398 \
  8e166ca53cd1f864b63c13cc1d326d38316d00ea
```

The commit dates are October 5 and October 23 respectively. Ancestry, rather
than those dates, determines the selection. See the [upstream
comparison](https://github.com/leanprover/con-leche/compare/67f04630d88718e81aa4d07ab64501f68f105398...8e166ca53cd1f864b63c13cc1d326d38316d00ea).
Lean's pinned [release build configuration](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/CMakeLists.txt)
selects the older ConLeche revision and ConRon
`dd8d8218892c871276b1e569d3decbb368bba1b6`.

The selected local route is ConLeche's pure checker and relative set model on
Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). Its Lake manifest has
no external dependencies. No upstream source patches or local theorem changes
are needed for this alignment. The native emitter and main-project dependency
manifest remain unchanged. The existing graph specializations and `threeStep`
composition retain their statements, including explicit `SetTheory`, model,
membership and denotation premises. `AcceptedGraph.model_exists` still requires
the checker-acceptance equality; `GraphChecks` executes checks and does not
supply that kernel proof.

Run the selected route without the separate historical Lean4Lean diagnostic:

```sh
direnv exec . bash experiments/relative-graph/reproduce.sh --conleche-only
```

The script clones the selected revision, verifies ancestry, builds the selected
upstream theorem closure, compiles all eight local modules from source and runs
the existing exhaustive current-module audits. The default invocation still
runs the Lean4Lean diagnostic too. See [evidence.txt](evidence.txt) for results.

## Separate ConRon alignment blocker

ConRon's pinned [Lake file](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/proof/lakefile.toml)
and [manifest](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/proof/lake-manifest.json)
select the older ConLeche. Its host is Lean 4.35.0-rc3, and the proof build
requires a locally prepared Aeneas library at
`../_tmp/aeneas-lean-v4.35.0-rc3`, with Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`.

Changing that dependency revision alone cannot align the refinement. Newer
ConLeche removes `BinderMeta` and changes `Expr.lam` and `Expr.forallE` from
three arguments to two. Compare the [old expression type](https://github.com/leanprover/con-leche/blob/67f04630d88718e81aa4d07ab64501f68f105398/ConLeche/Kernel/Expr.lean)
and [new expression type](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Kernel/Expr.lean).
Pinned [ConRon Arena/Store.lean](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/proof/ConRon/Arena/Store.lean#L356-L357)
still requires `ConLeche.BinderMeta`. Its binder storage, accessors, interning,
denotation and downstream proofs therefore need a coordinated port. New
checker modes and removed annotation accessors add further interface changes.
A minimal probe importing the freshly built `ConLeche.Kernel.Expr` reports
`Unknown identifier ConLeche.BinderMeta` and prints the two-argument constructors.
This confirms the interface failure; it is not a failed full ConRon build.

The separate obligation is to port the selected arena/Rust-model refinement
chain to this target, provision compatible Aeneas dependencies, and then build
and audit that chain. No ConRon dependency was added or patched here, and no
aligned ConRon build or execution-refinement composition is claimed. The
completed ConLeche route does not depend on resolving this port.

## Capstone assumptions and execution boundaries

The inspected [plain ConRon capstone](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/proof/ConRon/Capstone.lean#L679-L713)
requires `SetTheory V`, initialization, a `ReadsAs` input relation, successful
parsing and preparation, pin-text decoding and interning, verified installation,
arena freezing and successful worker folds covering every pending check. It
concludes a represented environment and `Nonempty (ConLeche.Model V env)`.
These are explicit premises about modeled calls, not guarantees that a driver
establishes them.

The [source axiom guards](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/proof/ConRon/Capstone.lean#L876-L903)
list only `propext`, `Classical.choice`, and `Quot.sound` for the plain capstone.
The embedded-pin specialization additionally depends on
`kernel.pins_text.PINS_TEXT._native.decide.ax_1`, outside our whitelist.
This is source inspection, not an independently reproduced ConRon audit.
A future aligned audit must use the free-pin-text theorem or replace and audit
that embedded dependency; matching theorem names is insufficient.

The [maintainer README](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/README.md)
identifies the driver and Aeneas translation boundary. Neither this inspection
nor the graph experiment proves compiled binary execution, file I/O,
scheduling, C++ kernel equivalence or native-emitter correspondence. Host/target
version separation remains a distinct investigation; compatible Lean 4.35.0
continues to host the selected local route.

## Provenance and licenses

Both pinned [ConLeche](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/LICENSE)
and [ConRon](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/LICENSE)
use Apache-2.0. Inspection and builds use isolated clones. No upstream source
is vendored, no local upstream patches are distributed, and shared dependency
checkouts are unchanged.
