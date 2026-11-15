# Evaluation import proposal for local #1022

Read-only preparation, 2026-11-02. No compiler/build was invoked, and no source,
candidate, cache, configuration, or existing process was changed. This is an
uncompiled proposal, not a validation result or a performance claim.

## Exact proposed edit

Replace only line 2 of `conaled/Applications/Progress/Evaluation.lean`:

```lean
import Applications.Optimization.Relations
import Lean.Elab.Tactic.Omega
```

Keep every other byte unchanged. Current source is 5871 bytes, SHA256
`8882235188cd0e293f3433d220b677f160b539f4829f899ed2a911c655ca059f`.
The proposed single-line replacement, computed only in memory, is 5879 bytes,
SHA256 `3be90be15e37dd6f0fc12ef43e60ea2d4a1caf85b6de7471c4aeeb0a7696233d`.

## Complete-file inspection and providers

The entire 148-line file was inspected. Its only arithmetic tactic is `omega`,
at lines 78, 82, and 83 in `search_complete`. The other proofs use ordinary Lean
induction/cases, simp/simpa, split, constructor reasoning, rcases/rintro/obtain,
and explicit Sum, Option, Prod, decidability, and Nat addition facts. No Aesop,
norm_num, linarith, convert, positivity, or other specialist Mathlib tactic
occurs. The Set specification and relational representations at lines 96–108
already come from the unchanged first import.

The pinned source gives a direct existing public tactic-support path:
`Applications.Optimization.Relations:2` → `SquareKit.Relations:1` →
`Squares:1` (`import Lean`) → `Lean.lean:18` → `Lean/Elab.lean:21` →
`Lean/Elab/Tactic.lean`. The latter publicly imports RCases at line 31, Omega
at line 36, and Simpa at line 37. `Lean/Elab/Tactic/RCases.lean:521,534,554`
registers rcases, obtain, and rintro. `Lean/Elab/Tactic/Omega.lean:9` publicly
imports its Frontend, whose lines 703–704 register `evalOmega`.

Thus the proposed explicit Omega import documents the local arithmetic tactic;
it adds no new functionality beyond the existing Lean dependency. No additional
Nat, Option, or RCases import is indicated by this inspection. In particular,
`Mathlib.Data.Nat.Basic` already occurs in the unchanged dependency closure via
Optimization.Basic → Order.Filter.Extr → Data.Finset.Lattice.Fold → Order.Nat →
Data.Nat.Find. Removing the line entirely might suffice, but is not this proposal.

## Remaining umbrella and source graph evidence

`Applications.Optimization.Relations` directly imports only
`Applications.Optimization.Basic` and `SquareKit.Relations`. Basic imports
`Mathlib.Order.Filter.Extr` and `Mathlib.Order.Hom.CompleteLattice`. Their resolved
source closure contains neither the full `Mathlib` nor `Mathlib.Tactic` umbrella.
It does retain **`Mathlib.Tactic.Common`** and **`Lean`**. A verified Common path is
Basic → Order.Filter.Extr → Data.Finset.Lattice.Fold → Data.Multiset.Lattice →
Data.Multiset.FinsetOps → Data.List.Infix → Data.List.Basic → Tactic.Common.
Common still imports Aesop, Qq, Plausible, and numerous common tactics. Those
dependencies are outside this single-line proposal.

| Source closure, including the named root | Project/package modules | Mathlib modules |
| --- | ---: | ---: |
| Optimization.Relations, unchanged | 704 | 424 |
| Evaluation, current | 3126 | 2837 |
| Evaluation, proposed | 705 | 424 |

Counts came from an in-memory source-import traversal with nested block comments,
line comments, and strings masked; ordinary/public/meta imports were followed.
Distinct resolved module names were counted under the repository and manifest
package roots. Distribution Init/Lean/Std/Lake modules were excluded and not
traversed; no unresolved non-distribution imports remained. These are source
graph counts, not measured loading, memory, elapsed time, or compiled-artifact
counts. Both Evaluation closures contain five project modules.

The known second route is FRP.Temporal:3 → Progress.Processors:1 →
Progress.Streams:1 → Progress.Evaluation:2; TemporalCausality imports Temporal.
Narrowing Finite alone leaves this route to Mathlib.Tactic. No estimate here
assumes the superseded Fin.Basic/Convert-only Finite proposal; root's corrected
Finite prototype also needs Sigma.Basic. No other umbrella roots were changed.

## Exact inspected identities and limits

Lean is pinned to `leanprover/lean4:v4.35.0`; Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679`. SHA256 identities:

| Path (repository-relative unless identified as Lean distribution) | SHA256 |
| --- | --- |
| `Applications/Optimization/Relations.lean` | `b7927580cfe5b9ba783d1d072d6d0f6859d06ab7c694ddb71ce4e835bed02319` |
| `Applications/Optimization/Basic.lean` | `3d50b415897412b28740b14073941841a9cfdb5c583fdc13aef923671cb2f109` |
| `SquareKit/Relations.lean` | `33d07aa8ea8df37a6264df39193ac3485254726c8a6859703f1e689c78ac6c03` |
| `Squares.lean` | `2556c4c895a747bc0092239b5dc5b220e8a6d4d6cf8a6f9fe66ab96fa2462dc7` |
| `lake-manifest.json` | `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean` | `4797f266ffecc82398b8a434cb3d6fd1c62f1849fef8b7e6fceea23f328052c8` |
| `.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean` | `395d1611fc233e70ae3915c1133c0ebb1c251251bb178dec93612e35bfaa57c9` |
| `.lake/packages/mathlib/Mathlib/Tactic/Common.lean` | `7ac187f6724a3254dbb6f9b73f59d857fca95caa822a84d8edb9e7e61a592452` |
| Lean distribution `Lean/Elab/Tactic.lean` | `912825b0028453b426cc17293adb962d2bc03cac66b68f9c0924eea8d759e03d` |
| Lean distribution `Lean/Elab/Tactic/Omega.lean` | `7a81cef2ff724f9f690993d01aef906b200ca11c36f72fb57f9e6e5eaf4ec45e` |
| Lean distribution `Lean/Elab/Tactic/RCases.lean` | `8bcaa6cb582761e2673dcb4b756bc78d67d588bca6ba036f9bfbad35699a22b3` |

Pinned distribution sources were read at
`/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/`; no executable was run.
Source inspection cannot establish that unchanged simp calls, ambient instances,
or downstream clients elaborate after an import change. A focused exact-byte
prototype and the existing candidate gates remain necessary if root selects this
proposal. This note supplies input to that decision and starts no new work loop.
