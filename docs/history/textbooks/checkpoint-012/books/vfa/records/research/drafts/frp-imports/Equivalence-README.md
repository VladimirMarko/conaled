# Bounded FRP Equivalence import prototype

2026-11-02. **The first focused compiler check passed with exit code 0, no
errors or warnings, and no correction.** The four information messages are
the original source's `#print axioms` commands; each reports only
`propext`, `choice`, and `Quot.sound`. This is local #1021 staging preparation,
not chapter acceptance, an integrated audit or authorization to restart the
primary candidate.

## Source and setup identities

`Applications/FRP/Equivalence.lean` replaces only `import Mathlib` with the
thirteen imports recorded in `equivalence-imports.patch`. Every other byte,
including all definitions, proofs and four axiom-printing commands, is
unchanged. `Equivalence.original.lean` preserves the input. Main and candidate
sources have the same original hash and remained unchanged after the check.

| Input | SHA-256 |
| --- | --- |
| Original source | `9ea7d5ef3fc907753df528adce7ad773a217179533f68b3190f475f1fa567a02` |
| Staged source | `0bf867cbfd819fd33dc1a762f17989131a720035ed1b50f65475857b45fb20d9` |
| Import-only patch | `d00eb4e124b78c6d17d97f8034338a557bd05bd0ec04553e71c22836c3b5e365` |
| Constructed setup | `f6d8d6d9ef85b743d06d5f5136201668ecec1b6bbd265a312b4b89ec91c7df00` |
| Setup name-only patch | `328f343e5f81187481b69ed96948e2091c2255551b6748f03b0706f999bf5427` |

The original candidate Equivalence setup did not exist when inspected. This
was reported to the coordinator before compilation. Both modules belong to
the same uncustomized `SquareApplications` configuration. The safe construction
replaces only the single module-name string in the frozen Spec setup with
`Applications.FRP.Equivalence`; `equivalence-setup-name.patch` records that
change. Every other byte is unchanged, including package, empty options,
legacy module mode, plugins/dynamic libraries, and all 9,035 artifact mappings.
There is no imports override. The source-header fallback and name-lookup
semantics are documented in the Spec prototype README.

All eleven explicit Mathlib roots had completed mapped artifacts. The two
explicit Lean-core tactic roots had completed artifacts in the pinned Lean
4.35.0 toolchain. The setup retains those source imports; it does not retain
`Mathlib` as a hidden root. Actual `out/Equivalence.ilean` reports the correct
module name and exactly these direct imports:

```lean
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
```

The generated C initializer declarations independently agree. Extracted
metadata, information messages and artifact hashes are preserved in
`equivalence-postcheck-evidence.json`.

## Command and result

`run-equivalence.py` records the exact command in `equivalence-result.json`.
It uses the same Nix environment as the frozen Spec check, working directory
`/workspace/scratch/0c54f2db1fdf/conaled`, and `LEAN_NUM_THREADS=1`:

```bash
timeout --signal=TERM --kill-after=5s 180s nix develop --command \
  /root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
  /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/Applications/FRP/Equivalence.lean \
  -o /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/out/Equivalence.olean \
  -i /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/out/Equivalence.ilean \
  -c /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/out/Equivalence.c \
  --setup /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/Equivalence.setup.json \
  --json
```

- Start: `2026-11-02T05:42:54.784855+00:00`.
- Finish: `2026-11-02T05:44:44.745613+00:00`.
- Exit code: **0**. Timed out: **false**.
- Diagnostics: no errors/warnings; four original axiom information messages.
- Elapsed whole invocation: **109.961 seconds**, including Nix startup. This
  is an execution record, not a controlled timing comparison or speedup claim.

Only one auxiliary compiler ran, after the Spec compiler had finished.
The timeout covered this complete invocation, with an unused five-second
termination grace period. No primary process was signalled. All compiler
outputs, command records and diagnostics target this staging directory.

## Independent integrity review and boundary

`/root/environment/lean_info_read` independently verified the exact source
replacement, all identity hashes, the name-only setup construction and the
runner's output paths and limits. It found no discrepancy and ran no compiler.
This is not a full independent chapter review.

No source or cache in main or the candidate was mutated. This check did not
run Lake, fetch artifacts, or replace any proof. It establishes the focused
compilation of this exact module under the recorded narrower imports. The
four existing axiom-printing commands do not replace the mandatory exhaustive
integrated audit. Direct clients are separate follow-up checks; no result for
them is inferred from this module's success.

Source, patches, setup construction and evidence are frozen. The copied setup
contains workspace-specific artifact paths and requires the pinned dependencies
to be recreated after workspace loss; generated output files are reproducible
intermediates whose historical hashes are preserved in the evidence record.
