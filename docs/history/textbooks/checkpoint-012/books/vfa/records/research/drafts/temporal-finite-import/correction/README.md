# Local #1022: bounded Sigma-import correction

Status: **the complete staged Finite module passed** on the sole authorized correction invocation, 2026-11-02. Baseline candidate: `bed44c16cee3e1eff6a4175bad9a7ed50651b927`. This is focused evidence for an import-only change, not validation of downstream clients or acceptance of a ticket, chapter, or full candidate. No main/candidate source, cache, configuration, or primary process was changed.

## Exact correction and preserved history

The staged `SquareKit/Temporal/Finite.lean` replaces the original sole `Mathlib.Tactic` import with:

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Tactic.Convert
```

Every original non-import byte is preserved. Removing just the Sigma import reproduces the initial failed attempt's staged source exactly. That first attempt returned exit 1 after 11.066 seconds because `Sigma.mk.inj_iff` was missing; its source, diagnostics, results, README, and manifest remain unchanged in the parent directory. The earlier read-only proposal's attribution of that lemma to already available core/basic providers was incorrect and remains a preserved historical finding.

Pinned `Mathlib/Data/Sigma/Basic.lean:58` supplies the exact missing theorem. The appended #1022 specification authorized this one concrete import-only correction in a separate directory. No third compiler attempt occurred or is authorized by this evidence.

## Setup and protected inputs

`Finite.setup.json` is **byte-identical** to the actual completed candidate setup: all 3,121 artifact mappings, original name `SquareKit.Temporal.Finite`, package `compilingWithSquares`, `isModule: false`, empty options/plugins/dynlibs, and no imports override. All three direct module mappings already resolve to completed pinned artifacts. No map entry was added, removed, or rewritten.

Forty-five protected identities were verified before and after: original main/candidate source, actual setup/trace, all fifteen mapped artifacts for the three direct imports, pinned environment/dependency configuration, direct dependency sources, completed candidate Finite outputs, and all sixteen frozen initial-attempt files. **None changed.** `inputs.json` and `postcheck-evidence.json` retain complete identities. The initial manifest remains `e26df3b2999dd96a9dca2be99b2c2fd9ad63d8893e5a85addcbbad0afbfd239b` (SHA-256).

## Exact invocation and result

From `/workspace/scratch/0c54f2db1fdf`:

```sh
python3 work-state/staging/temporal-finite-import/correction/prepare.py
python3 work-state/staging/temporal-finite-import/correction/run-check.py
python3 work-state/staging/temporal-finite-import/correction/postcheck.py
```

Only the runner invoked Lean. The actual completed candidate `Finite.trace` supplied its executable, compiler arguments, and complete `LEAN_PATH`. The original `-o`, `-i`, `-c`, `--setup`, and `--json` structure was retained; only source/setup/output paths were redirected to this directory. The trace is preserved as `Finite.original.trace.json`, and its command as `original-command.txt`.

The runner used the main checkout's pinned Nix shell, exact executable `/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, `LEAN_NUM_THREADS=1`, and `timeout --signal=TERM --kill-after=5s 180s nix develop --command …`. The limit covers the whole Nix/Lean invocation. `STARTED.json` and `result.json` record the full executed argument vector and environment additions. The runner starts a separate process session and rejects a second launch once its own `STARTED.json` exists. No build or cache fetch was invoked.

| Observation | Result |
| --- | --- |
| Start / finish UTC | 2026-11-02 06:56:09.941463 / 06:57:02.480798 |
| Elapsed / exit | 52.538727 seconds / 0 |
| Timeout | No |
| Diagnostics | Empty, zero bytes |
| Emitted module | `SquareKit.Temporal.Finite` |
| Emitted direct imports, in order | Fin.Basic; Sigma.Basic; Convert, with the full names shown above |
| Protected identities changed | None of 45 |

The `.ilean` header explicitly lists exactly those three imports, despite the unchanged broad artifact-resolution map. The C initializer declarations independently agree, plus Lean's `Init` initializer. `postcheck-evidence.json` preserves both records. Generated `.olean`, `.ilean`, and `.c` artifacts were hashed after completion, then removed after metadata extraction; the correction's `out/` directory is absent. Nothing was installed into a project cache.

## Downstream and performance boundary

This result checks the complete unchanged mathematical body of Finite, including its Sigma reconstruction proof. It does not certify the 33 production clients that can inherit its imports. A later integrated candidate must undergo the normal review, guarded full compilation, proof audit, and final candidate verification.

The active build's slow `Applications.FRP.Temporal` and `TemporalCausality` clients also inherit `Mathlib.Tactic` through `Applications.Progress.Processors` → `Streams` → `Evaluation`. Evaluation independently imports the umbrella. Therefore this Finite-only correction does **not** remove that broad dependency from those clients. Monitor has a separate umbrella import as well. Both are outside this correction's source scope; root owns their decisions. The 52.5-second focused result is not a controlled speedup measurement and is not directly comparable to the 756-second completed client build.

## SHA-256 identities

The independent `SHA256SUMS` in this directory covers retained correction files only. The parent manifest continues to cover the frozen first attempt.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| Original Finite source | 4,961 | `a5250768a66bb6103b3edb188f4ec370f2e9f9f8937ea066c914b3f6056b90a9` |
| Corrected staged source | 5,031 | `7b0e5af17f860c92c7a8ae5923ff77da493c9bf4562f24d4fd90d5a2ab2fa14b` |
| Actual and staged setup | 2,329,513 | `66b8e39dac0fb306ac3bfad9d0dfdd64a59320187b45256a949e13218d1d0e2f` |
| Result | 2,745 | `11542ab92ee2ced6568f73fc449df030cf444f655ec7c4275f32ef14ddac79e0` |
| Postcheck evidence | 12,811 | `9ede4b0e53ff11fc8b64516c80cfea41f39491d30d39afc3143bb2d5d237ed49` |
| Generated `.olean` (removed) | 724,408 | `5b80d46e6f772e7ec3b8dfeee85ae83f4855da0763f63e276a3592806c8be2d9` |
| Generated `.ilean` (removed) | 14,083 | `1d456a72613a573be79e84fe25ca8c5e9f8bdab8b6874da63e3bf29a764f3c21` |
| Generated `.c` (removed) | 36,713 | `82d6611e9ec77e7ff3bc08d9c1e980ac28e738fd95c03fe46109e0930942faa5` |

Frozen for the parent workflow's integration decision, review, and durability checkpoint. The initial failed result and the successful correction remain distinct.
