# Local #1022: first isolated Finite import check

Status: **failed focused check; no retry performed**. This preserves the sole initial invocation authorized by `work-state/specs/1022-Temporal-imports.md`, against candidate `bed44c16cee3e1eff6a4175bad9a7ed50651b927`. Main/candidate sources, configuration, dependency caches, and primary processes were not changed. No chapter, client, ticket, or full candidate is accepted by this result.

## Exact source and setup

The staged `SquareKit/Temporal/Finite.lean` replaces only `import Mathlib.Tactic` with:

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Convert
```

Every byte after the original import line is preserved; `Finite.original.lean` and `imports.patch` record the comparison. Both main and candidate original sources were byte-identical. The actual completed candidate `Finite.setup.json` already resolves both direct imports, so its complete bytes were copied unchanged: all 3,121 mappings, module name `SquareKit.Temporal.Finite`, package `compilingWithSquares`, `isModule: false`, empty options/plugins/dynlibs. There is no imports override.

The actual completed candidate `Finite.trace` supplied the compiler executable, argument vector, and `LEAN_PATH`; it is preserved as `Finite.original.trace.json`, with its command also in `original-command.txt`. The original `-o`, `-i`, `-c`, `--setup`, and `--json` argument structure was retained. Only source/setup/output paths point into this staging directory.

## Invocation and outcome

The preparation, single compiler runner, and evidence extraction were launched from `/workspace/scratch/0c54f2db1fdf`:

```sh
python3 work-state/staging/temporal-finite-import/prepare.py
python3 work-state/staging/temporal-finite-import/run-check.py
python3 work-state/staging/temporal-finite-import/postcheck.py
```

Only the runner invoked Lean. It ran from the main checkout's pinned Nix shell using `/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, the exact candidate `LEAN_PATH`, and `LEAN_NUM_THREADS=1`. Its wrapper was `timeout --signal=TERM --kill-after=5s 180s nix develop --command …`; the bound covers the entire Nix/Lean invocation. `STARTED.json` and `result.json` preserve the full executed argument vector and environment additions. The runner starts its own process session and refuses another invocation once `STARTED.json` exists.

| Observation | Result |
| --- | --- |
| Start / finish UTC | 2026-11-02 06:52:51.635121 / 06:53:02.701904 |
| Elapsed / exit | 11.066425 seconds / 1 |
| Timeout | No |
| Diagnostics | Two errors, four warnings; 3,329 bytes |
| Protected input identities changed | None of 23 |
| Generated `.olean`, `.ilean`, `.c` | None |
| Emitted direct-import metadata | Unavailable because no `.ilean` was emitted |

The first diagnostic is `Unknown constant Sigma.mk.inj_iff` at staged line 103 (original line 102). The following `funext` fails because the remaining goal is equality of Sigma pairs, rather than the intended equality of their function components. The four unused-simp-argument warnings occur in that same failed simplification. `diagnostics.jsonl` preserves every exact diagnostic; `postcheck-evidence.json` includes their parsed forms.

All 23 protected files retain their before-check identities: original main/candidate source, actual setup/trace, all ten artifacts mapped for the two direct imports, pinned environment/dependency configuration, direct dependency sources, and completed candidate Finite outputs. The empty staging `out/` directory is retained; there are no generated compiler artifacts to remove. No additional compiler, build, or cache fetch occurred.

## Concrete correction identified; not tested

Read-only source inspection after the failure located the missing theorem in pinned `Mathlib/Data/Sigma/Basic.lean:58`:

```lean
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂
```

That file's SHA-256 is `17276000df01bc19e9d16b8293d72c595e27b0b39fd0ed733afeab4adebff361` (11,219 bytes). The preserved setup already contains an artifact mapping for `Mathlib.Data.Sigma.Basic`. This identifies a concrete possible import-only adjustment for the parent's decision; it has **not** been added to this source or compiler-checked. The frozen earlier proposal incorrectly grouped `Sigma.mk.inj_iff` with available core/basic providers. This failed check corrects that attribution without altering its historical record.

## Material downstream impact caveat

The earlier proposal's Monitor caveat was incomplete. `Applications.FRP.Temporal` also imports `Applications.Progress.Processors`, which imports `Applications.Progress.Streams`, which imports `Applications.Progress.Evaluation`; Evaluation independently imports `Mathlib.Tactic` at line 2. The temporal-causality branch inherits this route too. Consequently, narrowing Finite alone would **not** remove the umbrella dependency from FRP.Temporal or TemporalCausality, regardless of Finite's own smaller import closure. Root identified this overlapping path and assigned its separate read-only investigation. This staging task changes no Evaluation or Monitor scope and makes no timing-improvement claim; an 11-second failed elaboration is not comparable to the completed 756-second client build.

## Identities and freeze

SHA-256 values; complete protected identities are in `inputs.json` and `postcheck-evidence.json`, and `SHA256SUMS` covers all retained staging files.

| File | SHA-256 |
| --- | --- |
| Original Finite source | `a5250768a66bb6103b3edb188f4ec370f2e9f9f8937ea066c914b3f6056b90a9` |
| Staged Finite source | `f4bc872664718f8cb4e0d1ca92f01c4129691eb68871958dafd0c3c28dcb738e` |
| Actual and staged setup, byte-identical | `66b8e39dac0fb306ac3bfad9d0dfdd64a59320187b45256a949e13218d1d0e2f` |
| Original completed trace | `f8abf2847a56be49086eabc78203f1c8730640ab8f11e9651d53f70ef58d8039` |
| Diagnostics | `023b96006428caedbe5fcb11fea99102588cb14a6e2a9624c550e54738f406b1` |
| Result | `b845f78e77f2d7520402e0ee376671d5910a586f4c1da664cc08761339478c52` |
| Postcheck evidence | `c35832cb64de1f678b731fbeea4680e1517cef88b32d168e1d6f53b6465f22ee` |

Frozen failure evidence for the parent workflow's decision and durability checkpoint. No retry, integration, review acceptance, or primary-candidate action is authorized by this note.
