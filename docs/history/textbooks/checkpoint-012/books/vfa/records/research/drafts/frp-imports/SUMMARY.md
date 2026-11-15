# Local #1021: final bounded import-check evidence

2026-11-02. Baseline candidate:
`cba657b43ed57e15962858713b819058e7d3c3ca`.
Requirements: `../../specs/1021-FRP-imports.md`.

**Spec, Equivalence and Finite passed their initial focused checks. Frontier
and Examples.FRP timed out without diagnostics and remain unvalidated by this
prototype.** No check was retried and no corrective source change was made.
No main/candidate source, dependency, cache or primary process was changed.

## Proposed two-file change

`proposed-imports.patch` replaces only the two `import Mathlib` lines in
`Applications/FRP/Spec.lean` and `Applications/FRP/Equivalence.lean` with the
conservative explicit imports checked here. Every other source byte, including
every definition, statement, proof, example, comment and option, is unchanged.
The three client copies are completely unchanged. No client correction is an
integration obligation.

Patch SHA-256:
`897bd8d56ad65cdbb957654fcb819d3ef99f9ddf09dc6783bf2194173d077082`.

| Source | Original SHA-256 | Proposed/checked SHA-256 |
| --- | --- | --- |
| `Applications/FRP/Spec.lean` | `c0b5d8155c574329fac0b4aced18c69322b33f8e4e6bbb5278365a7fc57211f8` | `b5df6de8a4ed0188009b4d35c8508512418a8e980a85300691d3585894d22230` |
| `Applications/FRP/Equivalence.lean` | `9ea7d5ef3fc907753df528adce7ad773a217179533f68b3190f475f1fa567a02` | `0bf867cbfd819fd33dc1a762f17989131a720035ed1b50f65475857b45fb20d9` |
| `Applications/FRP/Frontier.lean` | `582da35f674d141ab3d1e8bda8909982362490b018103a96a2053cef5be91cae` | Identical source; check timed out |
| `Applications/FRP/Finite.lean` | `2230666713793ad16889ac8d1a7f707011c316c13284f0387d276c15b4f232ed` | Identical source; check passed |
| `Examples/FRP.lean` | `ea92d7810565ba525f03cd68c5b68e86dd2dde74bf0e11c7011a3948776dc0ab` | Identical source; check timed out |

## Exact observed outcomes

Each invocation used the pinned Lean 4.35.0 compiler through the Nix shell,
`LEAN_NUM_THREADS=1`, and `-o/-i/-c/--setup/--json`. Only one auxiliary compiler
ran at a time. The 180-second limit covered the complete Nix/Lean invocation;
the five-second kill grace was available to the timeout wrapper. Reported
durations include Nix startup and are not a controlled performance comparison.

| Module | Exit | Whole invocation | Diagnostics and emitted output |
| --- | --- | --- | --- |
| `Applications.FRP.Spec` | **0** | 60.455 s | No diagnostics; `.olean`, `.ilean`, `.c` emitted |
| `Applications.FRP.Equivalence` | **0** | 109.961 s | No errors/warnings; the four original axiom-information messages; all three outputs emitted |
| `Applications.FRP.Frontier` | **124** | 180.062 s | Timeout; empty diagnostics log; no output artifacts |
| `Applications.FRP.Finite` | **0** | 88.378 s | No diagnostics; all three outputs emitted |
| `Examples.FRP` | **124** | 180.066 s | Timeout; empty diagnostics log; no output artifacts |

The Equivalence information messages report `[propext, choice, Quot.sound]`
for each of the four declarations already named by the original source.
They are not a replacement for the required exhaustive integrated audit.
Neither timeout establishes successful client elaboration or identifies a
missing import; no speculative correction was made.

## Setup and dependency evidence

The original Spec setup was copied exactly. No original setup for Equivalence
or any of the three clients existed when its staging input was prepared.
Constructed setups are explicitly labelled in their identity records. All
retain the baseline package, empty options, legacy module mode, empty
plugin/dynamic-library lists and original artifact-resolution map. They have
the actual module name and **no explicit import override**.

Equivalence changes only the module-name string in the frozen Spec setup.
The client setups retain every non-overridden base mapping and explicitly map
completed dependencies as follows:

| Client | Explicit artifact mappings |
| --- | --- |
| Frontier | Checked staging Spec; completed candidate `SquareKit.Relations` and `Squares`. The latter dependency is taken from Relations' actual setup. |
| Finite | Checked staging Spec and Equivalence. |
| Examples.FRP | Checked staging Spec, Equivalence and Finite; completed candidate Squares. |

The mapped dependency hashes were checked before and after each invocation.
Actual emitted `.ilean` metadata identifies the five intended Mathlib roots
and two existing SquareKit roots for Spec, the thirteen intended roots for
Equivalence, and the unchanged Spec/Equivalence roots for Finite. Neither
changed root retains `Mathlib` as an umbrella import. Generated C initializer
declarations corroborate those direct-import records. Failed client checks
have no emitted-import metadata; their expected source imports are recorded
separately and are not labelled as compiler output.

## Retained files and cleanup

| Evidence | Files |
| --- | --- |
| Spec inputs and outcome | `README.md`, `identity.json`, `imports.patch`, `Spec.original.lean`, `Spec.setup.json`, `run-initial.py`, `initial-result.json`, `initial-diagnostics.jsonl`, `postcheck-evidence.json` |
| Equivalence inputs and outcome | `Equivalence-README.md`, `equivalence-identity.json`, `equivalence-imports.patch`, `equivalence-setup-name.patch`, `Equivalence.original.lean`, `Equivalence.setup.json`, `run-equivalence.py`, `equivalence-result.json`, `equivalence-diagnostics.jsonl`, `equivalence-postcheck-evidence.json` |
| Client identities and outcomes | `frontier-*`, `finite-*`, `example-*`; the corresponding original source copies, setup JSON files and `run-*.py` scripts |
| All staged sources | `Applications/FRP/` and `Examples/FRP.lean` |
| Final proposal and outcome index | `proposed-imports.patch`, `summary.json`, this summary |
| Generated-output removal and final identities | `cleanup.json`, `FREEZE.json` |

Before cleanup, output hashes and extracted metadata were retained in the
postcheck evidence files. Only generated files under `out/` were removed after
all client invocations ended and no auxiliary compiler remained. The recorded
hashes describe historical outputs, not files expected inside the checkpoint.
Source, setup files, scripts, patches and logs remain available for recovery.
The setup paths are workspace-specific: restore the pinned dependencies and
appropriate artifact maps, and recreate `out/`, before reusing the runners.

The Spec and Equivalence input/runner identities received separate read-only
integrity reviews from `/root/environment/lean_info_read`. Those reviews found
no discrepancy and did not run compilers. They are not mandatory chapter
Standards/Spec reviews or a claim about the timed-out clients.

## Remaining gate

The two-file patch is a proposed **unaccepted** change. The coordinator may
integrate it according to local #1021, preserving the superseded attempt's
actual status and validating the resulting clean candidate normally. Full
integrated compilation, the output-integrity guard, exhaustive audit,
proof-audit regression, both independent review axes and final exact-candidate
verification remain required. That gate must resolve Frontier, Examples.FRP
and the remaining transitive clients. No focused success or timeout substitutes
for it. No book chapter is accepted by this prototype.
