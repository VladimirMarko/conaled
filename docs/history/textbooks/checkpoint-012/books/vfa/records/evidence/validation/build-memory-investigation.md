# Build memory investigation: output flags and import selection

2026-11-02. Bounded **read-only** source investigation; no compiler/build
experiment, process signal, cache hint, configuration change, main-source
edit, or validation-output mutation was performed. This note is the only new
artifact. The coordinator will continue the existing guarded incremental
candidate validation and retain its reusable outputs.

## Finding and evidence boundary

**The pinned implementation does not support restarting solely to omit `-i`
and `-c`.** Omitting `-i` skips a final reference-analysis/JSON-output stage;
it does not disable InfoTrees, server-independent snapshot retention, or
imported environments. Omitting `-c` skips the later C-emission pass and its
output buffer; it does not by itself disable ordinary elaboration-time
compilation or `.olean`/IR serialization. Whether those omitted stages
materially affect peak memory here is unmeasured.

The existing logs provide a useful caution: unchanged
`Applications.Resources.Measured` took **26s** in the focused main-checkout
build (`../staging/unary-costs/resources-build.txt:3`) and **226s** in the
isolated candidate build (`1002-candidate-cba657b.log:1277`). Both use stock
Lake's `-o/-i/-c` output path. The focused `Workload` and `Potential` builds
took 61s and 48s. These observations show substantial variation with the same
output flags; they are not a controlled comparison of those flags. The
coordinator reports continuing paging during the single-worker validation.
The earlier four-worker cgroup observations are separately preserved in
`1002-build-restart.md`; this investigation made no new memory measurement.

## Exact repository paths

`conaled/scripts/check.py:70–109` builds each fresh-mode module with
`[lean, "-o", target, source]`, in dependency order, with bounded worker count.
Its fresh branch at `:312–325` places outputs in a private temporary directory
under `.lake`, sets `LEAN_PATH` to that directory plus dependency build roots,
and separately compiles/runs the exhaustive audit using those outputs. The
temporary project outputs are deleted on exit and cannot advance the ordinary
incremental project cache.

The incremental branch (`:292–311`) runs the integrity guard, then
`lake --no-cache --rehash build +Module ...`, verifies outputs again, and runs
the audit explicitly through `lake env lean`. Stock Lake constructs the
per-module compiler command with `-o`, `-i`, `-c`, `--setup`, and `--json` in
the ordinary non-postponed configuration. `lakefile.toml` supplies no custom
compiler-option override. Both acceptance modes retain the source/coverage,
version, candidate-identity and exhaustive-audit requirements.

## Pinned Lean/Lake source findings

Inspected toolchain: Lean **4.35.0**, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Source pointers below are relative
to `/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/` in this
workspace, or to `src/` at that exact upstream commit.

| Question | Source evidence and consequence |
| --- | --- |
| What does `-i` enable? | `Lean/Shell.lean:351–352` sets only `ileanFileName?`; `:553–558` forwards it to `runFrontend`. It does not set `Elab.inServer` or an information-recording option. |
| Are InfoTrees absent without `-i`? | No. `Lean/Language/Lean.lean:523–540` initializes `infoState.enabled := true`, and `:697–714` populates the per-command InfoTree snapshot independently of the output filename. `Lean/Elab/InfoTree/Types.lean:29–44,73–85,313–325` describes the contexts stored and the enabled default. |
| What is retained? | `Lean/Elab/Frontend.lean:288–292` defaults to command-line snapshots regardless of `-i`. `Lean/Language/Lean.lean:649–653,686–695` discards nonterminal syntax/parser state and much reported command metadata; it would be wrong to say all full command states remain. The separate InfoTrees remain. `Frontend.lean:335–347,413–415` constructs/reports the snapshot graph and ultimately uses `Runtime.forget snaps`, rather than adding an earlier discard path when `-i` is absent. |
| What does `.ilean` contain? | Only when requested, `Frontend.lean:391–402` gathers InfoTrees, finds nonlocal module references, converts references/declarations to LSP data and writes compact JSON. `Lean/Server/References.lean:205–217` defines format version, module name, imports, references and declarations. This is additional traversal/output work, not serialization of the raw InfoTrees or full elaboration state. |
| What does `-c` add? | `Lean/Shell.lean:562–567` calls `Compiler.LCNF.emitC` after `runFrontend` returns, then writes the resulting string as UTF-8. `Lean/Compiler/LCNF/EmitC.lean:122–126,1174–1187` has a complete string buffer, mangling caches, and arrays of collected local/imported declaration information. This is real additional work and potentially additional live data overlapping the retained environment/snapshots; its size here is unknown. |
| Does `-o` alone avoid compilation/IR? | No general such conclusion follows. `Lean/Compiler/Options.lean:44–47` defaults `compiler.postponeCompile` to false. Eligible definitions compile during elaboration; the selection excludes theorems and definitions marked noncomputable (`Lean/Elab/PreDefinition/Basic.lean:134–141,207–223`). `Lean/Elab/Frontend.lean:385–389` invokes `writeModule` with IR writing enabled unless compilation is postponed. |
| Does removing `-i` remove `.olean.server` output? | No: `.ilean` and `.olean.server` are different artifacts. `Lean/Environment.lean:1902–1918` writes exported, server and private `.olean` parts for module-system sources, plus enabled IR parts, through `-o`; legacy sources write one `.olean`. |
| Where does Lake choose these outputs? | `lake/Lake/Build/Module.lean:890–899,993–1002` supplies artifact paths. `lake/Lake/Build/Actions.lean:29–58` adds `-o/-i/-c`, writes the setup JSON, and adds `--setup/--json`. The conditional postponed-compilation branch is explicit; changing it is outside this investigation. |

The imported environment is another independent lifetime: the header path
uses `processHeaderCore (leakEnv := true)` (`Lean/Language/Lean.lean:501–505`),
and `Lean/Environment.lean:2369–2412` retains imported compacted regions and
marks the imported environment persistent. Removing `-i` does not change that.

## Import selection is a separate difference between the modes

`Lean/Elab/Import.lean:150–160` selects `.exported` for ordinary module-system
compilation, `.server` for module-system server mode, and `.private` for
legacy source. `-i` does not change that choice.

Lake's setup supplies an explicit import-artifact map. In that route,
`Lean/Setup.lean:95–106` filters `.olean.server` unless server data is needed
or the private part depends on it; `Lean/Environment.lean:2231–2248` uses the
specified artifact parts. Lake does list the server path uniformly
(`lake/Lake/Build/Module.lean:488–527`), but listing it does not mean the
loader always reads it.

Without a supplied artifact map, the loader instead finds modules from the
search path and opportunistically reads all three `.olean` parts of a
module-system dependency (`Lean/Environment.lean:2079–2092`); the corresponding
IR fallback reads available IR parts (`:2094–2106`). The repository's fresh
command does not pass `--setup`, so this is an additional possible difference
from Lake, independently of `-i/-c`. It can make fresh mode load **more**
artifact parts for some module-system import graphs. Physical mappings,
resident pages, and the extension data exposed by the environment are still
different observations; this source inspection does not quantify their RSS.

`Resources.Measured` and `Squares.lean` use legacy imports; the latter imports
`Lean`. Legacy compilation already requests private/transitive information
(`Environment.lean:2110–2131`), so the module-system filtering opportunity must
not be assumed to reduce this example's imports. Fresh mode is not a general
way to avoid the broad Lean environment imported by `Squares`.

## Would an isolated one-module experiment help?

A single `-o`-only run could give a useful local time/RSS/page-fault observation,
but comparing it only with the historical 26s/226s timings would not isolate
the flag effect. A matched comparison could be informative if a later concrete
diagnostic need justifies it. **No experiment is currently recommended or run**;
the ongoing guarded validation should continue without competing compilers.

For a later authorized diagnostic, keep the exact source, compiler, one-thread
setting, complete import artifacts, setup JSON and other options fixed. Use
a completed, stable input set rather than artifacts being rewritten by active
validation. Write the `-o`-only arm and the ordinary `-o/-i/-c` arm into separate
new experiment directories outside both checkouts' `.lake/build`; give every
output an explicit experiment path. Derived `.olean.server`, `.olean.private`,
IR and temporary C files must stay there too. Read the stable setup/imports
without invoking Lake build or altering traces/verification records. Record
per-process peak RSS, elapsed time and major faults with an available observer,
plus ambient contention and natural input-cache conditions. Preserve all normal
elaboration/kernel-checking options.

That comparison tests the combined output-stage difference. It neither disables
InfoTrees nor isolates `-i` from `-c`; fresh-mode behavior would additionally
change setup/import selection. It would be diagnostic evidence, never a
replacement for the guarded whole-project build, audit, reviews or candidate
record. Restarting the whole project in fresh mode would discard useful
incremental progress and does not have an established memory benefit here.

## Source fingerprints

| Inspected file | SHA-256 |
| --- | --- |
| `conaled/scripts/check.py` | `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29` |
| `Lean/Shell.lean` | `bbfcf01a93bcb9ca3f4d1264d3ad9890f3a6384dbbc949f5bf3cc286c0ec2225` |
| `Lean/Elab/Frontend.lean` | `423d17e49722e901e5f82bd4b86e7cf2dd80c352fc55b3d72ac1301a79ead634` |
| `Lean/Environment.lean` | `6c90105aecc4d28efe94cc9aef1704c284e7a748b28270b5f8513d2562331e43` |
| `lake/Lake/Build/Actions.lean` | `9c7d7101f89eb1d0618d8a76b86c30d628932ed2d2088db29792fdf88fb1e870` |
