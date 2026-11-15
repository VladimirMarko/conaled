# Existing-language computational clients (#491)

This kit compares real imported Haskell and Agda library declarations on Boolean
sum elimination and a small stateful wrapper. It is an inspection/execution
probe, not a conaled importer or an external proof checker. The
[assessment](../../docs/research/existing-language-frontend-comparison.md) gives
the observation contract, limitations and proposed implementation follow-up.

## Reproduce

Use the repository's pinned development shell, a GHC 9.10.3 distribution with
its bundled packages, and the official Agda 2.8.0.2 Linux binary retained by
[#115's kit](../agda-internal-retention/README.md). Its executable SHA256 is
`3fe070780fa370f5b74e5716ebe42fb60ec6b0ad90d13f8ab45d2903abf39b84`.
Supply the Agda data directory containing `2.8.0.2/lib/prim`; the official
binary's existing setup directory may be copied. The runner creates private
compiler configuration, copies the data/library/client files, and never writes
interfaces into your supplied source directory.

Get the [stdlib 2.3 archive](https://codeload.github.com/agda/agda-stdlib/tar.gz/refs/tags/v2.3),
SHA256 `407286af16f2b5b8aebe577b3610ae9b40ce296ed3c03c66444b5801c2fa3012`,
and extract it. No global Agda library registration or package installation is
needed. Use a new work directory, since the runner refuses to overwrite one.

```sh
direnv exec . python3 experiments/existing-language-frontends/inspect.py \
  --ghc /absolute/path/to/ghc \
  --agda /absolute/path/to/agda \
  --agda-data /absolute/path/to/data \
  --stdlib /absolute/path/to/agda-stdlib-2.3 \
  --work /absolute/path/to/new-probe-directory
```

In the orchestrated run, this command is serialized with the shared build lock
and `taskset -c 0`. That host scheduling convention is not a compiler semantic
requirement. The script bounds each compiler subprocess to 120 seconds and
saves `commands.json` and full logs after every completed command, including an
unexpected failure. A timeout or interrupted process is not a passing result.
No Lean build is involved and no production plugin/backend is built here.

## Evidence contract

The report's retained manifest records the executable/source pins, package
versions, selected interface and generated-file hashes, command outcomes and
source inventory identity. GHC 9.10.3 is the executed comparison pin; the earlier
GHC feasibility report's 9.12.2 source baseline is not misreported as executed.
`results.json` records the independent expected Boolean vector and actual
observations. `artifacts.txt` contains representative readable compiler evidence;
full private logs are reproducible by running the commands, not required to
understand the retained excerpts.

Haskell is inspected at `-O0` and `-O1` with desugared/simplified Core and Core
Lint, and the installed `Either.hi` is inspected separately. The source wrappers
use `Data.Either.either`. Importing its name, seeing its unfolding in an interface,
and seeing specialized code after optimization are distinct observations.

Agda checks the actual stdlib-importing source and its `observations-correct`
reflexivity proof. The existing #115 decoder summarizes selected fresh `.agdai`
declarations before backend compilation. It is deliberately bounded and
untrusted: it leaves some environment/type metadata raw and is not an independent
typechecker. The ordinary GHC backend then emits real library/client Haskell,
which GHC executes. This obtains no direct treeless dump and establishes no
Agda-to-conaled or dependent-proof transport theorem. The generated proof's
runtime erasure is evidence of that distinction, not an inability to export
its completed internal declaration.

The vector contains eight `choose` cases (two masks, four tagged Boolean inputs)
and two five-element stateful observations (four prior-state outputs and final
state). Expected values come from the stated Boolean equations; neither language
is used as the other's oracle. These finite checks are not a universal theorem
about arbitrary input sequences or programs.

Two Haskell controls distinguish an unused failing branch from a forced bottom
scrutinee. A private Agda `--safe` module with an executable postulate must be
rejected by Agda itself. Proposed importer failures for unknown globals, residual
functions, altered primitives or source association are specified in the report;
this kit cannot claim to execute a nonexistent importer's rejection path.

The final run succeeded with `UnsupportedIndexedMatch` warnings from transitive
stdlib modules about cubical transports. The manifest retains counts and log
hashes; the excerpts include a warning. This ordinary computational probe does
not assert those cubical properties or warning-free whole-library compatibility.
Earlier version-guard and private-configuration corrections are recorded in the
manifest; the final probe repeats all commands. Generated names and paths can
affect artifact hashes, so replay does not promise directory-independent bytes.

Third-party excerpts retain compiler-generated/source names, upstream
URL/version and applicable base/stdlib copyright and license notices in
`artifacts.txt`. The kit does not vendor full dependencies.
