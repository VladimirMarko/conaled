# R2 receiving runtime evidence supplement

This is an external validation method for the unchanged candidate
`99a2974c93e556088af814f033540eb36ba2d3a6`, tree
`173003db476a73783a873897bb754ca941d2f9c8`. It addresses the remaining
runtime-artifact and observation part of SPEC074-1 in the existing
`/root/control_review073` review loop. It does not edit candidate source,
rerun the whole-library check, create a Lean verification receipt, or qualify
new textbook mathematics. The separately completed R2 whole-library CI remains
its actual earlier execution, with its own receipt and source binding.

## Commands and outputs

The workflow checks the immutable orchestration revision and R2 out into
separate directories. After its existing pinned Nix setup, it invokes:

```sh
python3 -B textbooks-runtime074.py run --repo /absolute/candidate --out /absolute/empty-evidence --candidate 99a2974c93e556088af814f033540eb36ba2d3a6
python3 -B textbooks-runtime074.py verify --repo /absolute/candidate --out /absolute/evidence --candidate 99a2974c93e556088af814f033540eb36ba2d3a6
```

`run` builds only `extract-searchtree` with
`lake --no-cache --rehash build extract-searchtree`. The complete build argv,
start/completion times, actual exit, stdout and stderr are retained. Build time
is separately labelled. Before/after build checks require exact clean R2 source,
all nine clean manifest-pinned dependency source checkouts, the compiler pin,
Python executable identity, and unchanged validation-driver bytes.

The method retains 23 selected generated C files, their current hashes and the
available historical CTB-91 hash comparisons. It records the actual native ELF
header, identity, `file`, `readelf`, `nm`, dynamic linkage, and selected native
comparator/thunk disassembly. It does not copy the ELF or dependency caches into
the evidence packet. Selected function bodies and call edges still require
independent affected-code assessment; a symbol name or an equal/different hash
does not itself establish correspondence or compiler correctness.

After the target build it inventories and hashes every project build artifact,
every existing dependency build tree, the compiler distribution's bin/lib trees,
and the executable's resolved dynamic libraries. All tracked project and
dependency source bytes are also recorded. These inputs must remain identical
after both runtime modes. No build/runtime CPU, worker, memory, affinity, or
execution-time cap is introduced.

The full unmodified public harness runs in direct Lean and standalone modes,
using explicit launch arrays and distinct `EXTRACT_TEST_LOG_DIR` directories.
Each outer run must exit zero and report all 55 tests without skips. The
unchanged harness retains each invocation's argv, start, duration, exit,
stdout/stderr, and all input bytes, including invalid receipt fixtures. Every
source test must have recorded invocations, with consecutive numbering and an
identical complete invocation set in both modes.

## Complete cross-mode comparison

The comparator pairs records by full test identity and invocation number, then
requires equal kind and exit. It verifies every retained byte hash and exact
file inventory, requires the recorded inputs to cover precisely the argv's
input-file options, and checks the exact launch prefixes. Observer interpreter
and script identities must match. Actual replay files must be byte-identical.

Complete stdout semantic values and complete stderr are compared. Typed JSON
nodes preserve duplicate member order, number spellings, Booleans, arrays and
all fields. Only nonnegative integer `elapsedNs` values are normalized. Negative,
Boolean, floating and nonfinite timing mutations remain distinct. Malformed
JSON/UTF-8 remains raw bytes, so failed-input cases are not silently discarded
or repaired. JSON whitespace/escaping is treated semantically; numeric lexemes
and object member order are conservatively retained.

Temporary path rewrites use only explicit paired input paths, preserve the
relative basename, and require full input comparison. Differing missing-file
paths additionally require a test-local parent-directory binding established
by an actually retained, exactly equal input byte sequence in that same test.
This can be an earlier invocation at the same path or a sibling fixture.
The report retains the supporting bytes/hash, test and invocation identities.
An absent path with no such evidence fails. The unchanged literal relative
`unused-replay-path` needs no rewrite. No basename-only or arbitrary temporary
directory normalization is available.

## Nonrepairing verification

`verify` first rejects any actual capture failure record. It rehashes the exact
evidence manifest, original runtime-input snapshot, current source/dependency/
compiler/native artifact inventory, and full retained semantic comparison.
It uses only Git/version/prefix identity probes and ordinary reads: no build,
harness execution, workload, proof audit or artifact repair. Its new readback
is separate from the original runtime result. Both records remain subject to
actual outer command completion and independent review.

Before/after equality cannot detect transient changes that are restored between
observations or undeclared external inputs. The isolated checkout, stable
dependencies and ordinary trusted compiler/OS/runtime remain execution
assumptions. The method makes no portable speed or asymptotic complexity claim.

## Preparation evidence and current status

`static-preflight.json` uses the already completed exact-R2 native source-policy
output and its matching 3,922-path manifest to check selected import reachability.
All 22 selected project modules are reached from the nine actual driver imports;
the external Mathlib list-sort module is also reached. The existing local
focused checkout already has the 21 selected imported project C files and the
Mathlib C file. The executable target must generate its own root C file on the
remote host. This is a static readiness observation, not a new target-build claim.

All 55 test methods have a static call path to `run_recorded`; actual execution
coverage is still checked by the runtime capture. A read-only preliminary
alignment assertion used the 3,921 public-module list against the 3,922-entry
policy output and failed before any runtime/test invocation. The corrected
check uses the complete source manifest, including the audit module.

The first comparator fixture run passed 13 tests. The final captured run passes
14 public-CLI tests, adding the actual-failure readback guard. Its command,
actual exit zero, elapsed time, full streams and exact source hashes are in
`fixture-tests-result.json`. Cases cover semantic corruption with an updated
digest, altered replay bytes, corrupt hashes, unaccounted files, missing input
identities, missing-parent and changed-basename rejection, cross-test parent
binding rejection, duplicate members, invalid timing values, malformed inputs,
and refusal to verify a failed capture. No Lean build or textbook runtime was
run during preparation. Required receiving acceptance remains pending until
the actual remote supplement and affected-code review complete.
