# Unary-comparison prototype validation

## Current resource-interface follow-up — passed

Date: 2026-11-02. The existing resource targets and the updated staging file
both passed their focused checks. This remains cross-cutting preparation,
not integrated acceptance or chapter completion. No Sort algorithm was added.

### Final checked artifacts

| Artifact | SHA-256 |
| --- | --- |
| `UnaryComparisonCosts.lean` | `997aa73ce69fe65712ba97a1217909a6f7af8c2d00e7e2978a4ca03a18c01c13` |
| `UnaryComparisonCosts.olean` | `2e8c6b2152981eb25b7cb4343899c8ea8e993ed1c520cd6743abb6f84f4c5743` |
| `README.md` | `e676d55a1faa402bb70874e22fad817670eadce19512489b5d9e2d8610aeb853` |
| `resources-build.txt` | `b9fc8b0ea81d69614dc659c211dd382043c3f85b1be09fe5a0b336dec76ba375` |
| `resources-adapter-validation.txt` | `24fa8f8c6b65e664747f88d6da77413252d9b9d709699c9b203e9acfeaff3355` |
| `resources-adapter-module-error.txt` | `c2b1e8d27b94b2c1b04ecd103e0a6c12d1eb9d54a71a1caee561d25dfa3f8dbe` |

Main checkout: `/workspace/scratch/0c54f2db1fdf/conaled`, commit
`cba657b43ed57e15962858713b819058e7d3c3ca`. Lean remains 4.35.0 at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. `git status --short` was empty
before the build and after the final staging compile. All nine dependency
checkouts were checked after the build: their Git revisions match
`lake-manifest.json`, and their source working trees are clean. The independent
`vfa-validation` checkout was not modified or used by these commands.

The toolchain, manifest, flake and existing resource sources matched their
pre-build SHA-256 values afterward:

| Existing input | SHA-256 |
| --- | --- |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lake-manifest.json` | `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b` |
| `flake.nix` | `0dc6835949ecc2a9e28e9fff16aeb4fa46eca74d1a92132d9a3a236974409f37` |
| `flake.lock` | `8489579a33350261a210f64e54d9442fece9c04fedf7ce8e6c5543010471238f` |
| `Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `Applications/Resources/Workload.lean` | `5db2ef8f7a504b33b4dfbb26ed39de1a194fa59568ba16702f3ba2359b46b4f5` |
| `Applications/Resources/Potential.lean` | `680ea6df1c0271094a93b089a6fa2e7e8826a4da12937889ed5ecff8fc59cabe` |

### Exact commands and results

Both commands ran in the main checkout with approved escalated execution to
access the installed Nix environment. Each invocation set:

```bash
export PATH=/root/.nix-profile/bin:$PATH
export NIX_CONFIG='build-users-group =
experimental-features = nix-command flakes'
export LEAN_NUM_THREADS=1
```

The single authorized focused build was:

```bash
nix develop --command lake build Applications.Resources.Measured Applications.Resources.Workload Applications.Resources.Potential > /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/resources-build.txt 2>&1
vfa_resources_build_status=$?
cat /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/resources-build.txt
exit "$vfa_resources_build_status"
```

Exit **0**; Lake reported completion of 590 scheduled/cached jobs. Newly built
outputs included the three requested modules and their needed dependencies.
Existing legacy modules emitted module-format suggestions; no source was
modified to silence them. No cache download or broad build was requested.
The three resulting resource `.olean` hashes were:

| Module | SHA-256 |
| --- | --- |
| `Applications.Resources.Measured` | `e41e8c06de9b31a2553dfcc48097ea4d5bbcc0eba5162d67cc83024ed2b335a2` |
| `Applications.Resources.Workload` | `02cf7c619f5df5a9bd7a34b6a6e1d652d5ee0685f4dffd6b5cc2191a8b674529` |
| `Applications.Resources.Potential` | `ebaf838b961a9f44618e4cee6855dfaae9c89c285280c1209a33fe13d3ae65c7` |

After the queue adapter's separate focused check released the compiler slot,
the unary adapter was checked with:

```bash
nix develop --command lake env lean -j 1 \
  -R /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs \
  -o /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/UnaryComparisonCosts.olean \
  /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/UnaryComparisonCosts.lean \
  > /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/resources-adapter-validation.txt 2>&1
vfa_unary_adapter_status=$?
cat /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/resources-adapter-validation.txt
exit "$vfa_unary_adapter_status"
```

Final exit **0**, with no warnings or errors. The original recursive bodies,
proofs and examples are retained. The added square adapter, its arithmetic
consumer, the bind/pure two-direction client, both general client theorems,
and the two new connected examples all compiled.

The first invocation of that command exited **1** on source SHA-256
`07e06097448269b03aab88f39a27f5068684c3f277d00476995df629f3e7bd31`:
Lean rejects importing the legacy `Applications.Resources.Measured` file
from a file marked `module`. Its diagnostic is preserved in
`resources-adapter-module-error.txt`. The correction changes only the staging
file to ordinary imports, removing its `module`/`public section` syntax; all
declarations remain public. This is an ordinary source compatibility issue,
not evidence of a Lake integrity incident. The final check reran the same
command after that correction; no further build was run.

### Axioms, statement review and scope

The eight printed axiom reports contain only permitted axioms:
`compareBothWays_value` reports `[propext, Quot.sound]`; the other seven
reported results contain only `[propext]`. They include all four original
principal claims and the new square value, composed value/specification and
composed example. No admission, application-specific axiom, unsafe shortcut,
or `native_decide` was added. These focused reports do not replace the full
integrated proof audit.

`README.md` records statement review and the independent client expectations:
the square at `(8,3)` returns false; comparing `(3,8)` and `(8,3)` returns
`(true,false)` and costs `4+4=8`. The former consumes `Square.commutes`; the
latter consumes the general specification derived using existing `bind` and
`pure`. No parallel cost framework was introduced.

The source and evidence are ready to freeze for the existing independent
staging review. All further compiler/build work is held while the parent
continues isolated candidate validation. Integrated import coverage, the
guarded build, exhaustive proof audit and chapter Standards/Spec gates remain
separate requirements; this file claims none of those completed.

## Historical initial standalone check

The remaining record describes the earlier source snapshot before the checked
resource adapter. Its source, README and `.olean` hashes are historical; the
current files have been superseded by the hashes above. The original
`validation.txt` log is retained. Date: 2026-11-02; initial standalone check
passed, without integrated acceptance or chapter completion.

### Checked input identity

- File: `UnaryComparisonCosts.lean`.
- Source SHA-256:
  `71f6b20983629b7020be14e836755ad1d201f96b1fb6051669dfba7da6025429`.
- Main checkout used only to resolve the pinned environment/import paths:
  `cba657b43ed57e15962858713b819058e7d3c3ca`.
- Compiler: Lean 4.35.0, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Imported dependency: cached `Mathlib.Data.Nat.Basic` from the checked-in
  dependency manifest, mathlib revision
  `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- `lean-toolchain` SHA-256:
  `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- `lake-manifest.json` SHA-256:
  `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b`.

### Exact successful command

Working directory: `/workspace/scratch/0c54f2db1fdf/conaled`.
The command used approved escalated execution to access the existing Nix
installation. The newline in `NIX_CONFIG` is intentional.

```bash
export PATH=/root/.nix-profile/bin:$PATH
export NIX_CONFIG='build-users-group =
experimental-features = nix-command flakes'
export LEAN_NUM_THREADS=1
nix develop --command lake env lean -j 1 \
  -R /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs \
  -o /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/UnaryComparisonCosts.olean \
  /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/UnaryComparisonCosts.lean \
  > /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/validation.txt 2>&1
vfa_unary_compile_status=$?
cat /workspace/scratch/0c54f2db1fdf/work-state/staging/unary-costs/validation.txt
exit "$vfa_unary_compile_status"
```

Exit status: **0**. Both the environment and compiler are restricted to one
Lean thread. No `lake build`, cache download, project-source edit, or integrated
check was performed for this prototype. Main checkout `git status --short`
was empty after the successful command.

### Result and limits

The compiler checked every definition, theorem, and named example in the file.
`#print axioms` reported only `[propext]` for `unaryLERun_spec`,
`unaryLERun_true_iff`, `no_difference_only_bound`, and
`equal_inputs_beyond_threshold`. There are no source admissions,
application-specific axioms, or `native_decide` uses.

- Successful output log SHA-256:
  `e607ab9418ee83bad23a0c32e6fc2c34a3d14ef87de2516c641a3f7a945fdc24`.
- Generated `.olean` SHA-256:
  `8c8f28a1d2ac7a365e21f757ba04ab3392c172aafe229c7b7e8699711214170b`.
- Accompanying `README.md` SHA-256:
  `47f8ed88a91b02036c06758af4a105ee8560e8eccdbdc9b0759dc90b2eb5ca97`.

An initial invocation needed the explicit `-R` staging root because its input
was outside the repository. In the first source check, simplification reduced
the no-bound contradiction to `bound 0 + 1 ≤ bound 0` but did not close it;
the final proof invokes `Nat.not_succ_le_self` explicitly. The final successful
log above is the validation evidence. Neither preliminary failure was accepted
as a proved claim.

The statement review and independently calculated examples are in `README.md`.
The output is an exact structural-call model for the displayed unary `≤`
recursion. It is not a verified Coq `Nat.ltb` implementation, native Lean-Nat
cost model, elapsed-time observation, or compiler-correctness result. The
proposed `Resources.Measured`/`erasureSquare` adapter was not compiled in this
initial check; the current follow-up above supplies that missing connection.
Integration still requires public import coverage, the full guarded build and
proof audit, and the repository's independent review gates.
