# Frozen dependent higher-identity source test

This isolated Agda experiment supplies partial evidence for
[#316](https://github.com/VladimirMarko/conaled/issues/316). It checks the
frozen memo's generic dependent derivation, its two substitutions, and
concrete higher and nonconstant-transport instances. It does not construct a
Lean model or a sound Agda-to-Lean interpretation. The higher adoption gate
has not passed. [The investigation](../../docs/research/dependent-higher-identity.md)
identifies the precise construction owned by
[#322](https://github.com/VladimirMarko/conaled/issues/322); #321 owns the
alternative cubical-calculus/source-compatibility programme.

## Checked claims

- `FrozenMemo.agda`: arbitrary-motive inductive identity elimination with
  judgmental reflexive computation; the dependent pair `(v,η)`; `apd-η`
  with its transported source; both substitutions and their composition;
  and `β⁻¹ · ap_T(h) · β = h` for the path-family instance.
- `HigherWitness.agda`: the parameter `K(ℤ,2)`, a pointed equivalence from
  integers to its second inductive identities, the chosen `h = decode 1`,
  and an integer detector with `encode(refl)=0`. The same generic substituted
  pair and dependent witness are instantiated at `h`. Its observed conjugate
  has detector value 1, and erasure to reflexivity is refuted.
- `Monodromy.agda`: the circle's integer cover, with nested transport giving
  3 for the selected loops and 2 after erasing the first loop; the full pair
  and transported witness satisfy the same repeated-substitution comparisons.
- `Everything.agda`: the aggregate check, with no added mathematical claim.

The generic file uses inductive `Agda.Builtin.Equality`, exposed by
`Cubical.Data.Equality.Base`. The higher construction uses Cubical Path,
univalence, and the library's `PathIsoEq` to construct its parameter and
convert both loop layers to inductive identity. These are separate equality
notions. The pointed comparison supplies the reflexivity observation; an
unpointed carrier equivalence would be insufficient. `abstract` proof
boundaries prevent expansion of large equivalences while preserving their
checked types and proofs.

## Reproduce

From the repository root, on Linux x86-64 with Python 3.12 or newer:

```sh
direnv exec . python3 experiments/dependent-higher-identity/check.py \
  --work-dir /tmp/dependent-higher-check
```

Choose a new work directory. The script verifies the SHA-256 of the preserved
[Myers checkpoint 22](../../docs/history/orbifold/agda-checkpoints/README.md),
extracts its pinned Cubical v0.9 and native compiler kit into private storage,
verifies the kit, and installs the exact official Agda 2.8.0.2 release.
`--compiler-archive /absolute/path/Agda-v2.8.0.2-linux.tar.xz` permits offline
setup. `--compiler-state /absolute/path/state` reuses an existing kit state
only after its compiler and embedded data pass `doctor`; use a private state
because the checker writes interfaces and logs there.

The aggregate check uses `--ignore-interfaces`, `--safe`,
`--no-allow-unsolved-metas`, and `--no-allow-incomplete-matches`. It selects
only the explicit Cubical registry, preserving library-scoped flags and
avoiding ambient default libraries. The run writes `check.log`, `imports.dot`,
and `validation.json` in the work directory. The receipt hashes every source
reported by the fresh checker, all compiler-owned builtin sources in the
import graph, the authored sources and script, the compiler,
and the log/graph. Compiler-owned imports omitted from the checker’s progress
lines are identified separately and checked against the kit’s source pins.
Failed checks retain their diagnostic log and failed receipt.
The checked-in `validation.json`, `check.log`, and `imports.dot` record the
successful run for this source candidate. Paths in the raw command identify
that run's temporary checkout; source hashes provide the portable identity.

The retained run completed at `2026-11-04T23:37:08Z`
(`2026-11-05 00:37:08` in Europe/Zurich). The checker reported 229 fresh
modules: four local, 209 Cubical, and 16 compiler-owned. Six further
compiler-owned imports were verified against the kit's source hashes, giving
235 source modules in the dependency graph. The aggregate checker invocation
took 60.26 seconds after a fresh offline compiler setup. This is a reproduction
receipt, not a performance benchmark.

## Source and trust boundary

The preserved archive's SHA-256 is
`19e6f70f5c86856ccd98b6ffb96817f6ee4a58938aa76e5aef1d91b670ba6a53`.
It contains Cubical commit `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.
The compiler archive and binary hashes are recorded in `validation.json`.
No vendored mathematical sources are modified. Cubical is MIT licensed;
Agda's release and kit provenance remain in the preserved checkpoint.

The relevant pinned library declarations are
[`Kn≃ΩKn+1∙`](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/ZCohomology/Properties.agda),
[`coHomK`](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/ZCohomology/Base.agda),
[`PathIsoEq`](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/Data/Equality/Conversion.agda),
[inductive equality](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/Data/Equality/Base.agda),
and the [integer cover](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/Data/Equality/S1.agda).
The source closure uses Agda's cubical primitives, interval, dependent Path,
transport/composition and Glue, as well as library HITs and truncations. Safe
checking rejects user admissions; it still trusts the Agda implementation and
its primitive rules. It is not the repository's Lean kernel axiom audit.
The Cubical manifest also uses `--no-import-sorts` and suppresses
`UnsupportedIndexedMatch` warnings. This does not admit unsolved proofs;
compatibility must still cover the particular indexed-inductive transport and
conversion rules used by `PathIsoEq`. Agda documents that feature as
[experimental](https://agda.readthedocs.io/en/v2.8.0.2/language/cubical.html#indexed-inductive-types).
The import graph records whole checked modules, including declarations unused
by these consumers; it is not a minimal logical proof-dependency graph.
No crisp/cohesive rules or smooth/geometric parameters are used here. Checking
this closure does not recheck the full Myers or Kock developments.

The first transparent higher-witness attempt was interrupted after its large
pointed proof expanded during checking (the earlier checker receipt
reported 483.753 seconds and exit -15, transcribed in `attempts.json`). Making `double-identities` abstract
allowed the same proof and consumer statements to check. The initial direct
normalization of three transported loops was also interrupted; named
single-loop and composition proofs replace that repeated normalization.
These observations concern this checker run, not a measured author-effort or
cross-language performance comparison.
