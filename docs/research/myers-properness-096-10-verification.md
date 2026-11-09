# Fresh verification of the properness obstruction

The unmodified target Orbifolds.ProperCompactDecisions and its import closure passed a fresh Agda 2.8.0.2 check on 2026-11-09. Exit code 0; elapsed 61.565 seconds. The check used --safe, --ignore-interfaces, the project library's cubical/guardedness/no-import-sorts/cohesion flags, and an explicit dependency registry without ambient defaults. This is new checking, not reliance on the checkpoint's prior receipts.

The compiler archive was independently compared to the official GitHub release API asset digest: 2bcf24bb561b1be859bba841e5d67962d1616b3251bc147f878e4f60a2fbd9f7. The extracted binary SHA256 was 3fe070780fa370f5b74e5716ebe42fb60ec6b0ad90d13f8ab45d2903abf39b84 and its numeric version was 2.8.0.2. This checks identity against the official distribution, not compiler correctness from a bootstrap build.

The recorded syntactic closure has 290 modules, including 28 project modules. Every copied project/Cubical module in that closure matched the original extracted archive bytes, and all recorded hashes were unchanged after checking. This is a targeted properness replay, not a rebuild of all 826 project modules or pending experiments.

The [curated source archive](../history/orbifold/agda-checkpoints/checkpoint-096-10-source/README.md)
contains the unchanged sources. Durable fresh evidence is stored alongside it:
[command](../history/orbifold/agda-checkpoints/checkpoint-096-10-source/verification/command.json),
[result](../history/orbifold/agda-checkpoints/checkpoint-096-10-source/verification/result.json),
[complete log](../history/orbifold/agda-checkpoints/checkpoint-096-10-source/verification/fresh-check.log),
[source closure and hashes](../history/orbifold/agda-checkpoints/checkpoint-096-10-source/verification/syntactic-closure.json),
[unsafe-feature scan](../history/orbifold/agda-checkpoints/checkpoint-096-10-source/verification/unsafe-scan.json),
[official asset identity](../history/orbifold/agda-checkpoints/checkpoint-096-10-source/verification/official-asset.json),
and [setup failures and resolution](../history/orbifold/agda-checkpoints/checkpoint-096-10-source/verification/setup-notes.md).
Temporary paths in receipts identify that run; replay does not require those
paths to survive. No compiler binary, source working copy or interface cache
is included in this evidence directory.

## Targeted statement review

The claims reviewed are Orbifolds.ProperCompactDecisions.compact-inhabitation-decidable, Diagonal.proper-diagonal≃discrete, and SmoothReals.smooth-real-diagonal-not-DP-proper, including the definitions and key intermediate proofs in Compactness, ProperMaps, SyntheticField and SyntheticDifferential.

* DPCompactAt p K quantifies over all hProp p A and families B : K → hProp p. It turns a pointwise mere disjunction A ∨ B(k) into A ∨ Πk.B(k). DPCompact uses p equal to the carrier universe. No resizing or restriction to externally supplied/crisp predicates is present.
* DPProper f quantifies over every subtype U : Y → hProp ℓ, taking DP-compactness of its subtype to DP-compactness of its inverse image. X and Y share universe ℓ. The forward passage from properness to compact fibers requires isSet Y; this is used rather than hidden in a generic higher-type claim.
* Compactness of a proposition P gives Dec P by testing A=P and B constantly false. Truncated disjunction can be eliminated to Dec P because P is a proposition and therefore Dec P is a proposition. The arbitrary K result passes compactness to ∥K∥ through the truncation map, whose fibers are merely inhabited. It does not choose an inhabitant of K.
* For set X, the fiber of x↦(x,x) over (x,y) is a proposition equivalent to x≡y. Compact fibers and decidability of those propositions therefore give both directions of DPProper diagonal ≃ Discrete X. The result is genuinely restricted to sets, and uses cubical path equality.
* SmoothReals is a module name, not a construction of real numbers. Its inputs are an arbitrary CommRing ℓ, KockField R, and FirstOrderKL R. KockField includes 0≠1 and finite-K: a finite tuple which is not all zero merely contains an invertible entry. FirstOrderKL is isEquiv of the affine map R×R → (D→R), (a,b)↦(ε↦a+bε), for D={ε | ε²=0}.
* KockField makes every square-zero ε double-negation equal to zero: assuming ε≠0 produces its inverse and hence ε=0. Decidable equality would remove that double negation for every ε. KL injectivity of affine coefficients then equates slopes 0 and 1, contradicting 0≠1. Consequently DPProper diagonal is impossible under exactly those supplied inputs.
* The critical quantifiers are ordinary/unrestricted, not @♭/crisp. The compiler cohesion flag does not itself supply a cohesive model. A decision about global points, or an external topological compactness/properness claim, cannot simply be substituted for these internal predicates.
* No model inhabiting the combined Kock/KL hypotheses is constructed by this result; no unconditional inconsistency of Myers theory follows. No ordinary-topological comparison functor or theorem is proved in this target module.

The syntactic import scan records all imported source hashes and detects no project or Cubical postulates or bypass pragmas. Agda builtin primitive postulates occur and are part of the compiler foundation, not new mathematical assumptions supplied by this project. Imported conditional records are permitted and are not postulates.

## Paper comparison and consequences

Myers's [version 1, Definition 6.2.1, Warning 6.2.3 and Proposition 6.2.4](https://arxiv.org/html/2205.15887v1#S6.SS2)
state the compactness/properness predicates, the decidability criterion for
propositions and the compact-fiber criterion. Warning 6.2.20 explicitly uses an
equality-dependent subtype to distinguish the internal compactness condition
from an ordinary closed-and-bounded test. This source comparison supports the
quantifier distinction; it does not prove a correspondence for every intended
model or audit the entire paper.

The verified result therefore warrants a concrete boundary: the external
finite-action theorem in [#435](https://github.com/VladimirMarko/conaled/issues/435)
exports Mathlib `IsProperMap`, with no automatic interpretation as this
unrestricted internal `DPProper`. The trivial-group diagonal remains a required
test of any proposed bridge. A restricted comparison or changed internal
interface needs its own statement, hypotheses and proof. #100/#36 own that
broader correspondence; #428 and #433 must keep their source/model assumptions
explicit. No new standalone obstruction programme is started here.

## Reproduction

Extract the curated archive into a fresh directory. Download the compiler from
`COMPILER-PIN.json`'s official URL and verify its archive and executable hashes.
Use that binary's `--setup` with fresh `Agda_datadir`, `AGDA_DIR` and `TMPDIR`
directories as described in the retained setup notes. Those directories must
not contain interfaces from earlier attempts. Set `AGDA_BIN` to the verified
binary, `SOURCE_ROOT` to the extracted `myers-096-10-source` directory, and
`REPLAY_ROOT` to a fresh writable directory. Then, inside the repository's
direnv shell, run:

```sh
printf '%s\n' "$SOURCE_ROOT/project/dependencies/cubical-0.9/cubical.agda-lib" > "$REPLAY_ROOT/libraries"
cd "$SOURCE_ROOT/project/formalization"
"$AGDA_BIN" --no-default-libraries --library-file "$REPLAY_ROOT/libraries" \
  --safe --cohesion --ignore-interfaces \
  -i src -i "$SOURCE_ROOT/project/dependencies/cubical-0.9" \
  src/Orbifolds/ProperCompactDecisions.agda
```

Keep `--no-import-sorts` in the supplied library descriptors, not as a global
command-line flag: applying it to compiler builtins caused the first failed
setup attempt. The successful receipt used a relocated descriptor with the
same project flags. The source and dependency hashes provide the connection
between that working copy and this curated archive.
