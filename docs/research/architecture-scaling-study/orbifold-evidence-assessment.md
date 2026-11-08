# Orbifold checkpoint 080: evidence and theorem scope

Assessment for [#362](https://github.com/VladimirMarko/conaled/issues/362),
2026-11-08, against conaled base
`700786fa2f691d6db196f388d69c2f12bc5d1afb`.

Checkpoint 080 supplies substantial parameterized Agda mathematics and two
separate accepted source closures. It does not supply a native interpretation
of the full Myers foundation. The original synthetic completion theorem, the
revised ordinary atlas theorem, and the presheaf obstruction have different
hypotheses and conclusions. Treating any one as evidence for the other would
change the claim.

The [preserved checkpoint](../../history/orbifold/agda-checkpoints/checkpoint-080/)
contains the unchanged archive and incoming reports. Archive paths in this
assessment are relative to `myers-agda-checkpoint/`; they are not integrated
repository modules. The earlier [checkpoint inventory](../../history/orbifold/agda-checkpoints/README.md)
covers checkpoint 022 and Kock separately. Neither the Lean build nor its
axiom audit certifies these archived sources.

## Independent byte and closure audit

The archive SHA-256 is
`4a2e2178578a9cfcae3877bbe4157cb69ea622fc7b07ff10a273b2276eecf264`.
Independent Python checks against the extracted checkpoint found:

| Check | Result |
| --- | --- |
| `MANIFEST.json` payloads | All 2,294 files exist and match their SHA-256; no extra files except the manifest itself. |
| Cubical receipt source hashes | All 539 match current archive bytes. |
| Ordinary receipt source hashes | All 54 match current archive bytes. |
| Recursive project imports | Exact equality with each receipt's source set; the two sets are disjoint. |
| Literal native `Checking` entries | All 54 ordinary modules; only the aggregate entrypoint in the retained Cubical log. |
| Project source OPTIONS | Cubical closure uses safe Cubical/guardedness, sometimes cohesion and two-level mode; every ordinary module uses `--safe --without-K --no-import-sorts`. |
| Textual `postulate` declarations | None in either admitted project closure. This scan does not replace compiler checking or an assumption audit. |

The closure traversal resolves source imports recursively from `src/Everything.agda`
and `src/Orbifolds/Intensional/Everything.agda`. It is an independent lexical
cross-check, not an Agda elaborator. It found 145 distinct external import
names from the Cubical project closure and two from the ordinary closure.
Those counts are direct external references, not full dependency counts.
The manifest covers bundled Cubical bytes; agreement with it is not an
independent Git authentication of the claimed upstream revision.

The supplied identities, independently recomputed, are:

| Artifact | SHA-256 |
| --- | --- |
| `formalization/validation/latest-check.json` | `d60652c2ed5ecad385ac1146ab7caa7eb93774e34708d99724be636aee4ae785` |
| `formalization/validation/latest-check.log` | `ff3eead8c013b5ee1ada9f0efe7bd9a9b59745529925e22a6635bd73899f462f` |
| Cubical source-map digest | `47d63b8136c9144a43e38141f31d7344297087592245cbfb2559b3caab407a60` |
| `formalization/validation/intensional-development-check.json` | `de458bbe8ebe1570371e9d23c99322f7a99a42031b27c7e144a6fe148f04b8f6` |
| `formalization/validation/intensional-development-check.log` | `53e681b54d9e16bac4e3601c20b5611499145ef39ac2b7fb3d6c4e134a9f1ad8` |
| Ordinary source-map digest | `46b4c23ab8f9d3898d613a387d26a21d2ff7834e4d1859835210b98f9ea0dcf5` |

The source-map digests use SHA-256 of Python
`json.dumps(checked_source_sha256, sort_keys=True).encode()`, including its
default spaces. A different JSON serialization produces a different digest.
`formalization/CHECKPOINT.json` agrees with these maps and the total of 593.

Both supplied receipts record exit code zero and stable sources. The Cubical
receipt records Agda 2.8.0.2, Cubical commit
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`, and 51.329 seconds. It is the
retained checkpoint-074 acceptance, not a new checkpoint-080 cold check.
`formalization/CHECKPOINT-080.md` explicitly records an interrupted optional
Cubical replay. Its one-entry log is consistent with an incremental aggregate;
it does not demonstrate fresh elaboration of all 539 modules.

The ordinary receipt records 71.076 seconds, `--ignore-interfaces`, no
libraries, safe mode, rejection of unsolved metas and incomplete matches,
and `--without-K`. All 54 project modules occur in its complete log. These
are supplied execution records whose bytes and source correspondence were
verified here; metadata agreement alone cannot reproduce execution or prove
that the recorded compiler actually produced the log.

## Independent ordinary replay

The coordinating agent ran the inspected setup and fresh ordinary runner in
an isolated copy on 2026-11-08. This audit then independently inspected its
[receipt](../../history/orbifold/agda-checkpoints/checkpoint-080/validation/intensional-development-check.json)
and [complete log](../../history/orbifold/agda-checkpoints/checkpoint-080/validation/intensional-development-check.log).
The run exited zero in 37.587 seconds, reported stable sources and
1,221,324 KiB child peak RSS, and used the pinned binary hash listed below.
All 54 expected project modules have literal `Checking` entries, and the
entire recorded source map equals the supplied ordinary receipt's map.
The isolated compiler setup also passed its six positive/negative smoke
checks. This reproduces ordinary native acceptance independently of the
supplied log; it does not reproduce the Cubical gate or mechanize the
external semantic reports.

The new receipt SHA-256 is
`d9a3a1e22f0eef6773af77b04733a60b43fca4066add316618cf984b12fec3b9`;
the log SHA-256 is
`e47236ab074b6c10e6c6fe327b94d1a6af33d5aeffc4c1a21a57cdb430ed165c`.
These new artifacts remain separate from the unchanged supplied archive.

## Original synthetic completion theorem

The inspected declaration is
`Orbifolds.FullProperEtaleOrbifolds.Context.Presentation.Ordinary.proper-etale-completion-orbifold`
in `formalization/src/Orbifolds/FullProperEtaleOrbifolds.agda`.
It concludes full infinitesimal-variety orbifold structure on the actual
`GroupoidCompletion.Completion.Object C invertible`. It calls the geometric
core theorem and then the spectrum-to-full bridge. Completed microlinearity
and properly finite completed identities are derived, rather than fields
of the input record.

Its enclosing contexts and signature require:

- A crisp commutative ring and Kock-field structure; crisp identity induction
  at the working and zero universes; zero-level Flat induction and computation.
- A crisp category with all arrows invertible; ordinary fixed-dimensional
  manifold structures on its objects and total arrows.
- Strict order, ordered-ring compatibility, constancy, interval-ball covering,
  unit-interval compactness, and the positive-line equivalence.
- RealFlat, crisp excluded middle, tinyness of the actual generator `𝔇`,
  Flat/truncation distribution at the working and successor universes, and
  crystalline preservation of crisp pullbacks.
- Literal `DPProper sourceTarget` and crystalline `Etale source`.

The complete statement and `formalization/PROPER-ETALE-ORBIFOLD-SCOPE.md`
support a completed conditional proof of the intended synthetic main theorem.
They do not construct these ambient hypotheses or identify internal DPProper
with classical topological properness. The broader historical ledger retains
39 checked, 58 relative and three corrected/refuted result rows. Its 100
anchors and 199 environment dispositions are editorial correspondence
coverage, not 100 unconditional theorems or a proof of full semantic soundness.
See `formalization/EDITORIAL-AUDIT.md`, `paper-correspondence.json`, `ERRATA.md`
and `COMPLETION-079.md`; this assessment did not independently reread all 100
proofs.

`formalization/src/Orbifolds/ExternalPropernessObstruction.agda` gives a
separate obstruction to preserving literal properness. Its
`represented-diagonal-proper≃discrete` takes a set and an actual representation
of its diagonal, including domain/codomain equivalences and the commuting
square. It relates DPProper of that arrow to decidable equality of the set.
Together with the synthetic real hypotheses, the ensuing argument obstructs
the specified classical-to-synthetic comparison package. It does not rule
out alternative properness notions or all models.

## Revised ordinary atlas theorem

The active theorem is
`Orbifolds.Intensional.DerivedAtlasOrbifold.Theory.Family.finite-branch-pushout-atlas-orbifold`.
Its exact project import closure has seven files under
`formalization/src/Orbifolds/Intensional/`:
`Identity`, `BoundedTruncation`, `Equivalence`, `FiniteBranchAtlas`,
`LiftingCancellation`, `PushoutLifting`, and `DerivedAtlasOrbifold`.
The other ordinary aggregate modules do not become hypotheses of this theorem
merely because they share an aggregate entrypoint.

The inspected input is an effective atlas `A → X`, object sethood, locally
merely given finite partial-map charts, a small indexed family of actual
pointed pushout tests, equivalence of the specified four-vertex mapping
comparison for `A`, and four vertex lifting properties of the atlas map.
`EffectiveAtlas` supplies surjectivity and equivalences between its actual
hom family and paths between atlas images. It does not assume the final
microlinearity or finiteness conclusion. The proof derives source locality
from the actual mapping square, derives the two atlas lifting fields, and
uses the earlier atlas theorem to descend locality and subfinite identities.

The conclusion `ReducedOrbifold X` has two fields: locality for the selected
gap maps and subfinite identity types. Subfiniteness is mere presentation by
a proposition-valued subset of a finite type. It does not give decidable
membership or an enumerated finite cardinality. `PointedPushoutTest` imposes
no Weil-algebra condition. In particular, choosing an empty test family makes
the locality component vacuous. A geometrically meaningful instance must
supply and interpret the intended tests; the general theorem alone does not
guarantee that they are the full Myers tests.

Logical inputs are explicit `FunExt ℓ ℓ` and `BoundedTruncation ℓ`.
The latter maps types in `Set (lsuc ℓ)` to propositions in
`Set (lsuc (lsuc ℓ))`, with point, squash and propositional elimination.
Its computation law follows from target propositionhood. There is no hidden
resizing claim, constructed truncation inhabitant, RealFlat premise, crisp
excluded middle or whole-neighborhood tinyness in this seven-file theorem.

`formalization/research/semantics/LANGUAGE-BRIDGE-074.md`,
`DERIVED-ATLAS-INTERPRETATION-076.md`,
`FINITE-BISECTION-INTERPRETATION.md` and `MORITA-COMPARISON-074.md` state the
external higher-Cahiers interpretation and classical orbifold recognition.
Those reports distinguish external mathematics from native model construction.
The recognition criterion uses an effective manifold atlas with representable
proper étale relation; it does not identify every reduced orbifold with a
classical finite-dimensional orbifold. The archive also reports countable
products of smooth lines among the broader reduced objects. The smooth-to-formal
extension is not claimed to preserve arbitrary dependent type structure.

## Constructed presheaves and the RealFlat obstruction

The final inspected native statement is
`Orbifolds.Intensional.PresheafObstructionInstance.ForEmbedding.ForCounterexample.real-flat-contradiction`.
The enclosing parameters matter: two small ordinary categories `C,D`, a
functor `i`, full-faithfulness inverse data, `FunExt ℓ ℓ`, an object `R` of
`C`, and an actual presheaf `F` with all three properties:

1. Nullity for projection-precomposition along `y_C(R)`.
2. Contractible global sections.
3. Nonterminality.

The witness is an input. The theorem does not prove that such an `F` exists
for arbitrary `C` and `R`. Given it, the modules construct right extension
`UF`, the restriction adjunction, full faithfulness, representable-line and
product comparisons, fixed exponentials, and the constant/global-section
adjunction. The canonical constant arrow of `UF` is invertible, while its
actual evaluation counit `ΔΓ(UF) → UF` is not. The final contradiction refutes
the implication between these two specified arrows at the supplied witness.
It does not assume either final conclusion as a structure field.

The right-extension formula is
`(UF)(d) = Nat(D(i(-),d),F)`; the chosen target line is `y_D(iR)`.
There is no assertion that right extension sends the source line to that
line. The pointwise constant presheaf and its actual evaluation counit are
constructed for small sets. They are not automatically constant sheaves.
`formalization/research/semantics/PRESHEAF-SEMANTICS-080.md` describes the nine
new modules and their exact limits. The native construction remains a
set-valued presheaf construction, without sheaf descent, internal universes,
crisp contexts or a source-language interpretation.

`formalization/src/Orbifolds/CrispPropositions.agda` resolves a consequential
quantifier ambiguity: `RealFlat` ranges over every crisp `P : Type ℓ`.
The letter `P` does not restrict the axiom to propositions. It equates
crisp discreteness with equivalence of the constant-function map
`P → (R → P)`. Source applicability of the new obstruction still needs an
interpretation of this quantified universe, a crisp code for the witness,
the line, the constant map, equivalences, Flat and its counit. External
cardinal bounds alone do not provide those interpretations.

The supplied external `formalization/research/semantics/SITE-TRANSFER-080.md`
works with finite-Weil formal smooth probes and two specified larger sites:
finite smooth presentations with point-covering principal-localization
topology, and finitely generated germ-determined smooth algebras with their
reflected open localizations. It supplies more than a full-inclusion claim:
it calculates pullbacks of principal covers using the body of a nilpotent
perturbation, proves covering-sieve lifting, proves sheafness of the right
extension, and identifies its actual counit using Yoneda. Cartesian or ball
bases require cover refinement, not closure under every principal open.

That report transfers the externally constructed de Rham witness from
`REAL-FLAT-DE-RHAM-078.md`. The resulting larger-site witness is a right Kan
extension; it is not asserted to be a direct de Rham computation on every
germ algebra. The implication fails for the stipulated ordinary-sheaf
interpretation `Flat = ΔΓ`. Changing the topology, line, Flat interpretation,
or quantified universe requires another comparison. Neither the native
conditional presheaf theorem nor the external site argument proves universal
inconsistency of the original foundation. The finite coefficient calculation
in the native de Rham branch does not by itself establish the sheaf witness.
This assessment inspected the supplied argument's scope; it did not
independently reconstruct its analytic and sheaf-theoretic proofs.

## Reproduction and recovery

The byte checks need Python only. After safe extraction, set `root` to the
`myers-agda-checkpoint` directory and run the following in the repository's
`direnv exec . python3` environment. It does not execute archive code:

```python
from pathlib import Path
import hashlib, json, re
root = Path('/tmp/conaled-orbifold-080/myers-agda-checkpoint')
project = root / 'formalization'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((root / 'MANIFEST.json').read_text())
assert all(sha(root / p) == h for p, h in manifest.items())
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()} == set(manifest) | {'MANIFEST.json'}
for label, entry in [('latest-check', 'Everything'),
                     ('intensional-development-check', 'Orbifolds.Intensional.Everything')]:
    receipt = json.loads((project / 'validation' / (label + '.json')).read_text())
    recorded = receipt['checked_source_sha256']
    assert all(sha(project / p) == h for p, h in recorded.items())
    seen, todo = set(), [entry]
    while todo:
        path = project / 'src' / (todo.pop().replace('.', '/') + '.agda')
        if not path.is_file() or str(path.relative_to(project)) in seen:
            continue
        seen.add(str(path.relative_to(project)))
        todo += re.findall(r'^\s*(?:open\s+)?import\s+([\w.]+)', path.read_text(), re.M)
    assert seen == set(recorded)
    print(label, len(seen), hashlib.sha256(json.dumps(recorded, sort_keys=True).encode()).hexdigest())
```

For native replay, copy the extraction first: the supplied ordinary runner
invalidates and replaces its receipt/log pair. Inspection of
`formalization/tools/check_intensional.py`, `tools/stream_check.py` and the
native kit found explicit isolated writable state, binary and setup-data hash
checks, mandatory safety flags, source stability checks, and a fresh-log
coverage check. The ordinary runner owns its compiler lock; adding an outer
`flock` would deadlock it. It requires no Cubical library registry.

The pinned compiler archive is the official Agda 2.8.0.2 Linux x86-64 release,
8,529,008 bytes, SHA-256
`2bcf24bb561b1be859bba841e5d67962d1616b3251bc147f878e4f60a2fbd9f7`.
The binary SHA-256 is
`3fe070780fa370f5b74e5716ebe42fb60ec6b0ad90d13f8ab45d2903abf39b84`.
In a separate copied checkpoint, the supplied recovery commands are:

```sh
python3 agda-native-kit-2.8.0.2/agda_native.py --state agda-state setup
python3 formalization/tools/check_intensional.py --fresh
```

The first downloads and verifies the release, initializes isolated compiler
data and runs positive/negative smoke checks. The second checks the entire
ordinary closure with native `--ignore-interfaces`. Full Cubical recovery uses
the separate `formalization/tools/check.py --setup --fresh --prepare` route
and explicit registry; it is more expensive and is not certified by the
ordinary check. `formalization/README.md`, `TOOLCHAIN-RECOVERY.json` and
`CHECKPOINT-080.md` retain the exact recovery distinctions. Old absolute
working paths and old process IDs in receipts are provenance, not current
commands or permission to signal a process.

For reuse, retain the original theorem's ambient package, the revised
theorem's selected-test meaning, and the obstruction's supplied witness as
separate obligations. End-to-end interpretation still requires actual sites,
sheaves, geometric instances, quotient/descent constructions, higher type
operations and universe/crisp/source-substitution proofs. These are concrete
remaining constructions, not consequences of counting admitted modules.
