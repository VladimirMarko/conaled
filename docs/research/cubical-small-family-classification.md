# Small cubical family codes and decoding

Issue #419 constructs a classifier for small native lawful families. Its code
presheaf retains a selected representable-local filler, not merely a carrier or
an assertion that some filler exists. Decoding constructs a lawful family, and
both directions retain the selected operations under the stated comparisons.
This is the size/classification milestone preceding Glue and the retained
circle-cover interpretation; it does not deliver those later constructions.

## Source rules and levels

The primary source is [CCHM, arXiv:1611.02108v1](https://arxiv.org/pdf/1611.02108v1),
Definition 18 and §8.3. The inspected PDF has 396214 bytes and SHA256
`b9ccc6ae8572db9521927211f7ae86b404eff6955051fafb825df5f9238022f8`.
The selected construction takes codes at a cube to be small fibrant families
over its representable, restricts codes by pullback, decodes at the identity,
and codes a family by its restrictions along generalized elements. The paper's
set-theoretic universe assumptions are not imported as Lean axioms.

The implementation uses the existing De Morgan cube category and its native
fresh-coordinate products. The levels are explicit:

| Object | Lean level |
| --- | --- |
| A native `Context.{u}` | `Type (u+1)`, with values in `Type u` |
| A native `Family` over that context | `Type (u+1)`, with fibers in `Type u` |
| `LocalFilling` of that family | `Type u` |
| A code `SmallFamilyCode.{u} I` | `Type (u+1)` |
| `smallFamilyCodes.{u}` | `Context.{u+1}` |
| `universalDecode` | A functor from code elements to `Type u` |

The code context is larger than its decoded fibers. Contextual codes use the
local `raisedContext`/`raisedSub` adapters. For every ordinary native context Γ,
a map from `raisedContext Γ` to the code presheaf decodes to an ordinary native
`Family Γ`. The existing `Family` interface and universe-free clients are
unchanged. There is no same-level code for the code presheaf itself.

Admission retains a **whole filler** with cap, tube and cube-restriction laws.
This is a stronger selected-operation presentation than an endpoint-composition
field alone. The existing native `Filling.toComposition` observes its far face;
existing connection-based composition-to-filling remains available. No equality
between an arbitrary selected filler and a filler reconstructed from only its
endpoint operation is asserted. The checked local/native round trips below
concern whole fillers, so they do preserve the selected operation exactly.
This report does not claim a complete translation of every CCHM or Agda rule.

## Locality and decoding

[Representables](../../SquareKit/Internal/Cubical/Representables.lean) constructs
represented contexts, their generic elements and evaluation. Its interval
identification uses `Cube.extend`, `pair`, `drop` and `fresh`; it does not adopt
a new cube model.

[LocalFilling](../../SquareKit/Internal/Cubical/LocalFilling.lean) restricts tests
to represented contexts. Its lawfulness predicate still requires both boundary
filling and uniformity. [LocalFillingBridge](../../SquareKit/Internal/Cubical/LocalFillingBridge.lean)
extends local filling by evaluating on generalized elements. It proves element
naturality, both boundaries and arbitrary-context uniformity. `toLocal_toFilling`
and `toFilling_toLocal` recover selected operations, not just existence or
endpoint values. `LocalFilling.comp`, `comp_boundary`, `comp_reindex` and
`comp_native` also identify the representable-local endpoint operation, prove
its laws and recover it from the native filler. The original varying-family
client exercises this bridge.

[SmallFamilyCodes](../../SquareKit/Internal/Cubical/SmallFamilyCodes.lean)
packages a small family and a selected lawful local filler over each
representable. Reindexing preserves this entire package. The code presheaf's
identity and composition laws are proved. [SmallFamilyDecoding](../../SquareKit/Internal/Cubical/SmallFamilyDecoding.lean)
evaluates a code at the identity and constructs its restriction maps, including
identity and composition laws at the heterogeneous context/fiber levels.

[SmallFamilyClassification](../../SquareKit/Internal/Cubical/SmallFamilyClassification.lean)
constructs contextual coding, decoding and the selected decoded filler. A local
test interval is identified with a represented extended cube. The code at that
chart supplies the filler, transported through the proved fiber comparison.
Chart naturality, code reindexing and transport comparisons prove uniformity;
boundary laws alone are not used as a substitute for it.

The underlying family and the whole decoded local-family package commute
strictly with arbitrary native context substitution. Coding native family
reindexing is also a strict equality. `decodeCodeIso` is a natural isomorphism
from decoding a coded family to the original family;
`LocalFamily.decodeCode_filling` proves recovery of its chosen local filler
through that isomorphism. `codeDecodedComparison` supplies the other fiber
comparison. `decoded_represented_family` identifies the entire decoded local
family over each represented element with decoding the corresponding code,
so the same selected-filler recovery applies there. These comparisons are not
asserted to be source-language definitional conversion.

## Constructors and checked consumers

[SmallFamilyConstructors](../../SquareKit/Internal/Cubical/SmallFamilyConstructors.lean)
accepts actual code-valued dependent inputs and constructs Sigma, Pi, dependent
Path and arbitrary discrete codes. It reuses `sigmaFilling`, `piFilling`,
`pathFilling` and `discreteFilling`, through the proved local/native bridge.
The generic decode/code comparison applies to their selected providers as well
as their underlying families. Pi and Path retain the native noncomputable
semantic providers; no executable extraction claim is added.

[SmallFamilySubstitution](../../SquareKit/Internal/Cubical/SmallFamilySubstitution.lean)
compares decoding reindexed constructor codes with decoding constructors of the
reindexed inputs. Dependent arguments are reindexed along `liftSub` of the
decoded domain; Path bodies use the interval lift and their endpoints are
reindexed separately. Native Pi and Path substitution isomorphisms are retained.
`LocalFamily.sigma_reindex` and `discrete_reindex` preserve whole selected
packages strictly. `pi_reindex_filling` and `path_reindex_filling` prove actual
selected-operation compatibility through their native comparison maps. Together
with strict decoded-family reindexing and decode/code filler recovery, these
laws retain the providers through dependent constructor substitution. These are
coherent semantic comparisons, not newly asserted strict constructor conversion
rules.

[The coded examples](../../Examples/CubicalSmallFamilies.lean) include an integer
fiber and a natural-number code with a code-valued family over its decoded
comprehension. That family reads the actual argument and returns `Fin (n+1)`.
The decoded fibers at arguments zero and one cannot be equivalent, established
through the comparison isomorphisms and finite cardinalities. This rules out a
constant-family stand-in. Two successive substitutions preserve the complete
selected decoded family, and the retained last-element observation gives
`5 : Fin 6` after successor and doubling. Constructor examples consume the
public decode and substitution comparisons. A composed client forms a dependent
Sigma, functions from its decoded carrier to a decoded Unit family, and a Path
of the resulting section, then substitutes that Path code. All three native
constructor providers occur in this composition.

Three elaboration guards reject putting the code presheaf at its own fiber
level, admitting only a bare family, and supplying boundary laws without
uniformity. The inspected failures are respectively a universe mismatch and
the missing admission fields. These guards check the interface boundary; they
do not prove that a particular bare family can never admit lawful filling.

## Statement review and limits

All admission and decoding claims quantify native small contexts, not only a
finite test context. Local uniformity quantifies every cube morphism. The bridge
then proves arbitrary-context uniformity. Filler operations and their laws are
separate fields, and classification does not infer lawfulness from a bare
operation. The code map carries the chosen filler through restriction; no
classical selection of unrelated fillers is hidden behind an existence proof.

The finite dependent example and integer code exercise distinct requirements:
the former establishes actual dependency and substitution, while the latter
prevents a finite-only surrogate. The example's non-equivalence and concrete
value are derived through the public comparison results. The general
constructor inputs include arbitrary dependent code maps; they are not limited
to the example's discrete family.

Transport component proofs use heterogeneous equality to compare casts across
proved fiber equalities. They do not identify arbitrary elements of a fiber or
assume uniqueness of fillers. The only inverse claims concern the constructed
comparisons and the selected local/native operations.

Glue, filling of the universe itself, univalence, the circle and source
conversion remain later obligations. The retained
[Monodromy.agda](../../experiments/dependent-higher-identity/Monodromy.agda) is
unchanged. Classifying its integer carrier does not interpret its `ua`, cover
transport, or computation rules. No compiler, runtime or source proof importer
is delivered here.

Validation is recorded against the coordinator's immutable candidate. Focused
author compilation and the initial locality audit are development evidence;
complete guarded build, exhaustive proof audit and independent Standards/Spec
review remain the acceptance gates.
