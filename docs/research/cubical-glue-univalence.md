# Cubical Glue and univalence construction

This is an incomplete, unaccepted checkpoint for #420, based on the checked small-family classifier from #419. A lawful whole Glue filler is constructed, with cap, tube and arbitrary-substitution uniformity laws. Its restriction recovers the entire supplied face filling operation. Normalized local-family codes have strict substitution and full-face equations; `Glue.code_full` recovers the original supplied partial code, and `Glue.code_substitution` preserves supplied codes and their selected fillers under substitution. Universe filling, `ua`, full univalence and their transport consumers remain unfinished. This checkpoint does not close the issue or constitute independent acceptance.

## Native equivalence and extension

`HomotopyEquivalences.lean` defines a homotopy fiber by native dependent sum and cubical Path. Contractibility contains a chosen center and a path from that center to the generic element. `HomotopyEquivalence` requires this contraction over the generic target, so the witness varies naturally over all targets and context restrictions. It is not a definition of set bijection or natural isomorphism. `HomotopyEquivalence.reindex` constructs its substitution witness. `HomotopyEquivalence.ofIso` admits a natural isomorphism by constructing the actual fiber contraction from the native dual interval connection; both complete contraction endpoints are proved.

`EquivalenceExtension.lean` derives extension of a partial section of a contractible family: the contraction supplies the tube from the center to the partial section, and the supplied family filling supplies the endpoint. Its boundary theorem identifies the result with the specified partial section on its face. The general extension lemma takes a filler. `homotopyFiberFilling` constructs that filler from the lawful domain and codomain using the existing sum and path providers; `HomotopyEquivalence.extend` uses it at the generic target. Its boundary law checks without assuming an extension field. Extension along arbitrary target substitutions also has a checked reindexing equation. Reflexive partial fiber data and the resulting boundary path are preserved explicitly. Source-input substitution also preserves the constructed generic fiber filler and extension, with the equivalence and both selected fillers reindexed explicitly. The corresponding ambient face extension, correction and assembled compatible section have checked source-input substitution laws. These equations do not permit arbitrary replacement of the supplied witnesses.

## Interval transport prerequisite

`UniverseFilling.lean` now constructs `IntervalTransport.equivalence` for the actual forward transport map of any supplied lawful interval-family filling. The proof lifts a target-endpoint path to a square, extends the resulting partial dependent path by relative backward filling, and fills a comparison-path box. `FiberExtension.extend_boundary` recovers both components of the original partial homotopy-fiber data. `HomotopyContractible.ofExtensions` turns this constructed contextual extension operation into a center and contraction. No isomorphism-only replacement or additional contractibility assumption is used. `FiberExtension.extend_reindex` proves target-context uniformity of the complete extension, including its selected comparison filler. The local construction can also take an explicit map with a required equality to the actual transport map. `HomotopyContractible.ofExtensions_iso` preserves the center and whole chosen contraction when an isomorphism preserves the contextual extension operation; it retains that preservation premise and source-extension uniformity explicitly. `FiberExtension.extend_input_reindex` discharges the transport-specific extension-preservation premise. `IntervalTransport.equivalenceOf_reindex` then proves equality of the chosen equivalence after source substitution, retaining both its center and contraction. It compares an explicit map `f` with the required equality `f = map F`; the ordinary `equivalence` uses the actual map. Universe filling and full univalence remain outstanding.

## Frozen consumers

The Boolean consumer must construct a universe loop whose transport sends true to false. The integer consumer must detect orientation: successor transport sends 3 to 4, whereas transport for its inverse sends 3 to 2. These observations must use the constructed `ua` and universe filling.

`Examples/CubicalStateTransport.lean` retains the direct native equivalence client. A state package includes its initial state, transition, invariant, initial validity and preservation proof. Successor conjugation sends the package with initial state 0, transition +2 and even invariant to one with initial state 1, transition +2 and odd invariant. The entire proof-bearing package must subsequently be compared with dependent transport along the universe path. The direct calculation alone does not establish that comparison.

`Examples/CubicalGlue.lean` supplies the constant Boolean-to-Unit rejection control. It builds two sections of the generic homotopy fiber, observes their Boolean components, and uses native discrete-path rigidity to refute a contraction. This rejects the actual equivalence contract, rather than relying on missing Lean instances. Positive controls now include Boolean transposition and integer successor/inverse through the constructed isomorphism adapter. A separate theorem rejects contradictory full-face data using the actual Glue introduction compatibility equation. These controls still do not assert universe-path transport.

## Levels and selected structure

The classifier's codes live in Type (u+1), while decoded fibers live in Type u. A focused probe constructs the functor from an arbitrary larger context's elements to Type u and selects lawful small decoded families on raised small represented charts. This is local reuse of #419 and does not require changing the global `Family` interface. It does not yet construct filling for the universe itself.

Codes retain the selected whole filling operation. CCHM's full-face composition equation only compares the far endpoint. A Glue filling construction must additionally prove preservation of the whole selected filler on the full face. `GlueFilling.lean` now constructs interval-universal faces with strict substitution and an all-future-restrictions specification. Its box augmentation lemma proves that adding a compatible selected whole tube forces a lawful filler to recover that whole section on the added face. `GlueFillingSubstitution.selectedFaceFill` actually uses the supplied face-family filler. Its cap/tube laws and whole-section preservation are checked. The constructed preliminary filler discharges the lawfulness premise.

The preliminary operation is now constructed separately. It first fills the ambient family, extends the equivalence fiber over the gluing face while fixing the original cap and tube, and uses an auxiliary ambient box to correct values along the resulting path. `preliminaryFill_fills` proves both original box laws. `preliminaryFilling_lawful` also proves arbitrary-substitution uniformity. The selected-face repair also has a checked uniformity proof. `filling_lawful` establishes the final filling laws, and `filling_full` proves equality with the supplied face filling operation after restriction and transport along `family_full`. This equality quantifies over every context, line, partial face and open box. No impossibility result or justification for discarding selected structure has been established.

`GlueSubstitution.reindexIso` recovers the complete compatible data under arbitrary substitution, using the existing bijection on generalized arrows. This is a checked natural isomorphism of the current presentation. `SmallFamilyGlue.lean` additionally normalizes the off-face carrier on represented cubes. `Datum.smallFamily_substitution` proves equality of the resulting family functors, and `smallFamily_full` retains the actual face family. Transport of the constructed filler is lawful and `smallFilling_full` recovers the whole supplied face filling operation. `LocalFamily.glue_full` also establishes equality of complete small families for the original presentation. The complete normalized selected filling now has a checked source-input substitution equality. `LocalFamily.normalizedGlue` and `Glue.localCode` satisfy strict substitution and full-face equations. `Glue.code` accepts supplied universe maps and `code_full` recovers the exact original partial code. Universe filling remains unfinished. Exact semantic round trips are now checked: `LocalFamily.decoded_code` recovers the complete original local family, and `LocalFamily.code_decoded` recovers the original contextual code map. The comparison is induced by equalities of represented indices, and its preservation of the selected filling proves equality of the whole code. This strengthens the existing semantic comparison without changing the code carrier; it does not claim source-language definitional conversion.

## Source admission

The semantic reference is [CCHM, arXiv:1611.02108v1](https://arxiv.org/html/1611.02108v1), especially the equivalence extension, Glue, universe and univalence constructions. The retained PDF has SHA256 `b9ccc6ae8572db9521927211f7ae86b404eff6955051fafb825df5f9238022f8`.

The retained experiment pins Agda 2.8.0.2 and Cubical v0.9 at `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. Eight relevant modules were recovered from that retained checkout and matched against the module hashes in `experiments/dependent-higher-identity/validation.json`: builtin Equiv and Glue, Primitive.Cubical, Cubical.Core.Glue, Foundations.Univalence, and Data.Equality's Univalence, S1 and Base. The external handoff records the exact copies and hashes.

The builtin Equiv source uses contractible homotopy fibers. Its `equivProof` adds a zero-face branch to the CCHM extension recipe to improve Agda transport computation. That extra source conversion is not implied by proving the semantic extension boundary theorem. A complete rule-to-theorem ledger is still required. Uncovered source conversions belong explicitly to #422; no evaluator, canonicity or cost result is claimed here. #421 retains the circle construction.

| Pinned source obligation | Current native evidence | Remaining boundary |
|---|---|---|
| `isEquiv.equiv-proof` uses contractible fibers | `HomotopyEquivalence.fibers`, native Sigma/Path fiber, discrete rejection and Unit-identity positive control | General native-isomorphism adapter, Boolean and successor/inverse equivalence witnesses are checked. The univalence consumer remains unfinished. |
| `primGlue`, `prim^glue`, `prim^unglue` | Actual face/ambient carrier, compatible introduction, unglue-introduction equation, compatible-presentation eta, full-face family equality | Complete compatible-data substitution isomorphism and preliminary lawful filling are checked. Selected lawful Glue filling and exact full-face recovery are checked. Normalized local-family code substitution and exact full-face recovery are checked; supplied-code substitution is checked; universe filling remains unfinished. Builtin declarations alone do not establish their source reduction rules. |
| `equivProof` extends partial fiber data | Constructed fiber filling and generic-target extension boundary theorem | The pinned Agda zero-face optimization is an additional source conversion obligation. |
| `primTransp` and `primHComp` | Existing restricted transport and native homogeneous filling providers remain the owners | Their connection to the new Glue/universe construction remains unfinished. Each claimed source use must discharge the actual constancy or boundary premises. |
| `ua`, `uaβ`, universe filling and univalence | Frozen Boolean, successor/predecessor and whole-package expectations; direct native conjugation checks | Universe-path construction, full equivalence and dependent transport comparison remain unfinished. |

This ledger records inspected sources and proof obligations. It does not yet constitute source admission for #420.

## Preserved stopping boundary

This local checkpoint stops after Glue/code operations and the substitution-coherent chosen interval-transport equivalence. The focused checks used CPU 0 and private outputs; they are not the repository's final guarded build/proof audit or independent Standards/Spec acceptance. The full construction is not imported through `SquareApplications.lean`.

Four substantial components remain:

1. Assemble compatible partial code, family and equivalence data, and construct lawful universe filling across the larger-context charts. The supplied-code operation and cap/tube code-system boundary and substitution equations are checked; assembly of the maps and complete chosen equivalence data remains.
2. Construct `ua` with exact endpoint codes and prove its transport comparison. An endpoint isomorphism alone does not establish code equality.
3. Prove full univalence, including its required homotopies. The constructed transport equivalence alone does not prove this.
4. Check the Boolean transposition, successor/inverse orientation and complete state-package universe-transport consumers, then finish the pinned source-rule ledger and integrated independent acceptance.

No impossibility result or architectural replacement is claimed. The preserved handoff distinguishes completed checked statements, planning notes and failed proof attempts.


## Resumed construction

`CodeSystem.glue` assembles compatible partial universe codes on a union of
faces. Its restriction equations recover the original codes, including the
selected local filling operations. `CodeSystem.Maps.glue` separately assembles
compatible family maps and recovers both inputs. Code compatibility alone does
not assert map or equivalence compatibility.

`CodeSystem.Box.partialCode` constructs the cap/tube code system from an actual
open code box. Its overlap follows from the box boundary equation. Exact cap,
tube and substitution equations are proved. The constant Boolean box exercises
a nonempty overlap; a Unit tube over a Boolean cap is rejected. A Boolean/Unit
two-endpoint boundary is also constructed. That partial boundary is not a path
between the two codes.

`UniverseCodePaths.lean` defines the dimension-dependent universe family and
proves the correspondence between code-valued interval lines with exact
endpoints and native universe paths. Both round trips preserve the line. The
adapter requires the line as input; it neither constructs `ua` from an
equivalence nor supplies universe filling or univalence.

`UniverseComposition.lean` constructs a small-context code filler. The complete
cap/tube face `(i = 0) ∨ φ` is closed under the connection `i ∧ j`. Contracting
that whole face produces one backward code line from the supplied partial code
to the cap pullback. Its actual decoded filling supplies the homotopy
equivalence used by Glue. This avoids separately choosing cap and tube
equivalences and then imposing their overlap agreement.

The resulting `Box.fillCode` recovers the original cap and tube codes exactly.
No premise identifies transport along an arbitrary constant line with identity.
The completed small-context filler commutes with base substitution, retaining
the chosen map and fiber contraction. `UniverseKan.lean` supplies the small
chart adapters for a large-context universe open box and proves compatibility
under chart restriction. Larger-context section assembly and its filling laws,
`ua`, full univalence and the required transport consumers remain within #420.
These small-context results do not yet constitute the lawful filling of the
universe family.

### Constructed universe filling and unglue equivalence

`UniverseKan.lean` now constructs `SmallUniverse.filling` for the actual
`SmallUniverse.family` over a context at universe level `u+1`, whose fibers
are small-family codes at level `u`. It reads each open box on represented
small charts, applies the checked code filler, and evaluates at the generic
point. The chart substitution law supplies section naturality and uniformity.
`fillTerm_cap` and `fillTerm_tube` recover the original supplied codes;
`filling_lawful` proves both boundary recovery and substitution. No universe
filling field is assumed. The focused check passed at default heartbeats.

`GlueEquivalence.lean` constructs `Glue.unglueEquivalence`: the actual
elimination map has contractible native homotopy fibers. Its proof extends
partial fibers using the supplied face equivalence and the lawful face and
ambient fillers, then derives the center and contraction. The Boolean-flip
client checks the constructed fiber center and its path to the target.
Targeted axiom inspection found only the repository's ordinary Lean axioms
(`propext`, `Classical.choice`, and `Quot.sound`).

These are checked intermediate results. They do not yet provide `ua`, its
transport comparison, full univalence, or final build/audit/review acceptance.

### Exact endpoint `ua`

`DisjointEquivalences.lean` assembles genuine equivalences on a disjoint face
cover. It retains the supplied branch centers and contractions and proves
substitution for the underlying contraction assembly. `Univalence.lean` uses
this construction with the supplied equivalence at zero and identity at one.
`uaCode_zero` and `uaCode_one` recover the original codes, including their
selected fillers; `ua` converts the line into a native path in the actual
universe family over the raised context. These declarations passed a focused
Lean check.

The transport comparison and full univalence are distinct remaining claims.
In particular, CCHM's inverse-homotopy construction involves chosen transport
in a constant family. It cannot be identified literally with the identity
endpoint used here without a further coherence argument. No regularity axiom
is added to remove that obligation.

### Transport comparison

`UnivalenceTransport.lean` now proves full-face recovery for elimination from
the supplied Glue code and constructs `Univalence.comparison`. For every
section of the decoded source, this is a native target path from the supplied
map's action to the actual selected transport along `uaCode`. Its construction
maps the filled line through unglue and uses the exact endpoint equations.
`mapLineComparisonTo` handles the endpoint casts without replacing selected
transport by the supplied map. This focused check passed at default limits.
The result is semantic; it asserts no evaluator behavior or cost bound.

The full native univalence theorem still requires the internal equivalence
family, its native proposition facts, and the homotopy/retract arguments.
The planned retract route preserves the chosen `ua` and uses this comparison;
it does not assume constant-family transport is literally identity.

`Examples/CubicalUnivalenceTransport.lean` checks the requested discrete
observations of that actual transport: Boolean transposition sends true to
false and false to true; integer successor sends 3 to 4; its inverse sends
3 to 2. The proof maps the comparison path into the constant target family
and applies native discrete-path rigidity. This is a checked semantic
observation, not execution of the noncomputable construction. The dependent
whole-state-package comparison remains outstanding.
### Native universal decoding

`UniverseDecode.lean` constructs the universal decoding family in the larger
context universe. Its fibers are raised by `ULift`; small represented charts
supply their original chosen fillings. `NativeDecode.filling_lawful` proves
cap and tube recovery and uniform substitution. `filling_reindex` retains the
selected filling exactly, rather than merely asserting that another filling
exists. No resizing or universe-decoding filling is postulated.

`UniversePathEquivalence.lean` uses that filling for arbitrary native universe
paths over a context in the larger universe. `pathToMap` is the actual chosen
interval transport, and `pathToEquivalence` constructs its native contractible
homotopy fibers. These modules passed focused checks at default Lean limits.
This supplies the forward operation needed for full univalence; it does not
yet prove that the operation from paths to equivalences is itself an
equivalence. The reverse operation, its coherence, and the final acceptance
checks remain necessary.
