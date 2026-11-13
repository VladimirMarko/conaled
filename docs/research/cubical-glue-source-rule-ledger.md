# Cubical Glue: source-rule ledger

Checkpoint ledger for #420, inspected 2026-11-13 in worker420 at committed checkpoint
`b6efed37aba9d92e9c408c3e4c6d6dfaa3e7d94b`, with active uncommitted work excluded from completed claims.
This records semantic construction evidence and the remaining source-admission
boundary. It does not certify full univalence, the unchanged Agda cover, or final
integrated acceptance. The generic native `ua` still depends on the unfinished
small-code substitution proof at this inspection.

The later checkpoint `30b68d9c` also constructs a native path from explicitly
supplied coherent chart data. It does not discharge that coherence premise for
the actual `ua` construction. Merge `007c7450` incorporates the validated #510
base `65123a90` without changing these mathematical claims.

## Sources and meaning of evidence

The reference calculus is [CCHM, arXiv:1611.02108v1](https://arxiv.org/html/1611.02108v1),
particularly §§5.3, 6.1–6.2, 7.1–7.2, 8.3 and Appendix B. The retained PDF has
SHA256 `b9ccc6ae8572db9521927211f7ae86b404eff6955051fafb825df5f9238022f8`.
Its Glue, universe composition and univalence arguments guide the construction;
the paper's syntax interpretation theorem is about its own calculus.

The separate source target is [Agda 2.8.0.2 Cubical](https://agda.readthedocs.io/en/v2.8.0.2/language/cubical.html).
Agda splits composition into generalized transport and homogeneous composition.
The primitive signatures are pinned in
[Agda.Primitive.Cubical](https://github.com/agda/agda/blob/v2.8.0.2/src/data/lib/prim/Agda/Primitive/Cubical.agda#L55-L67)
and [Agda.Builtin.Cubical.Glue](https://github.com/agda/agda/blob/v2.8.0.2/src/data/lib/prim/Agda/Builtin/Cubical/Glue.agda#L7-L17).
Those signatures alone are not proofs of reduction-rule preservation.
The retained library is Cubical v0.9 commit
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.

In this ledger, **semantic equality** means a Lean theorem identifying semantic
families, terms or chosen filling data. A **native path** is a term of the
presheaf Path family. Neither automatically gives **source judgmental
conversion**, which requires an interpretation of the relevant source judgments
and substitution rules. Conversely, a source conversion may be interpreted by a
proved semantic equality; it need not be Lean's own definitional equality.
An isomorphism or path cannot silently replace the equality promised by that
interpretation. Evaluation simulation, canonicity and cost are separate contracts.
See [judgment compatibility](cubical-judgment-compatibility.md) and the
[model construction](cubical-model-construction.md).

## Rule-to-construction mapping

Paths below are relative to the repository root. “Available” records checked
construction checkpoints, not the final #420 build/review outcome.

| Source obligation | Native evidence available | Exact admission boundary |
| --- | --- | --- |
| Genuine equivalence, as contractible fibers | `HomotopyEquivalences.lean`: `HomotopyEquivalence.fibers`, native Σ/Path fiber and chosen contraction; `ofIso` constructs that data for native isomorphism clients. `EquivalenceFamilies.lean` represents `Contr`, `IsEquiv` and `Equiv` internally with section bridges. | Preserve the selected center and contraction. A bijection, host proof irrelevance or constant family of external witnesses does not replace the native witness. |
| Glue formation and compatible introduction | `Glue.family`, `Glue.intro`, and its explicit compatibility premise in `Glue.lean`; `SmallFamilyGlue.lean` supplies normalized lawful codes. | Interpret the actual source level and face premises. Local families have one declared small level; do not claim all heterogeneous Agda level combinations merely because the primitive permits two levels. |
| Unglue of introduction | `Glue.unglue_intro` is a semantic term equality. | Attach the equation to the source eliminator rule and its interpreted premises; it is not an importer on its own. |
| Glue eta | `Glue.compatible_eta`, together with `familyIso`, recovers the complete compatible presentation. | The source eta judgment needs the explicit presentation comparison in its interpretation, not an unspecified homotopy. |
| Full-face type, introduction and elimination | `family_full`, `fiberEquiv_full`, `fiberEquiv_symm_full`; `UnivalenceTransport.lean`: `unglue_full`, `codeUnglue_full`; `SmallFamilyGlue.lean`: `code_full`. | Family/code equalities and typed maps are available. The full-face source introduction computation must be stated through these exact casts if a source-facing judgment theorem is claimed. |
| Substitution | `GlueSubstitution.reindexIso`, `compatibleReindex_intro`; `SmallFamilyGlue.code_substitution`; committed `GlueEliminationSubstitution.codeUnglue_substitution`. | Distinguish the compatible-carrier isomorphism from strict normalized code equality. Neither settles the still-active `Univalence.uaCode_reindex` construction. The code and eliminator congruence lemmas were checked and committed subsequently in `30b68d9c`; final acceptance remains pending. |
| Derived lawful Glue filling | `GlueFillingSubstitution.filling_lawful`, `filling_full`, `filling_input_reindex`: actual construction, whole selected full-face filler recovery, source-input substitution. `GlueEquivalence.unglueEquivalence` constructs native fiber contractions. | This supplies semantic Kan data. It does not assert algorithmic equality with every Agda Glue `transp`/`hcomp` reduction branch. |
| Generalized transport | `RestrictedTransport.lean`: `RestrictedConstancy`, `Filling.transp_on_face`, `transp_computation`, `transp_reindex`; `Judgments/TransportRules.lean` and `TransportSubstitutionRule.lean` validate provider-annotated rules. | Map the source face-constancy condition to the supplied semantic witness and selected provider. Arbitrary lawful filling alone is not a proof of every source constant-transport conversion. |
| Homogeneous composition | `Filling.hcomp`, `hcomp_boundary`, `hcomp_reindex`; `OpenBox` retains the cap/tube compatibility premise. | These are boundary and substitution laws, not a rule-by-rule simulation of the source type-directed reductions. |
| Universe filling and decoding | `UniverseKan.filling`, `filling_lawful`; `UniverseDecode.liftedDecode` and `NativeDecode.filling_lawful`, `filling_reindex`. Codes retain selected lawful small fillers; the large-context decoder lifts their fibers explicitly. | Declare `smallFamilyCodes.{u}` at level `u+1`, small decoded fibers at level `u`, and lifted native fibers over large contexts. No resizing or all-level source universe interpretation follows. |
| `ua` and its action | `Univalence.uaCode`, `uaCode_zero/one`, `ua`; `UnivalenceTransport.transport`, `comparison`, `unglueLine_zero/one`. | The comparison is a native path from the supplied-map output to the transported input (reverse it for the usual uaβ orientation). It does not assert generic definitional equality of transport with that map. |
| Full univalence | `NativeUnivalenceMap.pathToEquiv` is a native map into internal equivalences. `EquivalencePaths.ofHomotopy`, `NativePathSingleton.contractible`, `HomotopyContractible.retract`, and `HomotopyEquivalence.ofContractibleTotals` supply checked prerequisites. | **Incomplete:** generic reverse map still requires small-code substitution. Its drafted presence in `NativeUnivalenceUa.lean` is not a checked theorem that `pathToEquiv` has contractible fibers. Finish the generic comparison and retract/fiber argument. |

The full-face and eta source equations, transport constancy and homogeneous box
premises are specified in the pinned
[Agda documentation](https://agda.readthedocs.io/en/v2.8.0.2/language/cubical.html#glue-types).
In particular, transport requires constancy when its face is full and computes
to identity there; `hcomp` requires initial cap agreement. The semantic rows
retain those premises instead of inferring them from similar operation names.

## Two source computations not covered by generic filling laws

The pinned [builtin equivalence implementation](https://github.com/agda/agda/blob/v2.8.0.2/src/data/lib/prim/Agda/Builtin/Cubical/Equiv.agda#L19-L43)
defines equivalence through contractible fibers. Its `equivProof` deliberately
adds a zero-face branch to `contr'`, selecting the contraction center there for
improved Glue transport computation. Native extension boundary and uniformity
prove recovery on the supplied partial face. They do not establish this extra
empty-face definitional choice. **Uncovered source conversion:** recovery of the
chosen center for that optimized empty-face extension, where the cover's actual
derivation depends on it.

The primitive split `transp`/`hcomp` rules for Glue and the universe must likewise
be checked against their precise source reductions. **Uncovered source
conversion:** equality between the interpreted source reduction branch and the
selected native Glue/universe provider, beyond the proved cap, tube, full-face
and substitution equations. No rule-by-rule Agda evaluator correspondence was
constructed or inspected exhaustively here. This bounded ledger does not claim
that every such branch is used by the retained cover.

The pinned library defines `ua` by two Glue endpoint faces. Its
[`ua` construction](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/Foundations/Univalence.agda#L31-L34)
and named `uaβ` theorem must be kept distinct: the latter is a path-level
computation theorem, not permission to equate all transport expressions by
conversion. The library also uses stronger definitional glue/unglue inverses
for certain helpers; those helpers require their own rule mapping if imported.

## Checked clients and limits

`Examples/CubicalUnivalenceTransport.lean` observes actual decoded `ua`
transport: Boolean transposition, successor taking 3 to 4, and inverse taking
3 to 2. `Examples/CubicalStatePackageUa.lean` fills the whole native dependent
package along the actual successor carrier line and proves `initialPackage_eq`
and `finalPackage_eq`, including the proof-bearing fields. This goes beyond
host conjugation alone. The derived filler is in `CubicalStatePackageFamily`.

`Examples/CubicalGlue.lean` retains malformed-face and constant Boolean-to-Unit
non-equivalence rejection. Direct native equivalence clients remain usable.
These are semantic clients. They do not interpret `Monodromy.agda` unchanged,
and integer observations alone cannot certify preservation of its derivation.
Targeted package/equivalence-path/contractible-total axiom logs show only
`propext`, `Classical.choice`, and `Quot.sound`; this ledger ran no new builds
and does not replace final exhaustive #420 validation.

## Existing ownership and acceptance still required

[#422](https://github.com/VladimirMarko/conaled/issues/422), read on 2026-11-13,
already owns the unchanged circle cover and dependent monodromy witness. Its
frozen source is `Monodromy.agda`, SHA256
`bbca6eabc7d35040fd5bb1fcc84f49c12ddfcfb90ffc2edb6d922a8c6e622aa3`.
No new issue is required for the source-admission work:

1. In #422, derive the declaration-level dependency inventory for `Cover`, the
   successor path and `step`. For each used Glue/transp/hcomp conversion, name
   the source rule, interpreted premise, native equation or remaining gap.
   The zero-face optimization and split-operation reductions above are explicit
   candidates to resolve, not assertions that the entire compiler is needed.
2. In #422, interpret Path-to-indexed-identity conversion and the actual indexed
   elimination used by `step`. Native marked identity or a new Path-only proof
   is not automatically that interpretation. Record a changed proof separately
   if the unchanged conversion cannot be admitted.
3. Preserve #422's four named results and the unequal integer observer through
   the interpreted derivation, with term/dimension substitution and the promised
   conversion judgment. Keep the direct native and Cartesian comparisons named
   as comparisons. Circle construction remains #421's prerequisite.
4. In #420, finish generic small-code substitution, generic `ua`, its full
   equivalence-family comparison, and actual contractible fibers of
   `pathToEquiv`. The accepted model must retain selected filling/equivalence
   data. This ledger cannot discharge that mathematical gap.
5. Before #420 acceptance, integrate the final code, update chronological
   checkpoint documentation, connect each claimed source rule to the exact
   theorem or explicit #422 residual, and complete guarded build/audit plus
   independent Standards/Spec review. Do not promote a drafted declaration or
   a conditional chart assembly to completed full univalence.

No evaluator simulation, canonicity, runtime backend or cost result is claimed.
