# Raw Felix constructions and equation recovery (#450)

This is the R2 implementation record for [#450](https://github.com/VladimirMarko/conaled/issues/450).
The source is Felix at `6f36d28097db7ea5f5df3263db3e8be08f74e490`.
The [complete source index](felix-full-correspondence-source-index.md) retains
line links, hashes, inactive declarations and unfinished proposals. This report
adds the implementation correspondence; it does not replace the historical inventory.

## Semantics and assumptions

Every table entry below is in namespace `SquareKit`. Raw operations use
`CategoryOps` and the indicated terminal/product/coproduct data. They assume
no equations. Category and product congruence are separate from category and
product laws. The generic Cartesian proofs state `E.Rel`, never raw arrow equality.
Their explicit binders record the premises actually used: projection/pair equations
need only `ProductLaws`; composite equations generally also need category laws
and both congruence packages. Unit insertion followed by elimination needs no
terminal uniqueness; the reverse equation does. Inverse-preservation statements
accept a selected left inverse, without assuming a second inverse equation.

Object and hom universes are independent. Products take the maxima of the two
object levels and of the two hom levels. `FunctionLift.map.{u,v}` goes from
`Type u` to `Type (max u v)`; two consecutive lifts are checked. `RawQuiv.Obj.{u,v}`
is exactly Mathlib `Quiv.{v,u}`, whose objects have no category operations.
The Mathlib product and `SingleObj` bridges have preservation proofs and arrow
round trips. Monoid composition is `g * f`, matching Mathlib's categorical order.

Felix's `Equivalent q` permits computational witnesses in `Set q`. These R2
constructions specialize equivalence to the repository's `Prop`-valued `HomEquiv`.
They do not recover computational equivalence witnesses; that is [#453](https://github.com/VladimirMarko/conaled/issues/453).
`HEq` in `RawArrow.verticalAlong` transports the raw middle-arrow equality across
the explicitly supplied middle-object equalities. The normalized `vertical`
operation accepts the weaker semantic middle compatibility. `compose` itself
needs only equality of the middle objects.

`Squared` exposes both componentwise equivalence and the relation induced by
unsquaring. They are not equated: `induced_not_componentwise` and
`components_distinct` exhibit the difference using an empty second factor.
The product comparison is the middle-four shuffle, with independently checked
nonidentity behavior and inverse recovery.

## Raw definitions

The entries in this table are operation-for-operation translations of the pinned
right-hand sides. In particular, `first` and `second` retain the identity
compositions present in Felix; no law is used to simplify raw constructors.
`sub_refl`, `subEq_refl` and `sub_equiv` check reflexive and witness-independent
transport. `jam` is the copair of two raw identities.

| Pinned declaration | Local recovery |
|---|---|
| [`Category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L17) | `CategoryOps` |
| [`id`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L20) | `CategoryOps.ident` |
| [`_∘_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L21) | `CategoryOps.comp` |
| [`sub`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L25) | `CategoryOps.sub` |
| [`sub≡`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L28) | `CategoryOps.subEq` |
| [`Cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L34) | `TerminalOps + ProductOps` |
| [`!`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L41) | `TerminalOps.terminal` |
| [`_▵_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L42) | `ProductOps.pair` |
| [`exl`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L43) | `ProductOps.fst` |
| [`exr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L44) | `ProductOps.snd` |
| [`dup`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L46) | `Cartesian.dup` |
| [`_⊗_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L52) | `Cartesian.tensor` |
| [`first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L55) | `Cartesian.first` |
| [`second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L58) | `Cartesian.second` |
| [`twice`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L61) | `Cartesian.twice` |
| [`unitorᵉˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L64) | `Cartesian.unitLeft` |
| [`unitorᵉʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L67) | `Cartesian.unitRight` |
| [`unitorⁱˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L70) | `Cartesian.insertLeft` |
| [`unitorⁱʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L73) | `Cartesian.insertRight` |
| [`constˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L76) | `Cartesian.constLeft` |
| [`constʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L79) | `Cartesian.constRight` |
| [`assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L82) | `Cartesian.assocLeft` |
| [`assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L85) | `Cartesian.assocRight` |
| [`inAssocˡ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L88) | `Cartesian.inAssocLeft'` |
| [`inAssocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L91) | `Cartesian.inAssocLeft` |
| [`inAssocʳ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L94) | `Cartesian.inAssocRight'` |
| [`inAssocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L97) | `Cartesian.inAssocRight` |
| [`swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L100) | `Cartesian.swap` |
| [`inSwap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L103) | `Cartesian.inSwap` |
| [`transpose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L106) | `Cartesian.transpose` |
| [`inTranspose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L109) | `Cartesian.inTranspose` |
| [`_⦂_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L114) | `Cartesian.constants` |
| [`jam`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L132) | `CoproductOps.jam` |

## Category and Cartesian equations

| Pinned declaration | Local recovery |
|---|---|
| [`Category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L23) | `CategoryLaws + CategoryCongr` |
| [`identityˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L29) | `CategoryLaws.id_comp` |
| [`identityʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L30) | `CategoryLaws.comp_id` |
| [`assoc`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L31) | `CategoryLaws.assoc` |
| [`∘≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L34) | `CategoryCongr.comp` |
| [`∘-assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L37) | `CategoryLaws.assoc` |
| [`∘-assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L40) | `RawReasoning.assoc_left3` |
| [`∘≈ˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L43) | `CategoryCongr.comp h (E.refl _)` |
| [`∘≈ʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L46) | `CategoryCongr.comp (E.refl _) h` |
| [`Cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L54) | `TerminalLaws + ProductLaws + ProductCongr` |
| [`∀⊤`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L62) | `TerminalLaws.unique` |
| [`∀×`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L64) | `Cartesian.pair_iff` |
| [`▵≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L68) | `ProductCongr.pair` |
| [`∀×→`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L70) | `Cartesian.pair_iff_forward` |
| [`∀×←`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L74) | `Cartesian.pair_iff_backward` |
| [`▵≈ˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L78) | `Cartesian.pair_congr_left` |
| [`▵≈ʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L81) | `Cartesian.pair_congr_right` |
| [`exl∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L88) | `ProductLaws.fst_pair` |
| [`exr∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L91) | `ProductLaws.snd_pair` |
| [`exl∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L95) | `Cartesian.fst_tensor` |
| [`exr∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L97) | `Cartesian.snd_tensor` |
| [`exl∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L100) | `Cartesian.fst_first` |
| [`exr∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L103) | `Cartesian.snd_first` |
| [`exl∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L106) | `Cartesian.fst_second` |
| [`exr∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L109) | `Cartesian.snd_second` |
| [`exl▵exr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L112) | `Cartesian.pair_projections` |
| [`⊗≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L115) | `Cartesian.tensor_congr` |
| [`⊗≈ˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L130) | `Cartesian.tensor_congr_left` |
| [`⊗≈ʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L134) | `Cartesian.tensor_congr_right` |
| [`id⊗id`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L138) | `Cartesian.tensor_ident` |
| [`▵∘`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L141) | `ProductLaws.pair_comp` |
| [`⊗∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L144) | `Cartesian.tensor_pair` |
| [`first∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L159) | `Cartesian.first_pair` |
| [`second∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L163) | `Cartesian.second_pair` |
| [`⊗∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L167) | `Cartesian.tensor_comp` |
| [`first∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L171) | `Cartesian.first_tensor` |
| [`⊗∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L176) | `Cartesian.tensor_first` |
| [`⊗∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L180) | `Cartesian.tensor_second` |
| [`second∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L184) | `Cartesian.second_tensor` |
| [`first∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L188) | `Cartesian.first_comp` |
| [`second∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L192) | `Cartesian.second_comp` |
| [`first∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L196) | `Cartesian.first_second` |
| [`second∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L200) | `Cartesian.second_first` |
| [`unitorᵉˡ∘unitorⁱˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L207) | `Cartesian.unitLeft_insertLeft` |
| [`unitorᵉʳ∘unitorⁱʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L210) | `Cartesian.unitRight_insertRight` |
| [`unitorⁱˡ∘unitorᵉˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L213) | `Cartesian.insertLeft_unitLeft` |
| [`unitorⁱʳ∘unitorᵉʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L222) | `Cartesian.insertRight_unitRight` |
| [`exl∘swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L234) | `Cartesian.fst_swap` |
| [`exr∘swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L237) | `Cartesian.snd_swap` |
| [`swap∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L240) | `Cartesian.swap_pair` |
| [`swap∘swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L256) | `Cartesian.swap_swap` |

## Reasoning equations

| Pinned declaration | Local recovery |
|---|---|
| [`sym≈-sym≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L31) | `RawReasoning.symm_map` |
| [`elimˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L42) | `RawReasoning.elim_left` |
| [`introˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L51) | `RawReasoning.intro_left` |
| [`elimʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L54) | `RawReasoning.elim_right` |
| [`introʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L63) | `RawReasoning.intro_right` |
| [`elim-center`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L66) | `RawReasoning.elim_center` |
| [`intro-center`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L69) | `RawReasoning.intro_center` |
| [`∘-assocˡ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L79) | `RawReasoning.assoc_pull_left` |
| [`∘-assocʳ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L83) | `RawReasoning.assoc_pull_right` |
| [`∘-assocˡʳ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L88) | `RawReasoning.assoc_pull_left_right` |
| [`∘-assocʳˡ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L92) | `RawReasoning.assoc_pull_right_left` |
| [`∘-assoc-elimˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L97) | `CategoryLaws.cancel_left` |
| [`∘-assoc-elimʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L101) | `RawReasoning.cancel_right` |
| [`∘-assocʳ³`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L106) | `RawReasoning.assoc_right4` |
| [`∘-assocʳ⁴`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L111) | `RawReasoning.assoc_right5` |
| [`∘-assocʳ⁵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L116) | `RawReasoning.assoc_right6` |
| [`∘-assocʳ⁶`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L121) | `RawReasoning.assoc_right7` |
| [`∘-assocˡ³`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L126) | `RawReasoning.assoc_left4` |
| [`∘-assocˡ⁴`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L131) | `RawReasoning.assoc_left5` |
| [`∘-assocˡ⁵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L136) | `RawReasoning.assoc_left6` |
| [`∘-assocˡ⁶`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L142) | `RawReasoning.assoc_left7` |
| [`∘≈ʳ²`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L148) | `RawReasoning.congr_right2` |
| [`∘≈ʳ³`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L152) | `RawReasoning.congr_right3` |
| [`∘≈ʳ⁴`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L157) | `RawReasoning.congr_right4` |
| [`∘≈ʳ⁵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L162) | `RawReasoning.congr_right5` |
| [`∘≈ʳ⁶`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L168) | `RawReasoning.congr_right6` |
| [`cancelʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L180) | `RawReasoning.cancel_right` |
| [`cancelˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L193) | `CategoryLaws.cancel_left` |
| [`cancelInner`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L206) | `CategoryLaws.cancel_middle` |
| [`∘-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L220) | `RawReasoning.comp_inverse` |
| [`⊗-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L224) | `Cartesian.tensor_inverse` |
| [`first-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L229) | `Cartesian.first_inverse` |
| [`second-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L233) | `Cartesian.second_inverse` |
| [`assocˡ∘assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L243) | `Cartesian.assocLeft_assocRight` |
| [`assocʳ∘assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L267) | `Cartesian.assocRight_assocLeft` |
| [`assocʳ∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L288) | `Cartesian.assocRight_pair` |
| [`assocˡ∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L303) | `Cartesian.assocLeft_pair` |
| [`⊗⊗∘assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L320) | `Cartesian.tensor_assocRight` |
| [`⊗⊗∘assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L349) | `Cartesian.tensor_assocLeft` |
| [`first-first∘assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L376) | `Cartesian.first_first_assocLeft` |
| [`first-first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L393) | `Cartesian.first_first` |
| [`inAssocˡ′-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L404) | `Cartesian.inAssocLeft'_inverse` |
| [`inAssocʳ′-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L420) | `Cartesian.inAssocRight'_inverse` |
| [`inAssocˡ-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L436) | `Cartesian.inAssocLeft_inverse` |
| [`inAssocʳ-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L447) | `Cartesian.inAssocRight_inverse` |
| [`!⊗!`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L458) | `Cartesian.terminal_tensor` |
| [`[exl⊗exl]∘transpose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L474) | `Cartesian.fstTensor_transpose` |
| [`[exr⊗exr]∘transpose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L491) | `Cartesian.sndTensor_transpose` |
| [`transpose∘▵▵▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L508) | `Cartesian.transpose_pairs` |
| [`transpose∘▵⊗▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L536) | `Cartesian.transpose_tensorPairs` |
| [`transpose∘transpose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L552) | `Cartesian.transpose_transpose` |

## Derived preservation equations

| Pinned declaration | Local recovery |
|---|---|
| [`F-∘³`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L37) | `CartesianPreservation.map_comp3` |
| [`F-∘⁴`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L42) | `CartesianPreservation.map_comp4` |
| [`F-∘⁵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L47) | `CartesianPreservation.map_comp5` |
| [`F-∘⁶`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L53) | `CartesianPreservation.map_comp6` |
| [`F-exl`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L216) | `CartesianPreservation.fst_after_inverse` |
| [`F-exr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L217) | `CartesianPreservation.snd_after_inverse` |
| [`F-!′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L222) | `CartesianPreservation.terminal_after_comparison` |
| [`F-▵′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L225) | `CartesianPreservation.pair_after_comparison` |
| [`F-exl′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L228) | `ProductMapLaws.fst` |
| [`F-exr′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L231) | `ProductMapLaws.snd` |
| [`F-⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L236) | `CartesianPreservation.tensor_preserved` |
| [`F-⊗′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L250) | `CartesianPreservation.tensor_conjugate` |
| [`F-first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L262) | `CartesianPreservation.first_preserved` |
| [`F-first′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L266) | `CartesianPreservation.first_conjugate` |
| [`F-second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L270) | `CartesianPreservation.second_preserved` |
| [`F-second′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L274) | `CartesianPreservation.second_conjugate` |
| [`F-assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L278) | `CartesianPreservation.assocLeft_preserved` |
| [`F-assocˡ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L301) | `CartesianPreservation.assocLeft_conjugate` |
| [`F-assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L312) | `CartesianPreservation.assocRight_preserved` |
| [`F-assocʳ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L347) | `CartesianPreservation.assocRight_conjugate` |

The derived preservation table includes every active derived declaration of
`CategoryH` and `CartesianH`. The primitive fields remain `MapLaws`,
`TerminalMapLaws`, `ProductMapLaws`, and `ComparisonLaws`. The selected local
comparison `hom` points from the interpreted source product to the target
product: it is Felix's `μ⁻¹`; `inv` is `μ`. Thus `ProductMapLaws.fst/snd`
are Felix's primed projection equations, and `fst_after_inverse/snd_after_inverse`
recover the original orientation. The same convention applies to `ε`.

The conjugated tensor, first, second and associator equations require no inverse
laws. The equations with an input inverse comparison additionally require
`ComparisonLaws`. Source category/product laws are absent from all these
preservation theorems. Target laws and the supplied primitive preservation fields
suffice. `map_comp3`–`map_comp6` only require target composition congruence and
`MapLaws`.

## Construction recovery

| Pinned module and declarations | Local recovery and scope |
|---|---|
| `Construct/Product`: `Obj`, `_⇨_`, `category`, `products`, `cartesian`, `equivalent`, `l-category`, `l-cartesian` | `CategoryProduct.ops`, `terminal`, `products`, `equiv`, `congr/laws`, `terminalLaws`, `productCongr/productLaws`. Universal product equations follow from `Cartesian.pair_iff` on these packages. |
| `Construct/Product`: `Hₒ₁/H₁`, `Hₒ₂/H₂`, `catH₁/catH₂` | `CategoryProduct.fst/snd`, `fst_laws/snd_laws`. |
| `Construct/Product`: `pH₁/pH₂`, `spH₁/spH₂`, `cartesianH₁/cartesianH₂` | `fstTerminal/sndTerminal`, `fstProducts/sndProducts`, their `_inverse` and `_laws` theorems. `pair`/`pair_laws` and `pair_fst/pair_snd` additionally recover pairing of interpretations. |
| `Construct/Product`: `traced` | Componentwise selected feedback belongs to [#451](https://github.com/VladimirMarko/conaled/issues/451), which consumes the shared raw product; it is not a category-law assumption. Inactive Boolean/logic proposals belong to #454. |
| `Construct/Squared`: `unsquare`, `Hₒ/H`, `catH` | `Squared.unsquare`, `map_laws`. |
| `Construct/Squared`: `pH`, `spH`, `cartH` | `Squared.terminalMap/productMap`, `_inverse`, `_laws`; the terminal comparison eliminates/inserts a unit and the product comparison shuffles the middle two factors. |
| `Construct/Squared`: `equivalent`, `catL` | `(Squared.unsquare P).induced E`, `Squared.induced_laws`; the relation is explicitly separate from `CategoryProduct.equiv`. |
| `Construct/Arrow`: `Hₒ/H`, `catH`, imported comma operations | `RawMap.id/id_laws`, `RawArrow.Obj/Hom/ops/equiv`, specializing `Comma`. Source category/congruence laws recover comma laws through `Comma.laws/congr`. |
| `Construct/Arrow`: `productsH`, `strongProductsH`, `cartesianH` | `ProductMap.id/id_laws`, `Comparison.id_laws`, consumed by `RawArrow.products/products_laws`. |
| `Construct/Arrow`: `_ᵀ`, `composableᵒ`, `_○_`, `vcomposable`, `_◎_`, `Id`, `idᵀ` | `transpose`, middle-object equality, `compose`, middle-arrow equality after transport, `verticalAlong/verticalEq`, `identityObj`, `identityHom`; `identityMap_laws` checks the embedding. `transpose_transpose` checks recovery. |
| `Construct/Monoid`: `_⇒_`, `un⇒`, `category`, `equivalent`, `lawful-category` | `SetoidMonoid.Ops`, `ops`, `equiv`, `Laws`, `congr/laws`; homs use the carrier directly, so packing/unpacking are identity. Equality-lawful monoids use `ofMonoid`, `toSingleObj/fromSingleObj` and preservation/round-trip theorems. |
| `Instances/CAT`: `CAT`, `cat`, `obj/mor`, `_⤇_`, `mk⤇`, `Fₒ/Fₘ`, `category` | `RawQuiv.Obj = CategoryTheory.Quiv`, `Prefunctor`, and `RawQuiv.ops = ofCategory Quiv`. This uses Mathlib's existing prefunctor identity/composition. |
| `Instances/CAT`: `products`, `cartesian` | `RawQuiv.terminal/products`: terminal quiver has one vertex and one arrow; product quiver uses pairs of vertices and pairs of arrows. |
| `Instances/CAT`: `toHₒ`, `toH`, `it-⤇`, `Functor.catH`, `CartesianFunctor.cartH` | `RawQuiv.ofOps`, `ofRawMap/toRawMap`, both round trips, `FunctorLaws`, `CartesianFunctorLaws`. Raw operations must be supplied separately for the bridge. Functor and structural-comparison composition already use `RawMap.comp_laws`, `ProductMap.comp_laws`, `TerminalMap.comp_laws`. |
| `Instances/Function/Lift`: `lift₀′`, `lift₀`, `lift₁`, `lift₂′`, `lift₂` | `FunctionLift.lift0'/lift0/lift1/lift2'/lift2`; `unary/binary/constant`, `lift0_apply/lift2_map` connect them to lifting and product comparisons. |
| `Instances/Function/Lift`: `Hₒ/H`, `catH`, `pH`, `spH`, `cartH` | `FunctionLift.map`, `map_laws`, `terminal/products`, `_inverse`, `_laws`, with independent `u,v`. |

## Checked consumers and statement review

[Examples.RawConstructions](../../Examples/RawConstructions.lean) exercises the
public constructions. `mixed_laws` transports both the raw-code semantics and
finite-matrix equality through the componentwise product. `mixed_comp` checks
matrix multiplication alongside an unsimplified raw code composition;
`raw_ident_not_collapsed` rejects constructor equality with identity.
`shuffle_value`, `shuffle_not_identity` and `shuffle_recovers` distinguish the
middle-four comparison from an identity comparison. `induced_not_componentwise`
and `components_distinct` prevent identifying the two squared equivalences.

The list monoid checks noncommutative composition order. Its length setoid also
checks a semantic relation that equates distinct raw lists. Arrow consumers use
nonidentity connectors and horizontal arrows, check transpose involution,
object composition, identity embedding and vertical pasting. The empty-arrow
Boolean quiver has no possible category operations, while remaining a valid
`RawQuiv.Obj`. `lift_two_levels` and `lifted_tensor` check universe composition
and generic preservation through nonidentity product comparisons.

The initial missing connections were the generic componentwise product,
operation-only derived terms, and preservation through arbitrary comparisons.
Existing matrix, code, comma and function theories supplied their hypotheses;
the new cases use the shared results. Statement review checked object/hom
universes, composition order, comparison orientation, left versus two-sided
inverse assumptions, and raw equality versus semantic equivalence. No new
axioms or placeholder proofs were introduced. The negative examples concern
specific overly strong identifications; they do not refute the semantic laws.

Focused validation: `direnv exec . taskset -c 2,3 lake build Examples.RawConstructions`.
The final committed candidate still requires isolated candidate acceptance and
independent Standards/Spec review. This report does not claim a full acceptance
receipt. R2 does not close #8: selected trace, restrictions/setoids, computational
witnesses, and inactive monoidal/Boolean proposals retain their separate owners.
