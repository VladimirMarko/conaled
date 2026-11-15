# Independent design assessment for #315

Assessed the prospective freeze `0624161`, reviewed #314 at `3484ce5`, the design question, and the in-progress `InterpretationMaps.lean` on 2026-11-05. This is a mathematical design challenge within the current implementation loop, not Standards/Spec approval. No implementation files were changed and no builds were run. Proof routes below are proposals, not checked Lean results.

The section construction is mathematically credible, but constructing its model does not establish the intended reusable author boundary. The decisive missing ingredient is a retained generated argument with interpretation into a newly admitted model. Restriction of diagrams cannot provide that ingredient. Same-model context isomorphisms also cover a narrower class than arbitrary unequal family presentations. Neither observation refutes the candidate; both identify work that must be explicit before adoption.

## Structural transport and contextual J

The draft strict map has enough structural preservation data for telescope transport. Write `FΓ`, `FA`, `Ft`, `Fσ` for its components, with the necessary metatheoretic casts understood. Construct recursively:

- `Ftel(nil) = nil` and `Ftel(A :: T) = FA :: Ftel(T)`, transporting the recursive base along `F(Γ.A) = FΓ.FA`.
- A canonical equality `cT : F(total T) = total(Ftel T)` and preservation of telescope projection.
- `Ftel(T[σ]) = (Ftel T)[Fσ]`, with equality of the corresponding lifted substitutions after transporting source and target contexts.
- Preservation of `pathContext`, `rootSub`, `rootTail`, `pathTailMap`, `branchMap`, and `reindexBranch`.

Prove preservation of `sectionSub` and `lift` first. The telescope reindex recursion uses only these operations; `rootSub` additionally uses Id and reflexivity. Transport `Telescope.square` by its recursive definition or its appropriate uniqueness characterization. For the dependent branch, prove both its context/type equality and its term equation; equality of a square's outer contexts is insufficient. Host equality proofs can be normalized using Lean proof irrelevance. This does not make object identity proof irrelevant.

The `pair` field is redundant. After the extension cast, `F(pair σ t)` has first projection `Fσ` by `comp` and `weaken`; its generic variable is `Ft` by `subTm` and `mapVariable`. Target `pair_unique` from #314 identifies it with target pairing. This is also the strict comprehension argument in Bezem–Coquand–Dybjer–Escardó, Definition 3. The paper's terminal-map consequence is inapplicable to the present nonterminal empty context. [Primary source, §2](https://arxiv.org/pdf/2012.08370)

Keep signature preservation (`base`, `fiber`) separate from structural transport. Telescope transport does not use these signature assignments. Id/reflexivity preservation is needed for path/root constructions; preservation of the chosen J is a further obligation. This separation need not force a repository-wide record refactor.

After constructing transported motive and branch, the full-map law is precisely

`F(j_M(A,x,T,C,d)) = j_N(FA,Fx,Ftel T,FC,Fbranch d)`

in the canonically compared target family, expressed with the existing `HEq` discipline if desired. This is a legitimate model-builder law for a primitive operation. It must not be replaced by a law assuming transport-composition, certificate preservation, or dependent higher action. Those are derived arguments. The current structural fields alone do not prove this law; substitution stability and beta do not state preservation of another model's chosen J.

For compatible sections, construct telescope evaluation and its total-context comparison before pointwise J. The closure proof for J then uses the full-map law on each diagram arrow. Pointwise beta and substitution follow from component laws plus these telescope/branch comparisons and extensionality of section records. There is no evident mathematical need to restrict tails to length zero or to fixed motives. Identity/composition of full maps require functoriality of the same telescope and branch transport; arbitrary independently chosen transports would leave that proof open.

## Generatedness and admitting new settings

For a diagram `D : I → Models`, compatible sections impose preservation only for arrows present in `I`. A discrete diagram imposes no cross-model uniformity. In the simpler carrier example from #314, a chosen Bool element is compatible with the identity-only diagram, but cannot extend to the same object with negation included. This illustrates the logical gap; it is not a newly constructed automorphism of the full contextual-J model.

For `H : K → I`, restriction `Sec(D) → Sec(D ∘ H)` forgets components and equations. It does not extend a section to a larger diagram. A natural transformation of diagrams whose components are full model maps can induce another map on sections, but requires those whole-model maps. Assigning the primitive signature in a new model does not supply a map from an arbitrary previous ambient model.

Requiring an author to provide compatible sections for every diagram, with restriction naturality, merely moves the universal quantification. Hiding compatibility fields does not establish it. Likewise, existentially erasing the universal annotations from existing `Typed` derivations leaves the underlying author representation unchanged if users still construct those annotated derivations.

A concrete alternative is to retain generated recipes with syntactic indices:

1. Define admissibility judgments over source context, telescope, type, term, substitution, and equality syntax. Keep their indices independent of `Model`. The current raw vocabulary can be reused, but semantic annotation arguments must leave the public judgments. Include the entire frozen contextual-J rule and its branch, with the current distinction between object Id and conversion.
2. Construct interpretation into one arbitrary target with a supplied primitive assignment. Its type may quantify over models; the source judgment indices do not. Use recursive interpretation and equality soundness, including substitution and conversions. Derivation independence, or explicit coherent comparison between derivation-dependent interpretations, is a real obligation. Merely deleting the annotation parameters from `Typed` is not a proof.
3. Prove model-map preservation by induction on the retained recipe, using primitive map laws and the telescope transport above. Equality soundness supplies conversions. Prove that interpretation commutes with source substitution.
4. Define joint interpretation into `Sec(D)` from this interpreter and its preservation theorem, if the diagram model remains useful. The same recipe then interprets in an additional model without changing the authored argument or constructing a map from an old ambient model. Maps, when supplied, give comparison theorems.

This requires a sound interpreter, not a theorem that the source is initial or that every compatible semantic family is generated. Initiality and semantic extraction can remain separate investigations unless required by a selected client. Smart constructors and fixed commands must hide routine derivation and cast work from ordinary authors; a bare raw derivation API would not satisfy the intended author improvement by itself.

The external GAT source distinguishes uniform families over its entire model category from arbitrary families, and constructs syntax before claiming the equivalence with syntactic elements. Its result is not a justification for treating sections of a chosen small diagram as syntax. Its terminal-context assumptions and signature formulation also need adaptation to the frozen fragment. [Bezem–Coquand–Dybjer–Escardó, §§3–4](https://arxiv.org/pdf/2012.08370)

If a fully semantic approach is preferred, it still needs an equally concrete generation mechanism and proof of extension to new interpretations. A model-indexed GADT generated relative to one ambient model only gives transport along maps out of that model. It does not, without a freeness result, meet the new-primitive-assignment requirement.

## Presentation comparisons and equality levels

An actual context isomorphism `f : Δ ≅ Γ` gives reindexing of families and terms, inverse laws, and induced isomorphisms on extensions. For the path/tail comparison canonically induced by this base substitution, `j_sub` supplies the branch compatibility. This is useful and can compare genuinely different contexts.

It does not generally compare distinct families `A` and `B` over the same context. A family comparison requires, for example, an isomorphism `θ : A ≅ B[f]` in the category of display maps over `Δ`. #314's comprehension machinery derives its action on terms by taking a section, composing with the display isomorphism, and recovering the corresponding term. It also derives identity/composition of that action. No equality of family codes follows.

For unequal family presentations, preserving selected intensional Id, reflexivity, and J requires further compatible comparisons or a construction deriving them for the specific presentations. An arbitrary display isomorphism is not already such a comparison. In particular, current `j_sub` covers its canonical base-reindexing diagram; it does not state invariance under every isomorphism of motives or telescopes. A weaker object-identity comparison, where derivable using J, must not be reported as exact preservation of selected data.

Clairambault–Dybjer's pseudo CwF maps make substitution/type and comprehension comparisons explicit and derive pairing preservation; their unit/composition conditions are relevant models for the bookkeeping. Their biequivalence uses extensional identity and democracy, so it does not discharge intensional-J comparison here. [Primary source, §§3.1 and 3.3](https://arxiv.org/html/1112.3456)

The proposed within-model comparison therefore suffices for its advertised **base-reindexing** scope, provided a nontrivial example and branch proof are constructed. To advertise repair of unequal family presentations, extend it with actual display-family isomorphisms and their Id/J discipline, or show that the discriminating substituted-versus-fresh case falls within the narrower canonical scope. A context automorphism unrelated to that failure would not answer the comparison question. A general pseudo-morphism theory between arbitrary settings need not be constructed merely to prove one concrete presentation comparison, but the scope must remain explicit.

Keep three equalities distinct. Host `Eq`/`HEq` compares encoded data and supports casts; judgmental equality licenses the source conversion rules; object `Id` is a family with sections that may retain higher data. A selected dependent certificate is a section, not a host proposition. For `E(p) = Id(v(p),w(p))`, higher action must compare `tr_E(h,η(p))` with `η(p′)` in `E(p′)`. Strict map preservation of the derived construction follows only after Id/J preservation is established. The concrete higher-model interpretation remains #316/#321's separate gate.

## Discriminating completion evidence

Before choosing the diagram route as the author boundary, demonstrate one unchanged generated argument evaluated in a newly added target from its primitive assignment, without a caller-supplied full-model map or final naturality field. Reuse Bool symmetry at the correct signature: adding a distinguished point would remove negation from the admissible maps and change the rejection test.

For the public command problem, compare substitution of the fixed command with reconstruction on substituted arguments, including the actual telescope, motive, and branch. Fixed templates can make both commands instances of one retained recipe, but that identification must be proved. Test both substitutions of the transport value and its dependent certificate. Retain the decoded-equality rejection; an isomorphism of presentations does not imply equality of their records.

External model diagrams do not establish context-varying internal settings. Integrate #319's constructed indexed case or state the precise limitation and ownership. Publish model-builder costs, ordinary-author costs, and host cast costs separately. On the evidence inspected, structural maps are promising reusable work; full J transport, generated interpretation/reuse, and the relevant unequal-presentation comparison remain unestablished. The candidate warrants continued construction, not adoption yet.
