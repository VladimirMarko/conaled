# Dependent coherence: construction routes and author boundaries

Research for [#292](https://github.com/VladimirMarko/conaled/issues/292), under [#289](https://github.com/VladimirMarko/conaled/issues/289). **Investigate a separate semantic layer; retain the current strict model while its author boundary is compared with a replacement.** The checked Type-family construction demonstrates dependent constructor stability and rejects one proposed annotation shortcut. It does not establish a higher dependent model or repair #107. Wholesale migration remains deferred until a candidate preserves the external memo's dependent higher-witness capability and has an explicit interpretation contract.

The [external memo](dependent-coherence-discovery/292-external-memo.md) defines that capability independently of the implementation. Its [exposure log](dependent-coherence-discovery/292-external-source-log.md) and checksum manifest remain byte-for-byte unchanged. Commit `4c0ac58d0c6f71a4de4033166349aa6b2ea03f1b` preserves the freeze before local implementation. Local inspection started from `2525b12052e4c85c57f9050dbf18f7a36ba2ef19`; this candidate incorporates integration revision `d8563a8420196fedff7c875c158d0eeca3403db2`, the review base. The [retained-obligation inventory](dependent-coherence-fixture.md) was written later and pins the old source declarations separately from this experiment.

## What the source theorem requires

Lumsdaine–Warren's Theorem 3.4.1 requires a **full comprehension category**, condition **LF**, and the specified weakly stable constructors. LF asks for finite products and dependent exponentials along display maps for display maps and product projections. It is a categorical representability requirement, not a demand for object-language Π-types. The theorem covers its listed constructors, with the stated stable-class condition for W-types. Section 4.1's extension recipe is a heuristic and excludes rules concluding type equality. Right splitting instead requires coherent pseudo-stability of the whole constructor, including elimination. [Definitions 3.1.1–3.1.3, Theorem 3.4.1, §§2.4 and 4.1](https://arxiv.org/pdf/1411.1736)

The distinction matters here: semantic strictification cannot identify two independently chosen source annotations merely because they denote equivalent objects. Applying the theorem to additional syntax or equations requires an interpretation proof for those judgments. Neither the theorem nor the experiment supplies equality reflection.

## Audit of the local semantics

| Requirement | Current generic `Model` | Concrete groupoid interpretation | Type-family specialization |
|---|---|---|---|
| Context category and chosen reindexing | Strict category/type laws and heterogeneous term laws are fields | Constructed in `GroupoidSoundness.lean` and `SplitFamily.lean` | Functions and precomposition |
| Terminal context, finite products | `empty` is distinguished but has no terminal universal property; finite products do not follow | Concrete empty groupoid available; this code does not package the required full LF argument | Unit, binary products of types |
| Full comprehension | Pairing/projection laws, but no chosen category of family morphisms or full comprehension functor | Grothendieck family comprehension; full comprehension for a specified morphism notion is not proved here | Maps over Γ correspond to fiberwise functions; pairing representation checked |
| LF dependent exponentials | Not fields and not consequences of this interface | Not constructed or verified by this audit; choose fiber morphisms and prove the needed adjoints | Pointwise dependent functions; section representation and its naturality checked |
| Identity formation, elimination, stability | `Model` adds J over arbitrary finite dependent tails, β and substitution laws | Concrete contextual J, β and substitution already proved | Native equality used only for the bounded transport argument; no higher identity model |
| Connection to generated judgments | Existing recursive interpretation and annotation agreement | Existing soundness instantiated at the full model | No interpretation of generated judgments added |

The first column has an actual counterexample, not just a missing field. `MissingTerminal.model` in [the boundary examples](../../Examples/LocalUniversesBoundary.lean) implements the **entire existing `Model`** with contexts Bool and substitutions `PLift (Δ = Γ)`. Each family and section is Unit; extension preserves the context. `no_terminal` proves that no context receives even one substitution from every context. Thus the interface does not entail LF's finite products. Generated contexts reachable from `empty` stay in the false component; this counterexample does not rule out a terminal object in that restricted subcategory.

The groupoid column makes a different claim. Families are strict functors into groupoids, context extension is their Grothendieck construction, and sections include coherence on arrows. Whether the required comprehension is full depends on the chosen family morphisms, for example strict transformations versus suitable maps of total groupoids over the base. This audit has not constructed that category or LF exponentials. **No failure of LF for the concrete groupoid setting is proved.** Missing categorical proofs are owned residual work. The existing concrete model already has strict reindexing and stable contextual J; adding local universes would not improve those established laws by itself.

## A constructed dependent case

[SquareKit.LocalUniverses](../../SquareKit/LocalUniverses.lean) is an experimental specialization of the local-universe idea to the existing split families in `Dependent.lean`. A family over Γ stores `(V,E,a)` with `E : V → Type` and `a : Γ → V`. Decoding is `γ ↦ E(a γ)`; reindexing retains V and E and composes a. This is a local parameter object, not an object-language universe classifying every type.

For A represented by `(V,E,a)` and B over `Σ γ, E(a γ)` represented by `(W,F,b)`, the dependent sum is constructed over

```text
S = Σ v:V, (E(v) → W)
G(v,f) = Σ x:E(v), F(f x)
name(γ) = (a γ, x ↦ b(γ,x)).
```

Precomposition of this name agrees with rebuilding it after substitution, including the lifted substitution into B. `sigma_reindex` checks that equation at the presentation level. `decode_sigma` identifies its meaning with the existing native dependent sum. `pair_twice` applies the native pairing substitution theorem to the composite of two arbitrary substitutions. No stability theorem is hidden as an input field.

The underlying Type model qualifies on paper: its family category uses fiberwise functions, which are in bijection with maps of dependent sums over the base, proving fullness. For display map `Σ x:X,A(x) → X` and B over its domain, the representing object has fiber `Π a:A(x),B(x,a)`. Sections over any `σ:W→X` correspond to sections of B over the pulled-back display map. `displayCurry` constructs this bijection and `displayCurry_natural` checks substitution naturality. Product projections are the constant-family instance. Unit and products give finite products. These constructions establish the required Type case without assuming LF as a record field. The Lean module checks the displayed representation and Σ construction; it does not formalize the complete categorical local-universes theorem or every transferred constructor.

[Examples.LocalUniverses](../../Examples/LocalUniverses.lean) uses the existing family `AS n = Fin(n+1)` and dependent tail `BS(n,i) = Fin(i.val+1)`. Its pair chooses the last index and its dependent witness. Substitution first by `n ↦ n+1`, then by `n ↦ 2*n`, gives

```text
Σ i:Fin(2*n+2), Fin(i.val+1).
```

At n=2 both selected values are 5, independently calculated from `2*2+1`. Both projections are checked through `pair_twice`; this is not a constant second fiber disguised as a dependent example.

The same file also specializes the memo's transport argument:

```text
v = move q (move p u)
η : v = move (p.trans q) u
w = (v, η).
```

`move_comp` is proved by equality induction. The witness family depends on v and is lifted from Prop to Type. `substituteFirst` sets y=x and p to a loop; `substituteSecond` sets z=x and q to a second loop. `Transport.routes_agree` checks the whole pair under both substitutions via `pair_twice` and decoding into the original native family semantics. Thus the positive result compares the same native argument through the original and delayed-family routes. It is extensional: Lean's native identity proofs are proof irrelevant. It omits p′, h and dependent action on h, and cannot satisfy the memo's nontrivial monodromy or higher-identity observations.

## Generated source and higher witnesses

The old generated transport proof is separately retained under two arbitrary source substitutions by `Source.transport_twice`, using `TmEqDeriv.subComp`. `Source.dependent_tail_twice` composes the existing generated dependent substitution conversion twice. These maintain the current annotation discipline. They do not claim to translate the new Type-family proof into generated syntax, or identify a fixed substituted command with a freshly reconstructed command. The historical failure remains pinned in the [fixture](dependent-coherence-fixture.md).

`PresentationFailure.decoded_equal` and `presentation_ne` give a checked rejection test: the constant Nat family over Bool, represented by reindexing a family named by Unit, decodes exactly like a fresh family named by Bool. Equality of their records would imply Unit=Bool, contradicting subsingletonness. Decoding therefore does not reflect presentation equality. This refutes an automatic annotation-equality shortcut. A translation with explicit comparisons or a different author boundary remains possible.

The retained witness tests are independent of that Type example. `Witnesses.source_transport` interprets the existing generated proof in the C4 action on ZMod 2, where the generator swaps 0 and 1 and the family is not isomorphic to a constant family. `higherTwice` substitutes into the existing algebraic two-loop expression twice; its Boolean and labeled interpretations agree and retain observation 1. The native-identity rejection theorem proves that no observation through `(true = true)` preserves every labeled 2-cell's observation. These checks rule out collapsing the selected higher data to native equality. The algebraic fragment does not contain arbitrary dependent families or contextual J, so combining these tests is **not** a construction of the memo's dependent higher model.

The exact remaining author capability is the memo's `apd_η(h)` under both dependent substitutions, together with the path-family observation `β⁻¹ · ap_T(h) · β = h` in a model admitting nontrivial second identity. A model with discrete identity groupoids cannot supply that nontrivial second identity. A higher model must separately interpret the admitted motives and J computation/stability laws. On paper, any such model and a sound interpretation of the specified intensional fragment interpret the memo's identity-induction derivation and substitution laws. This conditional argument is not a new model existence or initiality proof.

## Repair and replacement are separate decisions

| Author boundary | What it could remove | Proof still owed | Assessment |
|---|---|---|---|
| Current derived helpers plus comparisons of context presentations | Manual casts at repeated command call sites | Factorization of endpoint substitutions, telescope/motive/branch comparison, then general source associativity | Existing #107 alternative; no completion claim |
| Fixed open source templates with typed arguments | Fresh reconstruction at each application | Dependent argument environments and correspondence to named operations | Promising #107 experiment; fixed-term composition supports its mechanism but does not prove the whole design |
| A judgment interpretation boundary independent of model construction | Model-parametric annotation equalities leaking into ordinary author steps | Rules/derivations for the chosen fragment, interpretation of all admitted judgments and their equality, selected witness preservation | Investigate under #289/#36/#235; may replace contexts or syntax rather than adapt immediately |

The model-construction choice is independent:

| Route | Mathematical opportunity | Admission cost and decisive test |
|---|---|---|
| Local universes | Derive strict constructor stability from qualifying weak semantic structure | Prove full comprehension, LF and required weak stability; test eliminators and any extra type equations |
| Direct strict CwF or natural model | Supply strict dependent structure directly, as the existing groupoid model already does | Representability alone does not supply identity elimination or judgment interpretation; establish each structure and interpretation theorem |
| A chosen classifying universe with chosen pullbacks | Build contextual objects from represented families | Prove coverage and constructor closure/computation for the selected universe; an unrepresented needed family rejects the choice |
| Right splitting | Strictify coherently pseudo-stable structure | Supply coherent choices for the complete eliminator data; weak existence alone is insufficient |

The direct natural-model account needs identity/reflexivity maps and the lifting structure for elimination, beyond representability. Its general construction theorem is related to local universes, so changing that interface is not an independent strictification proof. [Awodey, Proposition 20 and Remark 34](https://arxiv.org/pdf/1406.3219) The fixed-universe construction requires terminal context, a selected universe map and chosen pullbacks; constructor structures are additional data. Its higher simplicial realization has further size assumptions. [Kapulkin–Lumsdaine, Proposition 1.3.3 and Theorem 1.4.15](https://arxiv.org/pdf/1211.2851) The extensional CwF/LCCC biequivalence does not justify replacing intensional identity with native equality. [Clairambault–Dybjer, §§2–5](https://arxiv.org/pdf/1112.3456)

A replacement's lack of an immediate adapter into `Typed` is an integration cost, not a mathematical refutation. Conversely, claiming that replacement repairs existing generated judgments requires a translation preserving contexts, raw judgments, semantic type annotations or specified comparisons, term judgments, conversion and identity witnesses. Strict substitution in a semantic interface alone proves none of that correspondence. A migration must also account for the existing source soundness clients.

## Statement review and validation scope

The new definitions and claims were reviewed against these intended meanings:

- `Family` quantifies over same-universe contexts and parameter types. It represents arbitrary Type-valued families via `present`; it does not provide an object-language classifier. Its reindexing laws are literal record equality. Decoding equalities and term equalities are metatheoretic equality.
- `comprehensionEquiv` quantifies over all maps from an arbitrary Δ, returning a base map and its dependent section. `displayCurry` quantifies over arbitrary A, B and σ, with both inverses and naturality. The explicit functions construct the claimed representation; they do not assume an adjoint or the desired conclusion.
- The Σ constructor allows an arbitrary function from each first fiber to second-family parameters. The lifted substitution changes the second family. The two-substitution result includes both dependent components and their type; the Fin example checks expected projections through that result.
- The native transport witness has its actual dependent equality type and both substitutions are well typed. Its universes are explicit through `ULift (PLift ...)`. Proof irrelevance limits this example; no higher identity claim is extracted from it.
- `MissingTerminal.model` supplies J for **every** family A, point x, finite tail length n, telescope T over the path context, motive C over T's total context, and branch d over the root pullback admitted by the unmodified `Model`. All such families/sections are Unit, so returning Unit satisfies β and substitution, including the actual canonical path-tail map and reindexed branch. The restricted family collection is allowed by the interface; the model definition does not weaken or omit arbitrary-motive fields. Its distinct Bool contexts make the terminal conclusion fail. It is a counterexample to an interface entailment, not a claim about useful higher semantics.
- The source claims quantify over arbitrary composable *generated* substitutions into the precise retained contexts. Their conversions arise from existing derivations; no semantic-equality reflection is used. The higher guards reuse the original witness-sensitive interpretations and explicitly expose their algebraic-fragment scope.

Focused validation: `direnv exec . lake build Examples.LocalUniversesBoundary` passed, compiling all three new modules. The public entrypoint imports that boundary module, so all new declarations enter the repository build and exhaustive audit. Candidate acceptance uses `direnv exec . ./check.sh --candidate HEAD`, followed by `--verify-candidate HEAD`; the acceptance receipt and independent review results belong to the implementation handoff. No toolchain or checker changes were made.

Implementation work here constructs semantic operations and regression examples. No independent proof author was timed. There is no measured author-effort saving and no implemented extractor. Model builders prove the representation and stability laws once; authors in this bounded Type route supply their family parameters, terms and substitutions. The generated route still requires the annotation alignments documented by #107. Reducing this recurring burden in a higher model remains an adoption criterion rather than an observed result.

## Decisions and owned residual work

| Decision | Owner and next evidence |
|---|---|
| Adopt the bounded construction as research evidence, not the default author interface | #292 retains positive, source and rejection cases with this report |
| Investigate a replacement judgment boundary independently of the model-construction route | #289 with #36/#235: specify the admitted dependent fragment and prove its interpretation/equality contract; compare fixed templates and presentation comparisons without presuming the old encoding |
| Investigate the actual groupoid LF/full-comprehension package if weak-model strictification is needed | #289: choose family morphisms, construct full comprehension and the required dependent exponentials; absence of these proofs is not failure of the setting |
| Preserve the higher-dependent author test as an admission condition | #289 coordinated with #297: supply a higher model, dependent J and the memo's two-substitution/h observation; algebraic 2-loop tests alone do not close it |
| Retain the current strict groupoid model and source clients pending evidence | #107 remains paused with its existing repair scope; #108 stays gated and no trial theorem has been prepared |
| Reject automatic source-annotation repair from strict semantic reindexing or decoded equality | #292 counterexamples and the unchanged #107 failure record establish the limits |
| Defer wholesale migration | #289/#36/#235 need capability evidence, an integration/retirement plan and ordinary independent review; an immediate adapter is not a prerequisite for researching the replacement |
