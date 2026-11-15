# Reusing a six-functor argument

Research deliverable for [#557](https://github.com/VladimirMarko/conaled/issues/557),
2026-11-15. This report develops paper-level arguments and proposed interfaces.
It does not add Lean declarations, construct the motivic categories in Lean, or
measure author productivity. The [initial assessment](six-functor-language.md)
records the wider motivation; [#555](https://github.com/VladimirMarko/conaled/issues/555)
retains the full application, including motivic realizations and higher coherence.

The result is a reusable proper Künneth argument, its interpretations in derived
sheaves and motivic stable homotopy, and transport of its specified isomorphism
from real to complex schemes. An internal-Hom argument tests the exceptional
operations. These calculations justify an ordinary categorical checkpoint and a
separate investigation of higher interpretations, without making the checkpoint
the language's expressive boundary.

## Source contract and observation level

The primary references used below are:

- **S:** Scholze, [*Six-Functor Formalisms*, October 2025 revision](https://people.mpim-bonn.mpg.de/scholze/SixFunctors.pdf).
  Lecture I, Theorems 1.1–1.3 and the calculation on printed pp. 7–8 supply the
  sheaf example and argument. Definitions 2.3–2.5, pp. 16–17, give the
  correspondence presentation; Definition/Proposition 3.2, p. 18, describes its
  simplices. Lecture IV, Theorem 4.6, is a construction result, not a consequence
  of naming the functors. Lecture XI supplies wider motivic context.
- **CD:** Cisinski–Déglise, [*Triangulated categories of mixed motives*, arXiv v4, June 2019](https://arxiv.org/pdf/0912.2110v4).
  Example 1.4.3, p. 28, and Example 2.4.48, p. 77, identify `SH` as a motivic
  category. Theorem 2.4.50(1),(2),(4),(5), pp. 78–79, supplies exceptional
  adjunctions, proper comparison, base change and projection/Hom formulas.
  Sections 1.1.15–16, pp. 8–9, and 1.1.31–32, p. 12, specify exchange maps and
  their compatibilities. Definition 1.4.2 and §1.3.25 explain the monoidal fibers.

Page numbers are printed numbers, not PDF indices. CD is used as a primary
source for its own six-operation theorem, including its explicit `SH` example.
It traces the construction to Ayoub. The issue's
[Ayoub I PDF](https://www.numdam.org/item/AST_2007__314__R1_0.pdf)
exceeded the browser's document-size limit; the
[Ayoub II catalogue](https://numdam.org/item/AST_2007__315__1_0/)
was accessible. This report does not claim independent verification of Ayoub's
long construction or infer a theorem from that catalogue. CD's theorem gives
the applicability evidence needed here.

Our observation level is objects, morphisms, specified natural isomorphisms,
and equality of their composites in ordinary categories, including homotopy
categories. A higher enhancement would retain spaces of transformations and
homotopies between them. The paper calculations below do not establish that
stronger preservation theorem.

## One argument and its exact requirements

Let `C` have the pullbacks in question. Fix a class `P` of proper maps, containing
identities and closed under composition and pullback. For each `T`, let `D(T)`
be a symmetric monoidal category. Supply a contravariant pseudofunctor `D*` with
strong symmetric monoidal transition functors, and adjunctions
`f* : D(T) ⇄ D(U) : f_*` for `f : U → T`.
Functor composition below is mathematical right-to-left composition.

For a cartesian square

```text
W --q--> Y
|        |
p        g
|        |
v        v
X --f--> S
```

use the canonical mate `BC : f* g_* → p_* q*`. Its transpose under `p* ⊣ p_*`
is the composite `p* f* g_* ≅ q* g* g_* → q*`, ending in the counit of `g`.
Require this map invertible when `g ∈ P`. For `h : U → T` in `P`, require the
canonical projection map

\[
 \operatorname{PF}_h(M,N):h_*M\otimes N\longrightarrow h_*(M\otimes h^*N)
\]

to be invertible for **all** `M ∈ D(U)` and `N ∈ D(T)`. Its transpose is the
monoidal comparison followed by `ε_h(M) ⊗ id`. Use the induced right-adjoint
composition isomorphisms, not unrelated choices. Neither cartesian squares
alone nor the invertibility of an unmated comparison proves these hypotheses.

Take `f : X → S` and `g : Y → S` proper, `W = X ×_S Y`, `h = f p = g q`,
`A ∈ D(X)`, and `B ∈ D(Y)`. Put `A ⊠_S B = p* A ⊗ q* B ∈ D(W)`. Here is the
complete derivation, with every line in `D(S)`:

\[
\begin{aligned}
f_*A\otimes g_*B
&\xrightarrow[\sim]{\operatorname{PF}_f}
 f_*(A\otimes f^*g_*B)\\
&\xrightarrow[\sim]{f_*(1\otimes\operatorname{BC})}
 f_*(A\otimes p_*q^*B)\\
&\xrightarrow[\sim]{f_*(\text{symmetry, PF}_p,\text{symmetry})}
 f_*p_*(p^*A\otimes q^*B)\\
&\xrightarrow[\sim]{\text{composition}}
 h_*(A\boxtimes_S B).
\end{aligned}
\tag{K}
\]

The third line uses `p ∈ P`, obtained by pulling back `g`, with coefficient
objects `q*B ∈ D(W)` and `A ∈ D(X)`. No dualizability, orientation, purity,
constructibility, boundedness, or field of coefficients enters this abstract
proof. Those restrictions could enter a realization of its laws. We deliberately
retain both properness assumptions to match the selected sourced argument;
this is a sufficient contract, not a claim of weakest hypotheses.

Define `K_S(A,B)` to be this composite. Expanding PF and BC and cancelling the
unit/counit pairs gives its useful alternative characterization: under `h* ⊣ h_*`
it is the map

\[
 h^*(f_*A\otimes g_*B)
 \simeq p^*f^*f_*A\otimes q^*g^*g_*B
 \xrightarrow{p^*\epsilon_f\otimes q^*\epsilon_g}
 p^*A\otimes q^*B. \tag{E}
\]

This is also a direct paper proof of the characterization: transpose the first
line of (K), substitute the defining transpose of BC in the second, transpose
the PF for `p`, and apply the triangle identities. The remaining factors are
exactly the two counits in (E). Naturality follows from naturality of those
counits and monoidal structure maps. This identifies a specified isomorphism,
not just existence of some isomorphism between the endpoints.

The calculation generalizes S's absolute argument to a base `S`. It uses only
pullback, proper pushforward, tensor, and adjunction/coherence data. Internal
Hom, exceptional pullback, and exceptional pushforward for nonproper maps are
not tested by (K).

## Two interpretations

| Interpretation | Domain and coefficients | Discharge of (K) |
|---|---|---|
| Derived sheaves | Finite-dimensional locally compact Hausdorff spaces that are locally closed subsets of some Euclidean space; continuous maps; `D(T) = D(Ab(T))`, with derived tensor over `Z`. Use compact `X,Y` and `S = point`. | S, Theorems 1.1 and 1.3, supply proper BC and PF for arbitrary objects of these derived categories. Pullback is symmetric monoidal. (K) gives `RΓ(X,A) ⊗ᴸ_Z RΓ(Y,B) ≅ RΓ(X×Y,A⊠B)`. |
| Motivic stable homotopy | Restrict to separated finite-type schemes over `R` (or over `C`), hence noetherian of finite dimension. `D(T)=SH(T)`; tensor is motivic smash, unit the motivic sphere. No rationalization or orientation is imposed. `f,g` are proper. | CD's `SH` example supplies the premotivic structure. Theorem 2.4.50 gives BC and PF for `!`; its proper comparison `f_! ≅ f_*` gives exactly the required laws. (K) is an isomorphism of motivic spectra in the homotopy category `SH(S)`. |

Thus the same proof has two interpretations, with different base geometries and
coefficients. The motivic conclusion is not an assertion about singular
cohomology or tensoring ordinary cohomology groups. Taking cohomology groups of
(K) need not produce an underived tensor formula; the derived tensor already
retains the Tor information. The sphere in `SH` is not silently replaced by an
Eilenberg–MacLane object.

## Transport along a concrete connection

Choose `u : S' = Spec(C) → S = Spec(R)`. For each separated finite-type
`R`-scheme `T`, put `T' = T ×_S S'` and let `u_T : T' → T`. The base functor
is `T ↦ T'`, and the fiber maps are

\[
 F_T=u_T^*:SH(T)\longrightarrow SH(T').
\]

This is a nonidentity change of setting. For example, `Spec(C)` viewed over `R`
becomes `Spec(C ⊗_R C) ≅ Spec(C × C)` after this extension, using the two complex
embeddings over `R`. The route is motivic-to-motivic; no connection to the first
row of the table is asserted.

Here is the preservation contract and its discharge, restricted to the fragment
actually used:

| Required comparison | Evidence and scope |
|---|---|
| `F_T(M⊗N) ≅ F_TM⊗F_TN`, `F_T(1) ≅ 1` | Strong monoidal pullback in the premotivic structure, CD §1.3.25 and Definition 1.4.2. |
| `F_U v* ≅ v'* F_T` for `v:U→T` | Pseudofunctor composition and the cartesian square defining `v'`; retains the actual pullback cone and its comparison. |
| `β_v: F_T v_* ≅ v'_* F_U` for proper `v` | Proper BC, obtained from CD Theorem 2.4.50(2),(4). This is the canonical mate, with counit compatibility. |
| Compatibility for identities, pasted squares and PF | CD §§1.1.15–16 and 1.1.31–32 give the exchange construction and coherence. At the observation level here these also follow by expanding the mates: the triangle identities cancel adjacent unit/counit factors. |
| Proper witnesses and `W' ≅ X' ×_{S'} Y'` | Base extension preserves proper maps and pullback cones. These are geometric inputs, separate from the coefficient functors. |

For clarity, the counit compatibility just used says that the following
composite equals `F_U ε_v(M)` after the pullback composition identification:

\[
 v'^*F_Tv_*M\xrightarrow{v'^*\beta_v}
 v'^*v'_*F_UM\xrightarrow{\epsilon_{v'}}F_UM.
\tag{C}
\]

This equality is the defining adjunction property of the base-change mate,
so it does not require a new, independently chosen coherence axiom. Pasting
squares gives the corresponding equation for composites by substituting (C)
and the composite-adjunction counit. This supplies the coherence consumed in
transport, rather than assuming that any family of isomorphisms suffices.

Write `A'=F_XA`, `B'=F_YB`, and `L=f_*A⊗g_*B`, `R=h_*(A⊠B)`. There are
specified endpoint comparisons

\[
\begin{split}
\lambda &: F_SL\xrightarrow{\sim}f'_*A'\otimes g'_*B',\\
\rho &: F_SR\xrightarrow{\sim}h'_*(A'\boxtimes_{S'}B').
\end{split}
\]

Construct `λ` from monoidality and `β_f,β_g`; construct `ρ` from `β_h`, pullback
composition and monoidality. Apply the functor `F_S` to the source proof and
conjugate its conclusion:

\[
 \rho\circ F_S(K_S(A,B))\circ\lambda^{-1}
 =K_{S'}(A',B'). \tag{T}
\]

To prove the equality, transpose both sides by `h'^* ⊣ h'_*`. Use (E) on the
left. Monoidality moves `F` through its tensor, and (C) replaces each transported
counit with the target counit. The result is exactly (E) for `f',g'`. The
adjunction bijection is injective, proving (T). A functor preserves inverse
identities, so `F_S(K_S^{-1})` conjugates to an inverse for the target map.
This transports the morphism, its inverse, their equations and its naturality
in `A,B`; it is more than repeating (K) in a second model.

This paper proof specializes the cited preservation laws to the concrete field
extension. It retains no claim of reflection, descent of arbitrary complex
objects to real ones, or preservation of unobserved higher homotopies. Nor does
it prove arbitrary pullback commutes with all right adjoints or internal Homs.
Those would be different contracts. The full-interface transport extension is
an owned requirement below, not a conclusion of the proper fragment.

## Exceptional operations and internal Hom

A second paper calculation tests operations absent from (K). In `SH` on the
same scheme domain let `f:X→S` be separated of finite type, without assuming
properness, and let `A∈SH(X)`, `B∈SH(S)`. CD Theorem 2.4.50(5) gives the
internal-Hom formula. Its adjunction proof can be reconstructed as follows.
For arbitrary `T∈SH(S)`, write `[U,V]` for morphisms and `Hom` for internal Hom:

\[
\begin{aligned}
[T,\operatorname{Hom}_S(f_!A,B)]
&\cong[T\otimes f_!A,B]\\
&\cong[f_!(f^*T\otimes A),B]\\
&\cong[f^*T\otimes A,f^!B]\\
&\cong[f^*T,\operatorname{Hom}_X(A,f^!B)]\\
&\cong[T,f_*\operatorname{Hom}_X(A,f^!B)].
\end{aligned}
\]

Closedness gives the first and fourth bijections; PF and symmetry give the
second; the exceptional and ordinary adjunctions give the third and fifth.
Naturality in `T` and Yoneda give the specified isomorphism:

\[
 \operatorname{Hom}_S(f_!A,B)
 \simeq f_*\operatorname{Hom}_X(A,f^!B). \tag{H}
\]

This uses all six operations in one derivation. No biduality theorem or
constructibility hypothesis is needed for (H). A Verdier biduality assertion
would require further hypotheses and is not inferred from closedness.
For a concrete nonproper shape take the open immersion
`A¹_R \ {0} → A¹_R`; (H) now uses exceptional pushforward outside the proper
fragment. This is a paper specialization, not an implemented motivic example.

## Encoding and the full capability requirement

A proposed ordinary presentation separates indexed symmetric monoidal fibers,
chosen adjunctions, admissibility predicates, and invertibility of canonical
mates. It can express (K), (H), (T), and their naturality with ordinary functors,
natural transformations and equations. Replacing specified comparisons by mere
existence of isomorphic objects would lose the conclusion of (T).

In a correspondence presentation, assign `X ←a W →b Y` to `b_! a*`. Compose it
with `Y ←c V →d Z` using `P=W×_Y V` and projections `r:P→W`, `s:P→V`.
The semantic composite `d_! c* b_! a*` becomes
`d_! s_! r* a* ≅ (d s)_! (a r)*` by BC and composition. Thus BC is the
comparison needed to interpret composition itself. Tensor requires compatible
external products and diagonals. S's Definitions 2.3–2.5 package this in a lax
symmetric monoidal functor `Corr(C,E) → Cat∞`, with right adjoints to obtain
six operations. For the full proposal require `E` closed under composition,
pullback and diagonals, containing isomorphisms.

This packaging moves repeated diagrams into the semantics. It does not build
the functor, prove its extension exists, construct adjoints, or check an
infinite collection of coherences by writing a short type. For three spans,
associativity compares two iterated pullbacks; for further compositions its
compatibilities must persist. An ordinary bicategory can retain associators,
unitors and their equations. A homotopy category forgets homotopies between
those witnesses. Neither automatically provides the higher functor.

| Capability | Evidence in this report | Remaining full-interface obligation |
|---|---|---|
| Indexed `f* ⊣ f_*`, tensor and proper BC/PF | (K), both interpretations, and (T) | Higher naturality of these comparisons. |
| `f_! ⊣ f^!` on admissible nonproper maps | (H) with an open immersion | Construct the operations and their coherently composed units/counits in an implementation. |
| Closed fibers and internal Hom | (H) with arbitrary coefficients | Retain variance, evaluation and currying under interpretation; do not infer Hom preservation from strong monoidality. |
| Comparisons between composite functors | (E), (C), (T) and span composition | Higher transformations and coherent pasting beyond equations of ordinary natural transformations. |
| Purity, twists, localization and duality | No new derivation here | Scoped motivic library work with exact geometric and coefficient hypotheses; these are not axioms of every client. |
| Full maps of six-functor models | Proper fragment of real-to-complex base extension | Determine admissible exceptional/Hom preservation and higher witnesses for a selected extension; arbitrary maps need not preserve every operation. |

The first row is not evidence that the whole table is implemented or that all
six-functor arguments are expressible in the eventual source language.

## Proposed author expressions and generated obligations

The following is design notation, not accepted Lean syntax or an implemented
parser. `≈` denotes a specified isomorphism here, not definitional equality.

```text
argument relativeKunneth in D requires ProperProjectionBaseChange:
  given proper f : X → S, proper g : Y → S
  given A : D(X), B : D(Y)
  let (W, p, q, square) := pullback(f, g)
  show push f A ⊗ push g B ≈ push (f ∘ p) (pull p A ⊗ pull q B)
  calc
    ... ≈ push f (A ⊗ pull f (push g B))        by projection f
    ... ≈ push f (A ⊗ push p (pull q B))       by base_change square g
    ... ≈ push f (push p (pull p A ⊗ pull q B)) by projection p
    ... ≈ push (f ∘ p) (pull p A ⊗ pull q B)   by compose_push

interpret relativeKunneth in DerivedSheavesZ
interpret relativeKunneth in MotivicSH
transport relativeKunneth along BaseExtension(R → C)
  preserving ProperProjectionBaseChange

argument exceptionalHom in D requires ClosedExceptionalProjection:
  given admissible f : X → S, A : D(X), B : D(S)
  show internalHom (push! f A) B ≈ push f (internalHom A (pull! f B))
  by yoneda T; closed; projection f; adjoint! f; closed; adjoint f
```

Routine authors supply the geometry, coefficient objects, intended conclusion
and the mathematical steps. The elaborator must infer each fiber, insert
associators and symmetric monoidal comparisons, track the cartesian witness,
and request invertibility only at the actual inverse use. For example,
`base_change square g` produces a term of
`Iso (pull f (push g B)) (push p (pull q B))` in `D(X)` and must discharge
`Proper g`; it must not manufacture that evidence merely because `square` is
cartesian. `projection p` must derive properness from the base-change witness.
An error should name the missing PF instance and its coefficient objects.

Model builders supply the indexed category, adjunctions, canonical exchange
construction, theorem-backed admissibility rules, and their coherence. The
transport builder additionally supplies the base functor, fiber functors,
comparison transformations and their preservation proofs. Equation (T) is a
test for those proofs. A library can derive compatibility of canonical mates
once, but cannot infer the geometric BC theorem from the names of operations.
Authors should reuse the installed model and route without restating these laws.

Source equality is part of the contract. In this checkpoint, equality of arrows
is a proposition and isomorphisms are data with inverses. In a higher source,
a path between transformations and a path between such paths may be observable
data. Storing those paths as proof-irrelevant propositions would change the
contract. Likewise, the pullback cone, comparison isomorphism, chosen adjunction
and dependent coefficient objects must survive transport; `W` is not identified
with `W'` by an unchecked cast. A source judgment `A : D(X)` translates to
`F_X A : D(X')`, and a term witnessing an isomorphism translates with its inverse
and inverse laws. The proof of (T) accounts for the endpoint conversions.

An implementation should expose universe parameters for base objects, fibers,
hom types and the ambient category of categories. For these scheme examples one
can work in chosen universes and their enlargements. Large `SH(T)` and derived
categories must not be declared small in the same universe as all their objects;
localizations and presentability need explicit size treatment. This is a semantic
obligation, not a reason to force a different kernel or assume resizing.

## Local evidence and implementation choices

Local evidence was checked against base commit
`c214fb0720ffc998951255a7e4b5f2e80a299186`, with Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` from `lake-manifest.json`.
The existing [geometric morphism](../../SquareKit/Internal/GeometricMorphism.lean)
interface supplies an ordinary inverse/direct-image adjunction with finite-limit
preservation. [DependentBaseChange](../../SquareKit/DependentBaseChange.lean)
constructs comparisons from `IsPullback`, including evaluation and currying
laws. [AdjointComparison](../../SquareKit/AdjointComparison.lean) handles changes
of chosen adjoints. Their slice and witness contracts are useful native clients;
none supplies motivic smash or exceptional pushforward.

Mathlib's pinned
[mates](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Adjunction/Mates.lean)
provide `mateEquiv_vcomp`, `mateEquiv_hcomp`, and `mateEquiv_square`.
Ordinary categories, monoidal categories, adjunctions, natural isomorphisms,
Yoneda and universe parameters are existing representational tools for the
paper checkpoint. This does not assert that a complete compatible six-functor
package or either realization is already present in Mathlib.

Constructing motivic homotopy categories, verifying their exceptional operations,
and proving the geometric applicability theorems are mathematical library work.
A higher encoding additionally needs a chosen representation of higher categories,
functors, adjunctions and coherent transformations with a sound interpretation.
Which source judgments should remain intensional, how much coherence can be
generated, and how models of different dimensions share a surface remain language
design questions. Missing implementations are not mathematical impossibility
results and do not establish a need for HoTT or a new kernel.

The bounded mates work in [#556](https://github.com/VladimirMarko/conaled/issues/556)
can supply reusable ordinary comparison proofs. Its acceptance does not supply
the motivic construction or the higher interpretation. A wider framework must
recover existing slice projection/evaluation contracts under their current
assumptions, including the
[noninvertible-mate control](../../Examples/IndexedWitnessAdjunctions.lean).
Migrating those clients should not force them to provide unrelated exceptional
operations.

## Decisions and schedulable handoffs

These are proposed bounded follow-ups owned by the named umbrella issues, for
tracker scheduling by the coordinator. They are not claims that child tickets
have already been created. None closes the full requirements of #555.

| Assessment | Follow-up and scope | Owner and acceptance evidence |
|---|---|---|
| **Adopt** | Use (K), (H), (T) as separate mathematical benchmarks, with canonical maps and sufficient hypotheses frozen as above. | [#555](https://github.com/VladimirMarko/conaled/issues/555). Preserve both interpretation and transport acceptance; preserve the higher residuals. |
| **Investigate** | Implement the ordinary proper Künneth proof and its canonical-map characterization from supplied indexed laws. Reuse mates rather than recoding #556. | [#290](https://github.com/VladimirMarko/conaled/issues/290), coordinated with [#235](https://github.com/VladimirMarko/conaled/issues/235). Checked abstract theorem, two explicit small models, and a nonidentity route proving the analogue of (T); do not call small models motivic realizations. |
| **Investigate** | Compare an ordinary indexed interface with a higher correspondence encoding on the same (K)/(H) contracts. | [#289](https://github.com/VladimirMarko/conaled/issues/289) with [#36](https://github.com/VladimirMarko/conaled/issues/36). State source equality, universes and retained higher witnesses; show which coherence is constructed and which supplied; recover native slice observations. |
| **Investigate** | Build a staged motivic-library plan from the cited `SH` theorem, then select one checked construction milestone. | #555 with #36. Dependency inventory for schemes, motivic localization/stabilization, monoidal structure, exceptional adjoints, BC/PF; no opaque assumptions presented as constructed models. |
| **Investigate** | Extend the real-to-complex route to a stated exceptional/Hom fragment and higher observations. Separately assess a Betti route if a motivic-to-topological connection is desired. | #555 with #290. Exact comparison transformations, hypotheses, canonical compatibility and a transported (H) or duality conclusion; distinguish noninvertible comparison from missing formal libraries. The present (T) is already a successful proper-fragment transport. |
| **Investigate** | Run author trials only after an interface and checked models exist. | #290 with #235. Freeze direct and shared tasks: construct (K), apply it, transport it, diagnose a missing properness/PF obligation. Separate framework/model setup, routine author work, assistance and retained witnesses. Include a held-out task; report actual attempts. |
| **Defer** | Broad implementation of purity, localization and constructible biduality, and a claim of full higher six-functor coverage. | #555. Retain these as explicit library/source-language requirements; select a sourced duality benchmark and its exact hypotheses before implementation. Deferral concerns sequencing, not relevance. |
| **Reject** | Treat an invertible mate as automatic; equate separate models with transport; infer all-six or higher expressivity from (K); identify derived tensor with tensor of cohomology groups. | These claims fail to supply the required contract. The existing mate control and the missing exceptional/Hom/higher data identify the specific defects. |

A first ordinary implementation can validate the reusable proof mechanism while
motivic and higher work proceeds independently. Its acceptance must report that
boundary explicitly. Broader adoption requires the new mathematical clients and
recovered native specializations, not a shorter proof script alone.

## Validation and statement review

This artifact requires source, link and mathematical review rather than a Lean
build. The statement review checked each fiber and variance in (K), the
properness of `p`, the definition and orientation of BC/PF, the counit
characterization (E), the endpoint comparisons and mate equation in (T), and
the adjunction directions in (H). Absolute sheaf cohomology, relative motivic
objects and coefficient conventions remain distinct. `f=g=id` reduces (K) to
the tensor unit/composition identifications; the open-immersion instance of (H)
exercises a nonproper admissible map. These are paper controls, not checked tests.

The source review checked the cited numbered results and the geometric domains;
the Ayoub access limitation is recorded above. Independent Standards and Spec
review, tracked outside this source file, remain the implementation workflow's
acceptance gate. No formal build or proof audit is claimed for these sketches.
