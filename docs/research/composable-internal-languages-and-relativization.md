# Composable internal languages and relative semantics

Research note, 2026-10-24. This investigates the two constructions in the
preserved conversation supplied by the project owner. It proposes design tests,
not a replacement for the existing Lean embedding or a fixed compilation chain.
The governing direction remains [mathematical settings as parameters](../language-direction.md).

## What Vickers's tower consists of

Vickers, [*Generalized point-free spaces, pointwise*](https://arxiv.org/pdf/2206.01113),
§8, printed pp. 18–21, works with relative geometric theories and bounded toposes.
An internal theory in a base topos E yields a classifying topos over E;
bounded geometric morphisms compose (§8).

In §8.1, a GRD presentation Σ (generators, relations, disjuncts; §4.3) becomes
parameter data in a theory. Adjoining
a point produces `(Σ : GRD, F : pt(Σ))`. For a family `Σ : X → GRD`, the
extension is `(x : X, F : pt(Σ(x)))`. Repeating this construction gives the
quoted “tower of relativizations, with internal at one level being external at
the next.” The finite quantifiers in Proposition 8 concern finite presentation
data; they do not license unrestricted universal quantification.

Section 8.2 treats sites: represent objects, arrows and covers internally,
then describe flat continuous functors geometrically. Making the site condition
geometric requires additional chosen structure. Section 8.3 identifies the
relative classifiers as bipullbacks of model-reduction maps. Presentations
matter: a GRD presentation is not uniquely determined by its locale.

This supports iterated relative construction, not a theorem that every logic,
model or infinite tower admits such internalization. Sections 7.2 and 11 leave
the scope of the geometric/arithmetic program open.

## Two constructions and their different contracts

**Transport between settings.** A structure-preserving map acts on an existing
interpretation. For the simply typed case, Awodey's
[*Notes on Type Theory*, §2.5](https://awodey.github.io/typetheory/notes/typetheory2.pdf)
defines translations of λ-theories that preserve constructors and axioms.
They preserve derived equations and compose. Cartesian closed functors induce
the corresponding translations of internal languages. The required preservation
includes exponentials if the source uses function types; a bare functor does
not supply it.

Schematic equational contract:

```text
source term t  ── translation τ ──→  target term τ(t)
     │ interpretation                       │ interpretation
     ▼                                      ▼
arrow ⟦t⟧ in C ─────── F ─────────→ arrow F(⟦t⟧) in D
```

The bottom-right identification can involve comparison isomorphisms rather
than definitional equality. If `⟦t⟧ = ⟦u⟧`, functoriality gives equality of
their images. Identifying those images with the translated syntax requires
the preservation contract. This explains the role of the square, without
requiring that the next target be Lean's native mathematics.

**A setting constructed within another setting.** Here the input includes
internal data specifying the new semantic setting. The output is a relative
semantic construction over the surrounding setting, together with its
external account. This changes the base in which subsequent constructions
are interpreted. Merely applying a map to a term does not perform this task.
Caramello and Zanfa develop the external description through indexed categories
and stacks in [*Relative topos theory via stacks*, Introduction and §§2–3](https://arxiv.org/pdf/2107.04417).
Their conventions distinguish small-generated sites, locally small categories
and small categories. An internal presentation and an arbitrary externally
large category therefore cannot be treated as interchangeable inputs.

For our design, a useful distinction is between supplying a model as a Lean
parameter and allowing the object language to describe a model relative to
its current context. The former already enables reuse. The latter needs
formation, interpretation and change-of-base rules for the model data itself.
These are separate capabilities, even when both are implemented in Lean.

## Composition does not guarantee recovery of information

The following are mathematical checks on a proposed contract, not new checked
Lean results.

Preservation alone has the shape

```text
T proves φ  ⇒  U proves τ(φ).
```

It does not imply the converse. As an elementary example, the unique functor
from a category with two distinct parallel arrows to the terminal category
identifies their images. Returning an equality through that functor is invalid.
For equations, faithfulness supplies the relevant reflection of arrow equality.
For a general theorem, specify conservativity or an appropriate reflection
theorem for the chosen judgments. A syntactic translation's conservativity
and a semantic functor's faithfulness are different obligations.

Likewise, external validity need not produce a global witness. Consider the
two-element set with its elements exchanged by a two-element group. Its map
to the terminal group-set is surjective, but a global element would have to be
a fixed point, and none exists. Thus an interpretation of existence through
epimorphisms cannot be replaced by a choice of global elements. This is a
worked mathematical example; it has not been added to the repository as a proof.

The design implication is that each edge should state separately what it
preserves, what it reflects, and what witness or equality information it
forgets. Requiring equivalences everywhere would exclude useful forgetful maps.
Treating all maps as reversible would make unsound return paths possible.

## Depth, coherence and expressive power

The defensible replacement for “there is no inherent depth at which composition
must break” is conditional: **any finite sequence of compatible interpretations
can be composed once the required composition and coherence laws are provided.**
There is no depth bound in ordinary categorical composition. This says nothing
about whether the next requested interpretation exists.

Four different ambitions should receive separate acceptance criteria:

| Ambition | Required evidence |
|---|---|
| A particular finite chain | Each edge is defined and the interfaces match. |
| Every finite path in a fixed family | A uniform composition operation and its laws. |
| Arbitrary nesting of internally constructed settings | Closure under relative construction, change of base, and explicit size conditions. |
| A semantic object representing an infinite tower | A specified limit or other construction and a theorem that its required structure exists and is preserved. |

The last row does not follow from finite composability. Nor does making a finite
syntax for a tower prove that the tower has the intended semantics. Universe
polymorphism can support a family of finite constructions without producing a
single universe containing every level and its own semantics. The exact universe
requirements must follow the chosen representations; this note does not infer
one Lean universe increase per semantic nesting step.

Dependent coherence is a mathematical obligation, not only an elaboration
problem. Clairambault and Dybjer's
[*The Biequivalence of Locally Cartesian Closed Categories and Martin-Löf Type Theories*, §§1–3](https://arxiv.org/pdf/1112.3456)
correct the naive treatment of strict substitution by arbitrarily chosen
pullbacks. Their result uses democratic categories with families, extensional
identity, Σ and Π structure, and morphisms preserving structure up to
isomorphism. It does not establish a corresponding result for arbitrary
intensional identity, cubical operations or univalence.

For the project, preserving expressive power means recording these differences
instead of forcing every edge through the weakest common logic. A path using
only existential and conjunctive reasoning should have a small contract. A path
using dependent functions or higher identity should expose those additional
requirements. A branch may support one contract and fail another. Failure should
identify the missing preservation law, not silently change the statement.

A design with branching paths and comparisons has a relevant precedent:
Gratzer, Kavvos, Nuyts and Birkedal's
[*Multimodal Dependent Type Theory*, §§2, 4, 7 and 9](https://arxiv.org/pdf/2011.15021)
uses a small strict 2-category of modes, modalities and transformations.
Its models carry more structure than an arbitrary diagram of functors;
dependent right adjoints participate in its semantic constructions. This is
evidence that an organized network can be given syntax and semantics. It is
not evidence that its modalities automatically implement relative topos
construction or every translation required here.

## What the repository currently supplies

This assessment comes from inspecting the named definitions, not from running
new Lean checks.

| Existing construction | What it establishes | What it does not establish |
|---|---|---|
| [`Squares.compose`, `vertical`, `compose_assoc`](../../Squares.lean) | Horizontal and vertical pasting with an explicit agreement condition. | Closure of an arbitrary object language under internal model construction. |
| [`Compiler.Target`, `Sound`, `compile_sound`](../../Compiler.lean) | Target-parametric compilation and conditional semantic correctness. | A network of dependent theory translations with reflection. |
| [`Internal.FormulaCore`, `Derives`, `sound`](../../SquareKit/Internal/Logic.lean) | Syntax independent of its Set interpretation; equality, binary atoms, conjunction and existential derivations. | Full geometric syntax, including arbitrary disjunctions, or a universe of internal theories. |
| [`SheafContexts.sound`](../../SquareKit/Internal/SheafSoundness.lean) | The supported derivations interpreted through sheaf predicates and local images. | A construction of arbitrary relative classifying toposes. |
| [`StructuralModel.Telescope`](../../SquareKit/Internal/PathTransport/ContextualModel.lean) and [groupoid model](../../SquareKit/Internal/PathTransport/GroupoidSoundness.lean) | Finite dependent telescopes, reindexing and a constructed ordinary-groupoid instance of the supported rules. | Arbitrary higher identity or internal towers of groupoid/topos semantics. |
| [Dependent function comparison](../../SquareKit/Internal/DependentFunctionSheafComparison.lean) | Comparison of supported source operations with ordinary sheaf dependent-product structure. | General comparison data for all paths through all models. |

The first construction, transport, already has substantial ingredients here.
The second is not supplied by calling a Lean-level model a parameter or by
nesting Lean records. Its missing design question is how model presentations
become admissible data inside an interpreted language, with an externalization
theorem for that construction.

## Bounded design tests before new infrastructure

Continue the embedded implementation. The following are proposed tests for
its interfaces, not a prescribed implementation sequence or an importer project:

1. **Two paths, one result.** Interpret a current graph or Frobenius derivation
   directly in a model and through a second interpretation. State the exact
   comparison between the paths, including substitution.
2. **A parameterized setting.** Specify a small family of presentations depending
   on a base context. State what extending that context means semantically and
   how substituting base parameters changes the constructed setting.
3. **Nesting and transport together.** Compare changing the base before forming
   the relative setting with changing it afterwards. Write the required comparison
   square and identify which hypotheses would make it commute.
4. **An intentionally unsupported operation.** Use a principle absent from one
   edge's contract and check that the obligation remains visible. Separately test
   a return path that lacks reflection.

These tests keep both constructions in scope. They also expose whether a proposed
shared interface is erasing mathematical differences before committing to Agda
import, a new surface syntax, or a general relative-topos implementation.
