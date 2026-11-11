# A Haskell frontend for conaled

A restricted Haskell frontend is a credible next compiler project. A semantics-preserving frontend for unrestricted GHC Core is a separate research programme. The main scope decision is which observations and inputs the frontend promises to preserve, not how many constructors occur in Core's AST.

This is a source-based feasibility assessment, not an implemented frontend or a measured effort estimate. Local inventory is assessed at baseline `40bc196d1100d76b4832f837a4309eef84dd1d98`. Inspection used the local compiler interfaces, the author paper, first-party plugin documentation, and explicitly versioned GHC 9.12.2 documentation/source. That GHC version is an inspection baseline, not a proposed project pin or a claim about the newest release. No GHC/plugin builds were attempted.

## Existing foundation and the missing step

[`Compiler.lean`](../../Compiler.lean) already defines intrinsically typed terms with functions, products, sums, nonrecursive lets, and abstract primitives. `compile_sound` relates compilation to a total Lean evaluator, subject to the target's `Sound` contract and supplied primitive meanings. [`FirstOrder.lean`](../../FirstOrder.lean) separately supports targets without closure. These are substantial reusable components. Neither module parses Haskell nor defines GHC Core semantics. [`docs/SOURCES.md`](../SOURCES.md) explicitly says the project does not port ConCat's GHC plugin.

The implemented [finite-sum reactive lowering](finite-sum-reactive-lowering.md) supplies another reusable target for a finite total fragment, including canonical admission, encoding correctness and conditional service contracts. Its circuit evaluates both case arms eagerly. Its proof therefore does not justify importing a lazy Haskell conditional whose unselected arm diverges. Reuse must preserve this totality boundary.

The existing [graph emission development](graph-emission-implementation.md) offers an architectural precedent: separate syntax conversion, typing, denotation, exact artifact correspondence, and primitive-environment checks. Its represented core is a bounded **Lean expression** fragment, not GHC Core. Reusing that pattern would require a new Haskell-specific boundary.

The [language direction](../language-direction.md) asks authors to reuse constructions across settings with explicit requirements. Haskell syntax could improve program authoring, but would not by itself supply transport of Lean proofs, dependent judgments, or richer mathematical settings.

Elliott's [paper](https://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf), sections 3–5, supplies the relevant mechanism: translate lambda syntax into categorical operations, then interpret those operations in another category. Section 10 documents engineering around numerical reboxing and compiler inlining; section 12 leaves broader recursion and separate compilation as future work. The paper's elegant mathematical translation should not be read as an end-to-end mechanized verification of arbitrary Haskell.

The first-party [ConCat README](https://raw.githubusercontent.com/compiling-to-categories/concat/master/README.md) confirms an implementation using both Haskell rewrite rules and a Core-manipulating builtin rule. It documents residual conversion markers producing runtime errors when translation fails. A conaled importer should instead reject incomplete conversion before accepting an artifact.

[Categorifier's plugin documentation](https://raw.githubusercontent.com/con-kitty/categorifier/main/plugin/README.md) reports support for sums and some recursion, but lists limitations involving mutual recursion, polymorphic recursion, arbitrary FFI, `RealWorld`, and constrained polymorphism. It also requires access to imported unfoldings and explains dictionary construction limitations. This is useful engineering evidence for a bounded frontend, not evidence that unrestricted Core has a ready-made formal model.

## Three scopes with different obligations

| Scope | Meaning and acceptance boundary | Work added beyond the existing compiler |
|---|---|---|
| Total restricted frontend | Admitted programs over related total inputs and approved primitives preserve the selected total denotation. Unsupported constructs fail explicitly. | Pinned GHC adapter, export format, admission checker, primitive/type mapping, translation proof, diagnostics and correspondence evidence. |
| Pure partial lazy fragment | Preserve divergence and partial values under specified observations, including forcing where admitted. | Lazy semantic domains or another justified partiality account, recursive definitions, a relation to execution, and revised target laws. |
| Broad GHC compatibility | Preserve a stated range of language, primitive and runtime behaviours across supported compiler configurations. | Much wider System FC/type representation support, primops, effects, exceptions and runtime interfaces, plus continuing compatibility work. |

These are proposed scopes, not project capabilities. The first is bounded engineering plus a focused correctness development. The second needs substantial new semantic mathematics. The third is too broad to estimate responsibly without an explicit feature and observation matrix. No elapsed-time estimate follows from the inspected sources.

The [GHC plugin API](https://downloads.haskell.org/ghc/9.12.2/docs/users_guide/extending_ghc.html) already provides access to Core and an insertion point in the compilation pipeline. It removes the need to implement the Haskell parser, renamer and typechecker. It does not remove their trust role, or decide which optimizations should occur before export.

## Why the semantic model grows

The [GHC 9.12.2 Core definition](https://raw.githubusercontent.com/ghc/ghc/ghc-9.12.2-release/compiler/GHC/Core.hs) has a compact expression datatype, but its fields include GHC types, coercions, variables and metadata. Its comments specify thunk allocation for lets, weak-head evaluation for case, and casts for newtypes and GADTs. An AST traversal is therefore much smaller than a faithful semantic model.

The following are unexecuted discriminating examples and proposed admission tests, derived from the [Haskell Report's expression rules](https://www.haskell.org/onlinereport/haskell2010/haskellch3.html) and [predefined types and `seq`](https://www.haskell.org/onlinereport/haskell2010/haskellch6.html):

- **Bottom and eta.** `seq (undefined :: Int -> Int) 1` fails to produce a value, while `seq (\x -> undefined x) 1` returns `1`. Here bottom abstracts failure or nontermination; an exception-sensitive execution contract would need to distinguish them. Unrestricted function eta is therefore incompatible with this observation. The existing total compiler's extensional function equality needs a restricted connection to Haskell, not silent reuse for arbitrary partial functions.
- **Lazy pairs.** An undefined pair differs from `(undefined, undefined)` when forced. Reconstructing a pair from its projections can change definedness. A model with only total Lean products loses that distinction.
- **Case versus let.** Matching `undefined` against a pair constructor diverges even when the branch ignores the fields; a lazy pattern binding can leave the value unforced. Replacing case by projections needs a totality hypothesis or a forcing-aware semantic rule.
- **Recursion and arguments.** Rejecting syntactic recursive bindings does not establish totality. Imported functions, dictionaries, primitives and higher-order arguments may still diverge. The accepted environment must have a semantic contract; termination on some inputs is insufficient for a universal total-function claim.

Several further decisions are independent of these counterexamples:

**Dictionaries and polymorphism.** A class dictionary selects actual operations; a class name does not prove algebraic laws. A proposed importer can specialize approved instances, or retain an explicit operation signature with evidence. Inlining arbitrary dictionaries and calling the result a lawful semiring is not a valid shortcut. Categorifier's documented dictionary and polymorphism limitations illustrate the practical work here.

**Casts and representations.** Runtime erasure does not license dropping every `Cast` in a typed importer. The translation must retain enough evidence to relate source and target types. A first version can accept an explicit set of representation conversions and reject GADT coercions and unsupported type forms. This restriction follows from the cast uses in the pinned Core source, not from any claim that Core casts execute runtime work.

**Numbers and primops.** GHC's [primitive-type documentation](https://downloads.haskell.org/ghc/9.12.2/docs/users_guide/exts/primitives.html) distinguishes boxed representations, liftedness and primitive operations. The proposed primitive contract must separately fix word width, overflow, division preconditions and floating-point observations. Mapping `Int` directly to Lean `Int`, or `Double` directly to mathematical reals, is not an equality-preserving default. Approximation or abstraction would need its own relation. Early export retains higher-level operations but more dictionary structure; late export exposes more specialized unboxed operations. Both choices need explicit handling.

**Sharing and resources.** Denotational equality alone does not preserve allocation, duplication or running time. A first frontend can retain lets and make no cost claim. A cost-preserving extension needs a sharing-sensitive execution model and a connection to the cost observation. [Breitner's mechanized Launchbury development](https://isa-afp.org/entries/Launchbury.html) demonstrates correctness and adequacy between lazy operational and denotational semantics. It is a useful reference for that separate obligation, not a complete GHC semantics to import unchanged.

A single `Option` around a total result will not represent all these distinctions: laziness permits partially defined fields and functions that are themselves defined while diverging on selected arguments. A domain-theoretic model can represent such distinctions, but its products, function objects, equality and fixed-point requirements must be checked against the exact source observations. Adding a generic bottom constructor to the existing compiler does not establish those laws.

## Proposed first experiment and trust boundary

Start with explicitly selected functions and a small approved primitive library. Fix one GHC version, flags, dependency closure and export phase. Admit a stated monomorphic fragment with products, sums, lambda/application and nonrecursive lets. Require total related inputs, including a logical relation for any higher-order inputs, and approved total primitives. Reject effects, unknown globals, unrestricted recursion, unsupported casts and unmodelled numeric operations. This is a proposed first slice, not a restriction that should silently define all future language work.

Export a versioned representation retaining binding identity, types, primitive identities and enough source/Core correspondence data for review. Lean should independently check admission and reconstruct typed terms, then establish the new translation theorem and compose it with `compile_sound`. Keep primitive semantics separate from categorical structure so that multiple targets reuse the same author program without being forced into an oversized interface.

The theorem must state exactly where its source begins. Checking that an imported AST is well typed establishes no equality with the original Haskell program: an exporter can replace addition by subtraction and still produce a well-typed term. Checking a translation certificate against exported Core can validate that later translation while still trusting the GHC-to-export boundary. Source hashes identify inputs but do not prove semantic correspondence. An end-to-end source claim needs a verified frontend/export step, independently checked correspondence with adequate semantics, or an explicit trust assumption covering that step and any preceding transformations. Core Lint and differential execution are useful checks, not replacements for this connection.

Retain successful examples for arithmetic, sums, captured variables and higher-order application; challenge the boundary with the bottom/eta/pair cases above, unknown dictionaries, altered primitive identities and unsupported coercions. Compare multiple target interpretations and author effort under the same contracts. The [hs-to-coq paper](https://arxiv.org/abs/1711.09286) supplies precedent for a useful total-Haskell translation into a proof assistant, but its existence does not establish a verified exporter for this project.

A useful completion criterion is therefore: an accepted fragment, explicit source/export assumptions, checked primitive and translation contracts, reusable target interpretations, and rejection examples demonstrating the boundary. Full lazy Core need not be solved before that experiment can deliver value.

The practical first client should use total Boolean data, products and finite
sums, followed by a finite-state transition. This avoids choosing machine-integer
or floating-point semantics merely to demonstrate the frontend. Higher-order
authoring can initially be internal to the admitted program; accepting arbitrary
Haskell callbacks would need the stronger input contract described above.

This assessment recommends a bounded exporter/admission experiment before a
general Core model. Start with a small cross-module source corpus to expose
unfolding and dictionary requirements, and report accepted and rejected Core
forms before selecting a larger implementation scope. General recursion remains
under #109; the source-to-proof association in #489 and certificate API in #490
are related contracts, not already implemented Haskell proof importers. Haskell
annotations and Core type-coercion evidence alone are not Lean proofs of totality
or bounded service. The earlier [codata assessment](codata-elaboration-termination-contracts.md)
and [demand/retention assessment](demand-retention-cleanup-assessment.md) contain
reusable obligations, but do not supply a complete lazy GHC semantics.
