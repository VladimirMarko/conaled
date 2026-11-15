Prompt:
````md
I remember that Robert Harper had some strong reservations about HoTT a few years ago. I believe his issue was that he did not believe that it could be given a computational interpretation, or something along those lines. Instead, he was pushing his RedPRL work. Can you please find out what that was about and whether and how it was resolved?
````

Response:
````md
**The computational objection was real, and its central technical part has been resolved. But I would qualify your recollection of Harper’s position:** the sources show him insisting that axiomatic HoTT had not supplied the computational meaning he wanted, while actively working to provide it. RedPRL was one implementation of that research programme. His group’s own 2018 paper explicitly acknowledged that several cubical approaches had supplied solutions. [cs.cmu.edu](https://www.cs.cmu.edu/~rwh/papers/redprl/lfmtp18.pdf?utm_source=chatgpt.com)

There are three strands to the story: the problem with treating univalence as an opaque axiom; Harper’s particular preference for building type theory from computation; and the distinction between computational **cubical theories** and the **original axiomatic presentation of HoTT**.

## 1. What Harper was actually saying

A particularly sharp statement appears in an August 2015 discussion on the HoTT mailing list:

> “Neither MLTT nor the HoTT variant have any inherent computational meaning.”

The context matters. Harper was objecting to a discussion of the time and space costs of univalence before an operational semantics had been specified. He immediately went on to explain how, once such a semantics was given, the cost of transporting along an equivalence would depend on executing that equivalence. His statement also included ordinary Martin-Löf type theory, so it reflects a broader methodological position about formal calculi and their computational interpretations. It should not be read as a claim that MLTT, or HoTT, could never be made computational. [groups.google.com](https://groups.google.com/g/homotopytypetheory/c/5snMdo3LnP8?utm_source=chatgpt.com)

There is unusually clear evidence about his expectations. In a paper dated December 14, 2015, Steve Awodey and Harper described extending the computational interpretation to univalence as the major outstanding challenge. They then said that recent developments in cubical models:

> “strongly suggest that such a unification will be achieved in the near future.”

That is an explicitly optimistic assessment. [cs.cmu.edu](https://www.cs.cmu.edu/~rwh/papers/siglog/siglog.pdf?utm_source=chatgpt.com)

Moreover, Harper had been pursuing this problem for years. In July 2011, Dan Licata announced their joint work obtaining canonicity for a restricted, two-dimensional type theory, explaining exactly how their formulation made previously stuck uses of transport compute. That was an early partial solution, before the later cubical developments. [Homotopy Type Theory](https://homotopytypetheory.org/2011/07/27/canonicity-for-2-dimensional-type-theory/?utm_source=chatgpt.com)

My reading of these sources is therefore: **Harper was demanding a computational foundation for the higher-dimensional ideas, and regarded producing one as a substantive research problem.**

## 2. What was the computational problem?

The key property is **canonicity**. In its computational form, it says that a closed expression of a basic data type evaluates to an actual value of that type. For example:

- A closed term of type `Bool` evaluates to `true` or `false`.
- A closed term of type \(\mathbb N\) evaluates to a numeral such as \(0\), \(1\), or \(2\).

“Closed” means that the expression has no unresolved input variables or assumptions. Huber’s subsequent cubical canonicity theorem establishes the natural-number property using a deterministic operational semantics. [arxiv.org](https://arxiv.org/abs/1607.04156?utm_source=chatgpt.com)

### Why an axiom for univalence causes trouble

Univalence lets us turn an equivalence of types into an identification of those types. Schematically,

\[
e:A\simeq B
\quad\longmapsto\quad
\mathsf{ua}(e):A=_{\mathcal U}B.
\]

An identification permits **transport**: moving an element, or a more complicated structure, from one type to another.

The difficulty in the original axiomatic presentation is that ordinary identity elimination has a computation rule for reflexivity:

\[
\mathsf{transport}(\mathsf{refl},x)\;\longrightarrow\;x.
\]

But if `ua` is merely an added axiom, an expression involving \(\mathsf{ua}(e)\) need not reduce to reflexivity, and there is no corresponding evaluation rule telling transport how to proceed. Licata’s 2011 explanation of his work with Harper identifies precisely this obstruction. [Homotopy Type Theory](https://homotopytypetheory.org/2011/07/27/canonicity-for-2-dimensional-type-theory/?utm_source=chatgpt.com)

A small example makes the distinction concrete. Boolean negation is an equivalence

\[
\mathsf{notEquiv}:\mathsf{Bool}\simeq\mathsf{Bool}.
\]

Use univalence to turn it into a path from `Bool` to itself, then transport `true` along that path:

\[
t :=
\mathsf{transport}_{X\mapsto X}
  \bigl(\mathsf{ua}(\mathsf{notEquiv}),\mathsf{true}\bigr).
\]

The intended answer is `false`: transporting along the equivalence should apply negation. In axiomatic HoTT, one can establish the appropriate **propositional equality**. But that is different from the evaluator reducing the expression to `false`. The same distinction arises when transporting entire algebraic structures between equivalent representations, as the 2014 HoTT research proposal explains. [homotopytypetheory.org](https://homotopytypetheory.org/wp-content/uploads/2014/04/proposalpublic2.pdf?utm_source=chatgpt.com)

This is why two statements that sound similar are technically different:

| Statement | What it provides |
|---|---|
| \(t\) **evaluates to** `false` | The computation rules produce the Boolean value. |
| There is a **proof of** \(t=\mathsf{false}\) | The theory contains evidence identifying the expression with that value. |

A stuck expression can already be a normal form. Thus the immediate problem is **failure of canonicity**, not necessarily failure of termination. Nor does it prevent developing and checking mathematical proofs in the axiomatic theory; it prevents automatically obtaining all the expected data by ordinary evaluation. The contemporary proposal explicitly distinguishes these possibilities. [homotopytypetheory.org](https://homotopytypetheory.org/wp-content/uploads/2014/04/proposalpublic2.pdf?utm_source=chatgpt.com)

Higher inductive types raised a related problem. These introduce constructors for paths and higher paths, as well as for points. Giving them a computational interpretation requires explaining how programs act on that higher-dimensional structure. Cavallo and Harper’s later work addressed this with a schema of cubical inductive types and an accompanying canonicity theorem. [cs.cmu.edu](https://www.cs.cmu.edu/~rwh/papers/higher/paper.pdf?utm_source=chatgpt.com)

## 3. Why RedPRL appealed to Harper

Harper’s preferred approach came from **computational type theory**, particularly the Martin-Löf/Nuprl tradition. The order of explanation is significant:

1. Specify a programming language and how its programs evaluate.
2. Explain types in terms of the behaviour of those programs.
3. Justify typing and proof rules against that computational meaning.

For example, the meaning of membership in `Bool` includes evaluating to one of the two Boolean values. The research programme then extends this explanation to higher-dimensional types, adding computational operations for transport and the higher structure. Angiuli, Harper, and Wilson’s 2016 paper presents precisely this approach. [arxiv.org](https://arxiv.org/abs/1604.08873?utm_source=chatgpt.com)

**RedPRL applied that methodology to Cartesian cubical type theory.** Its underlying theory supported both:

- Higher-dimensional **paths**, carrying the information relevant to univalence and homotopy theory.
- A separate **exact equality**, with equality reflection, in the tradition of extensional computational type theory.

These are distinct notions of equality. The system did not flatten the higher-dimensional paths into trivial equality proofs. Angiuli, Favonia, and Harper’s 2018 theory validates univalence in its fibrant fragment while also providing exact equality types, and proves that every closed Boolean evaluates to `true` or `false`. [drops.dagstuhl.de](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2018.6?utm_source=chatgpt.com)

The most decisive passage for your question is on the first page of the 2018 RedPRL paper. After describing the computational shortcomings of axiomatic extensions, the authors write:

> “Multiple researchers have recently established the constructivity of univalence and higher inductive types”

They credit the cubical theory of Cohen, Coquand, Huber, and Mörtberg, then introduce their Cartesian cubical approach as another solution. **By that point, Harper’s own publication presented the central existence-of-computation problem as solved by multiple approaches.** [cs.cmu.edu](https://www.cs.cmu.edu/~rwh/papers/redprl/lfmtp18.pdf?utm_source=chatgpt.com)

## 4. How cubical type theory supplied the solution

Cubical theories enrich the language so that higher-dimensional objects have explicit computational structure.

The central ingredients are:

- **Formal interval dimensions.** A path can be represented by an expression depending on an interval variable, with specified endpoints. More dimensions give squares, cubes, and higher cubes.
- **Transport and composition operations.** These provide computational ways to move through families of types and combine higher-dimensional information.
- **Constructions implementing univalence.** In the CCHM theory, *Glue types* let an equivalence participate in constructing a path between types. Univalence is then provable using the new machinery.

The substantial achievement was designing these operations so that their equations, boundaries, and higher-dimensional interactions work together. The CCHM paper supplies a constructive semantics and makes both univalence and function extensionality provable. [arxiv.org](https://arxiv.org/abs/1611.02108?utm_source=chatgpt.com)

This has concrete implementations. **Cubical Agda supports computational univalence and higher inductive types.** Its documentation explains how equivalences can be packaged as paths and then used computationally through transport. [Agda 2.10.0 documentation](https://agda.readthedocs.io/en/latest/language/cubical.html?utm_source=chatgpt.com)

The Boolean example above is present in the official Cubical Agda library: transporting `true` along the path induced by negation computes to `false`. The library checks the result using `refl`, which in this case means that computation itself establishes the required equality. [agda.github.io](https://agda.github.io/cubical/Cubical.Data.Bool.Properties.html?utm_source=chatgpt.com)

One technical qualification: the completely general law relating transport along `ua e` to applying `e` is not necessarily a judgmental equality in every cubical formulation. Cubical Agda states that general law propositionally. The concrete Boolean computation nevertheless reduces as expected. [Agda 2.10.0 documentation](https://agda.readthedocs.io/en/latest/language/cubical.html?utm_source=chatgpt.com)

### The main milestones

| Period | Development | What it settled |
|---|---|---|
| **2016–2018** | CCHM cubical type theory, with Huber’s canonicity proof | A constructive formulation of univalence in which closed natural-number terms compute to numerals. The arXiv papers appeared in 2016; publication dates vary by version. [arxiv.org](https://arxiv.org/abs/1611.02108?utm_source=chatgpt.com) |
| **2016–2018** | Angiuli, Harper, Wilson, and subsequently Favonia: computational higher type theory and Cartesian cubical computational type theory | The computational foundation behind RedPRL, including Boolean canonicity and eventually univalent universes alongside exact equality. [arxiv.org](https://arxiv.org/abs/1604.08873?utm_source=chatgpt.com) |
| **2019** | Cavallo and Harper’s work on higher inductive types | A broad schema of indexed cubical inductive types, with computational semantics and canonicity. [cs.cmu.edu](https://www.cs.cmu.edu/~rwh/papers/higher/paper.pdf?utm_source=chatgpt.com) |
| **2021** | Sterling and Angiuli’s normalization theorem | Normal forms for **open terms** in a Cartesian cubical theory, yielding decidability of judgmental equality and injectivity of type constructors. [arxiv.org](https://arxiv.org/html/2101.11479v2?utm_source=chatgpt.com) |

The final row is a further achievement beyond computing closed data. Proof assistants also need to compare expressions that still contain variables. Sterling and Angiuli’s theorem addresses that problem. Its precise scope matters: the published paper treats a specified Cartesian calculus with functions, pairs, paths, glue, and the circle; it is not a blanket theorem about every feature of every cubical implementation. [arxiv.org](https://arxiv.org/html/2101.11479v2?utm_source=chatgpt.com)

## 5. What about the original axiomatic HoTT?

This is the main qualification to “the problem was solved.”

Cubical theories **change the underlying language and computational rules**. Their success does not cause an unchanged MLTT evaluator, faced with an opaque univalence postulate, to acquire new reduction rules.

There is, however, a further development for the original syntax: **homotopy canonicity**. Instead of requiring direct reduction to a canonical value, this asks for a canonical value together with a proof, in the original theory, identifying the given term with that value.

Rafaël Bocquet’s *Strict Rezk completions of models of HoTT and homotopy canonicity*, first submitted in 2023 and revised in October 2025, gives a constructive proof. Its formal canonicity theorem is stated for Booleans in the specified HoTT with univalent universes and standard type formers, including W-types. Thus a closed Boolean has a closed identity proof connecting it to `true` or `false`. The paper also credits a 2019 proof by Sattler and Kapulkin whose details had not been publicly written up. [arxiv.org](https://arxiv.org/html/2311.05849v2?utm_source=chatgpt.com)

Bocquet’s author page currently lists the work as **under review**, so it is best described as a publicly available proof in a preprint rather than a published journal theorem. [rafaelbocquet.gitlab.io](https://rafaelbocquet.gitlab.io/?utm_source=chatgpt.com)

This changes the answer one should give today:

- **Executable univalence with canonicity:** established in cubical theories.
- **Recovery of canonical data up to an identity proof in axiomatic HoTT:** now also supported by a constructive homotopy-canonicity result.
- **Direct reduction under the original, unchanged computation rules:** the original stuck-term problem remains a fact about those rules.

The second result is substantial, but it is a different computational guarantee from running a cubical evaluator. It also should not be inflated into a theorem covering every possible higher inductive extension.

## 6. What remained of Harper’s reservations, and what happened to RedPRL?

The foundational preference survived the computational breakthrough.

An illuminating exchange occurred in the `cooltt` project in March 2021. Jon Sterling explained why subsequent work had moved toward typed normalization by evaluation and bidirectional elaboration: these made important typing and equality tasks easier to automate. The work retained computational semantics and gained a stronger account of computation with open terms.

Harper then distinguished type theory as an algebraic framework from type theory as a foundation for specifying and verifying programs. He wrote:

> “Both are interesting and important, and it is clear that the cubical methods are best-suited to the algebraic setup.”

My interpretation is that **the successful computational treatment of univalence did not erase his distinctions about what type theory should explain or which methodology best serves programming**. That is a separate issue from whether computational univalence exists. [GitHub](https://github.com/RedPRL/cooltt/discussions/186?utm_source=chatgpt.com)

The original RedPRL implementation was archived on April 2, 2023. The team’s subsequent systems include **redtt** and **cooltt**, both pursuing Cartesian cubical type theory; the project’s own site presents these as part of the same family of experimental proof assistants. [GitHub](https://github.com/RedPRL/sml-redprl?utm_source=chatgpt.com)

For reading the history directly, I would start with these three sources:

1. **[Awodey and Harper, “Homotopy Type Theory: Unified Foundations of Mathematics and Computation”](https://www.cs.cmu.edu/~rwh/papers/siglog/siglog.pdf)** — especially page 8, for their 2015 assessment of the computational challenge and prospects.
2. **[“The RedPRL Proof Assistant”](https://www.cs.cmu.edu/~rwh/papers/redprl/lfmtp18.pdf)** — the first page places the objection and the acknowledged cubical solutions side by side.
3. **[The 2021 cooltt discussion](https://github.com/RedPRL/cooltt/discussions/186)** — for the later evolution of the implementation approach and Harper’s own response.
````
