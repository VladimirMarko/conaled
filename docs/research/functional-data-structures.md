# Functional data structures: design and verification sources

Research date: 2026-10-26. Context: the Algorithm Design with Haskell
reconstruction in [#149](https://github.com/VladimirMarko/conaled/issues/149),
compiler optimization, and reusable mathematical libraries.

Use *Algorithm Design with Haskell* for algorithm derivation, add Okasaki for
persistent representation design, and use *Functional Data Structures and
Algorithms: A Proof Assistant Approach* as the main verification companion.
Read selected papers where a concrete representation or compiler transformation
needs them. This is a targeted source survey, not a proposal to port another
whole textbook.

## What Algorithm Design with Haskell covers

Bird and Gibbons cover amortized running times (§2.4), symmetric lists,
random-access lists and arrays (chapter 3), binary search trees and dynamic sets
(§§4.3–4.4), priority queues (§8.3), and disjoint sets/union–find (§9.3).
The preface nevertheless explicitly limits its treatment of data structures to
what its algorithm developments need and directs readers to Okasaki for more.
The book therefore already answers part of the question, while identifying its
own intended companion. [Publisher's contents and preface, especially p. xv](https://assets.cambridge.org/97811084/91617/frontmatter/9781108491617_frontmatter.pdf).

The book, supplied formalization, and accepted conaled reconstructions are
different bodies of evidence. The preserved checkpoint's
`project/BOOK-COVERAGE.md` reports symmetric-list invariants and amortization,
cached random-access paths, separate carry/borrow analyses with mixed-operation
counterexamples, array/copy costs, and AVL operations and costs. These are
supplied coverage reports, not fresh verification of all those claims here.
Consult the [archive guide](../history/algorithm-design-haskell/README.md) and
[reconstruction map](adwh-reconstruction-map.md) for provenance and accepted
scope. A data-structure gap assessment must match declarations and assumptions
against that map before proposing duplicate work.

## Representation and algorithm design overlap

Maciej Piróg's *FizzBuzz in Haskell by Embedding a Domain-Specific Language*
starts with command lists and an interpreter, recognizes the interpreter as a
fold, and transforms the program to remove intermediate structures. Context
composition also supplies a monoid. It supports the proposed connection:
choosing a representation changes which computations and transformations are
available. [Original article](https://themonadreader.wordpress.com/wp-content/uploads/2014/04/fizzbuzz.pdf).

The remaining design questions concern whole interfaces: which operations must
be cheap, what old versions remain usable, which invariants operations preserve,
and what evaluation and sharing assumptions justify the costs. An equality of
results alone does not establish an improvement in runtime or allocation.

## Complementary sources

| Source | Contribution | Recommended use |
| --- | --- | --- |
| Chris Okasaki, *Purely Functional Data Structures* | Persistence, lazy evaluation, amortization, scheduling, numerical representations, bootstrapping, and recursive slowdown. | Main source for designing persistent representations and understanding their costs. |
| Tobias Nipkow and collaborators, *Functional Data Structures and Algorithms: A Proof Assistant Approach* | Machine-checked functional correctness and running-time analysis in Isabelle. | Main source for proof organization and explicit cost models. |
| Andrew W. Appel, *Verified Functional Algorithms*, Software Foundations vol. 3 | Interactive Coq development of algorithms, abstract data types, trees, tries and queues. | Supplement for teaching, specifications, and proof engineering. |
| Ralf Hinze and Ross Paterson, *Finger trees: a simple general-purpose data structure* | A reusable sequence representation parameterized by monoidal measurements. | Focused example connecting algebra, representation design and search. |

Okasaki explains why ordinary amortized arguments can fail under persistence:
multiple futures can reuse a version and spend the same saved work. His lazy
constructions and analyses address this problem; scheduling turns selected
amortized bounds into worst-case bounds. Study the assumptions before moving
an implementation between evaluation strategies. The book includes Haskell
code; the freely available thesis supplies the underlying development but is
not the identical edition.
[Publisher's chapter overview](https://www.cambridge.org/core/books/abs/purely-functional-data-structures/amortization-and-persistence-via-lazy-evaluation/95B424557EF683F5EB579544A645EF6A),
[author's thesis at CMU](https://www.cs.cmu.edu/~rwh/students/okasaki.pdf).

Nipkow's book, previously available as *Functional Algorithms, Verified!*, links
its exposition to Isabelle proofs. It treats abstract data types, balanced
search trees, Braun arrays, tries, quadtrees, priority queues, amortization and
queues. Its step-counting functions make the performance claim an explicit
mathematical object. This is the strongest match among these sources for
combining correctness and complexity proofs. [Book site](https://fdsa-book.net/),
[contents and running-time model](https://fdsa-book.net/functional_data_structures_algorithms.pdf).

A particularly relevant reusable pattern appears in Isabelle's `Set_Specs`:
operations, an abstraction map, and a representation invariant have separate
roles. It derives set-interface laws from sorted inorder-list laws. That is a
concrete example of law transport to compare with conaled's squares, rather
than a reason to introduce a new universal interface before examining existing
code. [Checked theory](https://isabelle.in.tum.de/library/HOL/HOL-Data_Structures/Set_Specs.html).

Appel's volume teaches specification and verification of search trees,
balanced trees and priority queues; its ADT chapter addresses hiding
representations behind verified interfaces. It is useful for learning how to
structure the proof, while Nipkow provides the more direct starting point for
the combined correctness-and-cost agenda. The Coq exercises are learning
material, not automatically completed theorems to import.
[Preface](https://softwarefoundations.cis.upenn.edu/vfa-current/Preface.html),
[ADT chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/ADT.html).

Finger trees cache monoidal reductions and specialize to random-access
sequences, priority queues, and ordered sequences. Their search specification
distinguishes finding a transition from finding the unique transition;
monotonicity or application invariants justify the latter. This is a useful
test of extracting exactly the algebra and laws an operation requires. The
paper's bounds also require accounting for the cost of measurement operations.
[Author-hosted paper, especially §§4.1–4.7](https://www.cs.ox.ac.uk/people/ralf.hinze/publications/FingerTrees.pdf).

## A bounded next investigation

First make a coverage matrix for the existing and incoming library: abstract
operations, executable representation, invariants, correctness, cost model,
and persistent versus linear operation histories. Separate archived evidence
from accepted public declarations. This would answer what guidance and proved
components are missing more precisely than another bibliography alone.

Then select a concrete client and compare candidate realizations. Candidate
studies include a compiler work queue, a finite map for an environment, or a
sequence with cached monoidal summaries. These are proposed experiments, not
claims that the current compiler needs those representations. Prefer existing
Lean and Mathlib implementations when their contracts fit.

For each study, require an abstraction map or relation, invariant preservation,
and agreement with the client's semantic specification. Add a separate cost
statement with explicit primitive costs, history restrictions, and sharing
assumptions. For an optimization, also identify the baseline being improved.
These obligations fit the repository's
[architectural guidance](../agents/architectural-quality.md) and
[existing separation of representation contracts](../adr/0002-relations-and-synchronization.md).
They would establish useful reusable mathematics without treating semantic
compiler correctness as an automatic performance theorem.
