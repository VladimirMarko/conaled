# Frozen executable fixture for #291

Frozen before the reusable interface, against repository revision
`2525b12052e4c85c57f9050dbf18f7a36ba2ef19` and the
[#287 fixture](representation-extension-comparison/fixture.md).

Admit all set models with nonempty sorts A and B, an equivalence relation R
on A, and unrestricted P on A. Maps are pairs of functions preserving R and P
forwards. Old observations are all classical first-order formulas with typed
assignments, including equality and quantification over both sorts. Arbitrary
maps need not preserve these observations. Canonical expansion adds A×B and
A/R. Every expansion satisfying the product unique-pair axiom and the quotient
kernel and surjectivity axioms must compare isomorphically over its reduct.

The named consumer is the existing exact parser observation contract in
`Applications/Languages/IndexedCompositional.lean`, retaining the entire
`Decision (P w)` for words within the fixed depth, including the selected
witness. Its model adapter takes A to parsers for a fixed inhabited language,
B to the singleton type, R to equality of all bounded exact observations,
and P to the unrestricted always-true predicate. The resulting quotient must
recover native `Parser.parse` at every bounded word through the public
quotient extension. The native trie interpretation supplies the existing
independent denotation. This adapter exercises the quotient recipe and its
constant-fiber observer descent; it does not by itself exercise all first-order
formulas, arbitrary models, or varying dependent fibers. Those receive separate
universal proofs and checked instances. Recognition-only agreement must still
reject the existing two parsers choosing opposite epsilon witnesses.

Independent controls retain the #287 contracts unchanged: Bool A, singleton B,
universal R, empty P; swap is an admitted automorphism, no equivariant selector
exists, and a noncanonical section does. Adding c with P(c) must fail in this
model and succeed in a model with inhabited P. Dependent descent uses coherent
fiber equivalences, identity and composition, with a three-element base whose
classes have sizes two and one and whose fibers have cardinalities two and one.
The zero-index section must descend and recover its exact index; identity
transport over universal Bool must reject the section selecting its base value.

Mathlib's first-order language is single-sorted at the inspected pin. Reuse its
syntax and satisfaction by a tagged-carrier adapter with sort predicates and
relativized quantifiers; do not silently identify that carrier with either
original sort. The executable model class remains genuinely two-sorted and
unrestricted in cardinality. No syntactic-conservativity, proof-tree recovery,
or higher-groupoid strictification claim is planned.
