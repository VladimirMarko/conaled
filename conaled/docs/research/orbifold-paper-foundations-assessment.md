# Standalone orbifold development: paper and interpretation boundary

Assessment on 2026-10-19 of the user-supplied
`orbifolds-checkpoint-078-clean-rebuild-and-current-source-handoff.tar.gz`
in `/home/vlad/Downloads/orbifolds/`. Source paths below are archive members
relative to `orbifolds-lean/`. This note reviews mathematical meaning; the
companion reuse assessment covers current repository capabilities and builds.
The [curated archive guide](../history/orbifold/standalone-formalization/README.md)
contains the retained checkpoint and instructions for selective reuse.

The [arXiv record](https://arxiv.org/abs/2205.15887) lists only v1,
submitted 2022-05-31. The archive's correction is therefore a proposed
mathematical correction, not a later author-published revision found there.

The paper defines orbifolds using microlinearity and properly finite identity
types. Microlinearity tests infinitesimal pushouts through internal function
types. Its main comparison theorem concerns the Rezk completion of a crisp
ordinary proper étale pregroupoid. The intended models include smooth
infinity-toposes; explicit ordinary groupoids alone do not provide that
interpretation. See [Definitions 1.1.2 and 4.2.12, Theorem 6.3.7, and
§1.4](https://arxiv.org/html/2205.15887v1).

The printed Proposition 6.1.7 requires each point to have a unique finite
label. It does not require a label to determine a unique point. The archive
correctly identifies this reversal. Assigning every natural number the sole
label in `Fin 1` meets the printed condition. The corrected clause is
`R x i → R y i → x = y`.
See [Proposition 6.1.7](https://arxiv.org/html/2205.15887v1#S6.SS1.Thmthm7)
and the archive's `Finiteness/PrintedCounterexample.lean` and
`Finiteness/AssociationCharacterization.lean` under `Orbifolds/`.

The archive contains useful external mathematics, with these specific limits:

| Archive source | Checked statement's meaning | Consequence for reuse |
|---|---|---|
| `Orbifolds/External/Groupoid.lean`, `ActionGroupoid.lean` | Objects and arrows are native types; arrows retain group elements as data. | Suitable ordinary presentation mathematics. A later interpretation must connect these arrows to internal identifications. |
| `Orbifolds/External/InertiaFiniteness.lean` | The subtype of commuting arrows injects into the original hom type, transferring proper finiteness. | Reusable algebraic argument; no microlinearity or smoothness conclusion occurs in the theorem. |
| `Orbifolds/Finiteness/Definitions.lean` | Finite ordinal witnesses, injections and surjections; proper finiteness adds a proposition expressing decidable equality. | Useful constructive proofs. Native Lean predicates must still be interpreted or re-proved internally; their native quantification does not range over the model's generalized elements. |
| `Orbifolds/Finiteness/SubsingletonCover.lean` | A supplied subsingleton cover with subfinitely enumerable index yields proper finiteness. | The combinatorial final step is available. Producing that cover from geometric hypotheses is a separate obligation. |
| `Orbifolds/Category/Probe.lean` | Unique extension of ordinary hom-set maps along a test arrow. | A useful categorical lemma family; internal function objects or all generalized contexts, and higher mapping spaces, require additional arguments. The module itself states this limit. |
| `Orbifolds/External/Compactness/DPCompact.lean` | A native proposition distributing a fixed disjunction through universal quantification. | Its constructive derivations can guide an internal proof. Its native predicate does not distinguish compact geometric spaces. |

The compactness limitation is directly visible in the definition. Given
`∀ k, A ∨ B k`, classical case analysis on `A` proves
`A ∨ ∀ k, B k` for every native carrier `K`. This is a mathematical deduction
from the archive's source, not an assertion that its proofs are invalid.
Avoiding `Classical.choice` in those proofs preserves useful proof structure;
it does not by itself establish soundness in a chosen internal language.

The foundational obstruction files are also correctly scoped.
`Orbifolds/Foundations/NativeKockLawvere.lean` assumes a nontrivial native
carrier, specified algebraic laws, a Kock inverse property, and unique slopes
for **all native functions** on square-zero elements. It derives a
contradiction using classical reasoning. It does not rule out SDG interpreted
through objects and morphisms of a semantic category. Likewise, native
equality obstruction lemmas explain why ordinary Lean equality cannot retain
the archive's distinct Boolean action automorphisms.

Completing an internal-language infrastructure does not automatically move
these proofs into it. For each candidate, specify the object-language
statement, interpret its quantifiers and equality, discharge the required
logical and geometric structure, and prove the correspondence to its external
counterpart. Ordinary algebraic constructions can also remain external and
connect through explicit comparison theorems. The archive's
`docs/STATUS.md` and `docs/COVERAGE.md` already distinguish these routes and
do not claim the main theorem.

For later source acquisition, define acceptance targets before asking for
another isolated formalization: a result in the repository's internal
language, a model validating named operations, or an external theorem with
a specified comparison. Ask for nontrivial checked applications that expose
identity arrows, generalized contexts, and infinitesimal behavior. A library
of native propositions with familiar names cannot establish those contracts
merely by compiling. This is a recommendation from the source review, not
a claim that a particular HoTT or SDG package has already been evaluated.
