# Higher inductive types required by retained consumers

Research for [#404](https://github.com/VladimirMarko/conaled/issues/404).
Inspected local revision: `78540f8f30ed8cb1afa7dc799a96dac65fec1458`.
Use the retained circle cover as the first complete source consumer, and keep
the larger `K(ℤ,2)` construction as an explicit remaining obligation. A new
nonzero higher witness would repeat completed work without importing that
construction.

## Pinned dependency audit

The [experiment receipt](../../experiments/dependent-higher-identity/validation.json)
and [source explanation](../../experiments/dependent-higher-identity/README.md)
pin Agda 2.8.0.2 and Cubical v0.9 revision
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. The retained import graph is a module
closure, not a minimal declaration dependency proof. This investigation reads
that evidence; it does not rerun its checker.
The unchanged `Monodromy.agda` file has SHA-256
`bbca6eabc7d35040fd5bb1fcc84f49c12ddfcfb90ffc2edb6d922a8c6e622aa3`. The acceptance declarations are
`step`, `transport-three`, `transport-two`, `value-and-witness-twice` and
`transported-witness-twice`; matching only the integer outputs omits the last
two dependent claims.

| Retained component | Required construction |
|---|---|
| `FrozenMemo.agda` | Generic dependent pair, identity elimination, substitution and conjugation reasoning. No HIT constructor in the memo itself. |
| `HigherWitness.agda` | `coHomK 2`, the pointed `Kn≃ΩKn+1∙` comparison twice, univalence and `PathIsoEq` converting both loop layers to inductive equality. |
| `Monodromy.agda` | Circle integer cover, successor transport, nested transport and the same frozen substituted witness. |

At the pinned revision,
[`coHomK (suc n)`](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/ZCohomology/Base.agda)
is a truncation of `S₊ (suc n)`; in particular `coHomK 2` uses the library's
truncation index 4, its convention for a 2-type.
[`S₊ 2`](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/HITs/Sn/Base.agda)
is the suspension of the circle. The generic cohomology module also imports
nullification and set truncation; that import alone does not prove each is a
minimal dependency of `coHomK 2`. The pinned [truncation implementation](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/HITs/Truncation/Base.agda)
uses recursive `hub` and `spoke` constructors over sphere-indexed functions,
so a point-only quotient is not its source presentation.
A declaration-level slice of the pointed
comparison remains necessary before promising a complete importer.
The pinned
[`Cover`](https://github.com/agda/cubical/blob/b150186d2544e7efeddd31e5d14a8b9ecbb100f7/Cubical/Data/Equality/S1.agda)
uses the circle recursor with the successor type path converted to inductive
identity. This makes the equality-conversion boundary unavoidable.

## What the indexed cubical schema establishes

[Cavallo–Harper, POPL 2019, §§3–4](https://www.cs.cmu.edu/~rwh/papers/higher/paper.pdf)
provides indexed cubical inductive types with recursive higher constructors.
Its argument/boundary language and admissibility conditions delimit the schema.
Canonical values can include formal composition and coercion. The stronger
zero-dimensional constructor result is for non-indexed types; it is not a
promise that every indexed identity term reduces to reflexivity. The paper's
circle and 0-truncation examples therefore do not establish compatibility with
every Agda HIT or truncation encoding.

The inspected 27-page paper is DOI `10.1145/3290314`, PDF SHA-256
`c0b517025e366cdbec8c934bd2b1f1484e15bc830e9248a75003e052d4284992`.
Its Cartesian constraints and Kan operations differ from the selected De Morgan
semantics. Treat the schema as a source of construction and eliminator ideas,
not a theorem already instantiated by our presheaf family API.

## Bounded interpretation plan

Preserve `Monodromy.agda` and its 3-versus-2 observation as the acceptance target.
Construct a small circle semantic family with point `base`, path `loop`, and
lawful filling. A groupoid carrying an integer automorphism can be a comparison
model, but its existence alone does not supply the circle's dependent eliminator
or justify all source rules.

For each admitted dependent motive `P`, the eliminator takes `b : P base`
and a dependent path over `loop` from `b` to `b`. Prove its point computation,
path computation at every dimension, and compatibility of the path endpoints
with the point case. Prove reindexing under arbitrary context and dimension
substitution, and the action on formal composition using motive filling.
Only then interpret the source recursor. The proposed consumer theorem states
that interpreting its nested transport yields the existing integer observation
and retains the full pair and transported witness after both substitutions.

The next higher-constructor check is a suspension meridian and its endpoint
computations; the truncation step additionally needs its eliminator's
truncated-motive restriction and higher boundary coherence. These are later
coverage obligations for `HigherWitness`, not requirements to close the first
circle construction. Interpreting its pointed double-loop equivalence requires
retaining the basepoint comparison: an unpointed equivalence loses the
`encode(refl)=0` evidence used to reject erasure.

The [universe graph](cubical-universe-glue-milestone.md) supplies the code-valued
circle motive for the cover. The [fibrancy assessment](fibrancy-capability-assessment.md)
supplies reusable target closure. The [compatibility matrix](cubical-judgment-compatibility.md)
owns the separate source-judgment obligations. #316/#321/#322's accepted higher
witnesses remain valuable target parameters and regression clients, but none
replaces this source construction and elimination work.

## Tests that can reject the route

Reject a circle eliminator whose path case has the wrong endpoint, or which
handles the point and loop but lacks a composition clause. Test endpoint
substitution both before and after elimination. Reject arbitrary elimination
from truncation into an unproved nontruncated motive. Finally erase the first
cover loop: the observed result must change from 3 to 2 while the original
statement remains fixed. A model collapsing that distinction cannot serve this
consumer, even if it validates a weaker existence theorem.

Implement the circle admission and cover interpretation as one staged follow-up
with explicit partial checkpoints; do not close it upon constructing `base`
and `loop`. If the indexed conversion needed by `PathIsoEq` cannot be preserved,
record that failed rule and compare a Path-only reformulation as a changed
consumer, never as unchanged source reuse. No broad HIT framework or foundation
adoption is justified by this report alone.
