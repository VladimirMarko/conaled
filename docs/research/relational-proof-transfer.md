# Relational transfer of a FIFO construction

For [#295](https://github.com/VladimirMarko/conaled/issues/295), retain the direct
logical-relation proof for the frozen FIFO client. Investigate annotated transfer
only when another client makes repeated translation work visible. A partial
Galois presentation fits this representation, but its canonical representative
is extra data and must not replace the client's selected state silently.
Neither alternative discovers the algebraic requirements of an arbitrary proof.

This is a paper comparison with reused checked local evidence, not a new plugin
run or a formalization of either external metatheorem. The inspected local
revision is `701023ce73ff297604fb21f2b6caada9e727c10c`; the research checkout starts
at `a272379ff0abfb9d5b033340e77885266b065a79`. The cited FIFO source files are
identical between those revisions. No new Lean result or author-effort measurement
is claimed. The completed #210 delivery remains evidence, not reopened work.

## Frozen input and independent output contract

Use the [existing FIFO operations](../../Applications/Sequences/AbstractFIFO.lean)
and [ordinary client](../../Examples/AbstractFIFO.lean). Let `Q` be raw symmetric
list pairs, `L = List Nat`, `d q = q.front ++ reverse q.back`, and

```text
R q xs := Inv q ∧ d q = xs.
w := [enqueue 1, enqueue 2, delete, enqueue 3].
F_Q q := run symmetric w q.
F_L xs := run lists w xs.
```

Freeze the intended meaning before selecting a transfer route: commands append
to and delete from an ordinary sequence, including total deletion from empty.
The output must include the supplied implementation's final state, evidence
`R (F_Q q) (F_L xs)` for every related input, and exact equality of the final
`Option Nat` head observations. From the empty states, the abstract final state
is `[2,3]` and the head is `some 2`. A theorem that merely some target output
exists is insufficient. Exact raw layout equality is not promised by `R`.

This relation is not an isomorphism: the accepted valid layouts
`([1],[3,2])` and `([1,2],[3])` both denote `[1,2,3]`, yet their front lengths
differ. It is partial on raw pairs because `Inv` is required. Reversing it does
not choose an implementation state. The selected output here comes from
`run symmetric`, whose definition is fixed independently of the proof.

The task uses the same `Nat`, command list and `Option Nat` on both sides.
Their relations are equality. It is deliberately not a dependent-family
benchmark: changing an indexed output later requires an explicit relation over
related indices and the chosen output data in those fibers. Recognition or an
existential witness cannot stand in for an exact parser decision.

## Primary-source scope

[Cohen, Crance and Mahboubi, Trocq, v1](https://arxiv.org/html/2310.14022v1),
§§3–4.5, was inspected beyond the abstract. Theorem 4.7 assumes well-formed
`γ(Δ)`, typing `γ(Δ) ⊢+ M : A`, a term translation at annotated `A`, and a type
translation of `A` at an annotated universe. It yields a typed target and
`M_R : rel(A_R) M M'`. Thus successful derivations are certified; their existence
is a premise. Figure 8 supplies application and abstraction rules. Section 4.5
requires constant translations at chosen annotations, with consistent erased
types; unsuitable annotations can leave translation stuck. The annotation
lattice tracks relational structure, including maps, rather than assuming every
relation is an equivalence. Univalent parametricity in §4.2 uses univalence;
that is not a blanket requirement of every weaker translation. This assessment
uses v1's theorem numbering and does not claim a version comparison or plugin
execution.

[Kappelmann, Transport via Partial Galois Connections and Equivalences,
v1](https://arxiv.org/pdf/2303.05244v1), §§3.2–5, was inspected, including the
proof of Theorem 4.1 and the composition restrictions. Corollary 4.2 lifts
nondependent function relations when input and output partial Galois connections
are supplied, input relations are reflexive on their fields, and output
relations are transitive. Transport functions precompose with the input reverse
map and postcompose with the output forward map. Theorem 4.10 composes
connections or the listed equivalences when the middle relation agrees exactly;
forward maps compose in execution order, reverse maps in reverse order.
Theorem 4.12 instead treats partial preorder/PER equivalences with commuting
middle relations and constructed endpoint relations. Neither licenses arbitrary
unmatched composition. The dependent theorem has additional indexed monotonicity
premises; this FIFO comparison uses the nondependent case. The formalization
and prototype are in Isabelle/HOL, without a univalence requirement. They were
not replayed here. The HTML v1 endpoint was unavailable; the primary PDF supplied
the technical text, so this is not missing mathematical evidence.

## Direct transfer: construction and witness

Here is the paper derivation, using the existing public hypotheses. Let
`h : Simulation symmetric lists R`. A related input carries `(valid, decodeEq)`.
For an empty word, return the same two states and that relation witness. For
`enqueue x :: cs`, apply `h.snoc x` to the witness and continue with `cs`.
For `delete :: cs`, apply `h.tail` and continue. Finally apply `h.head` to the
final relation witness. This supplies both the state relation and observation
equality without selecting an inverse of `d`.

For the frozen word the witness is the explicit chain

```text
r0 : R q xs
r1 := h.snoc 1 q xs r0
r2 := h.snoc 2 _ _ r1
r3 := h.tail _ _ r2
r4 := h.snoc 3 _ _ r3
observation := h.head _ _ r4.
```

The transferred construction is `F_Q`, with certificate `r4`; equivalently its
output can be packaged as `(F_Q q, r4)` in the subtype of states related to
`F_L xs`. The state is data, the certificate is propositional. For empty inputs,
`h.empty` supplies `r0`. This is an explicit construction, not elimination of a
propositional existence claim to obtain executable data.

The generic derivation is already checked as `Simulation.run_preserves` and
`Simulation.client_eq`; `symmetric_correct` discharges its primitive obligations
using the existing operation squares. The example file checks the frozen word,
its `[2,3]` result and `some 2` observation. Those are reused accepted declarations,
not newly compiled evidence for this report. The chain above is explanatory
paper notation, not a separately checked Lean snippet.

## Annotated transfer on the same input

A proposed Trocq-style reconstruction would translate the argument, rather than
register the entire `run_preserves` conclusion as a primitive. Freeze these
entries before attempting it:

| Input | Target | Required relational evidence |
|---|---|---|
| List-state carrier | Symmetric-state carrier | Converse of `R`; retain its invariant restriction |
| `Nat`, commands and the frozen word | Same values | Equality; constructor and list eliminator compatibility |
| Empty, enqueue and delete | Existing symmetric operations | `h.empty`, reversed `h.snoc` and `h.tail` |
| Final head observation | Existing symmetric head | Reversed `h.head`, with equality on `Option Nat` |
| Word induction/recursion | Same word recursion | Its relational translation, not an opaque whole-client axiom |
| Function/result types and equality elimination | Corresponding relational types | Type-level derivation and equality-transport obligations at the chosen annotations |

The raw application rule would send each command application to the supplied
target operation and apply its witness to the two inputs and their relation
proof. Abstraction introduces the two states and their relation proof. For the
unrolled frozen word, these steps produce precisely `F_Q` and `r4` above. Thus
there is a concrete paper target and witness to test a plugin against, rather
than an assertion that a relation by itself synthesizes a queue implementation.

An actual annotated transfer still needs the universe/arrow annotation choices
and registered recursor and equality translations to elaborate together. No full
annotated derivation or plugin run was performed, so this report does not mark
that end-to-end transfer as established. In particular, registering only the
operation witnesses proves neither type translation nor translation of
`ordinary_correct`. Treat them as separate obligations in an adapter trial.

The comparison is still discriminating: the target construction needs no state
inverse, and the direct certificate uses no univalence. A prototype that forces
univalence or bijectivity for this fragment has exceeded its mathematical needs.
That would reject the proposed adapter configuration, not establish a limitation
of every possible Trocq annotation. A stuck recursor registration is unavailable
derivation evidence; accepting the forbidden observer below would be unsound
relative to the frozen contract.

## Partial Galois alternative: a selected representative

The following is our paper instance, not a claimed application checked in
Isabelle or Lean. Define

```text
E_Q q q' := Inv q ∧ Inv q' ∧ d q = d q'.
E_L xs ys := xs = ys.
e xs := run symmetric (map enqueue xs) nilSL.
```

Induction on `xs`, using the accepted enqueue square and empty invariant,
gives `Inv (e xs)` and `d (e xs) = xs`. This encoder uses the existing symmetric
operations; it does not assume the invalid representation `(xs,[])` is always
admitted. `E_Q` is a partial equivalence relation whose field is the valid pairs.
Both `d` and `e` are monotone for these relations. For valid `q`,

```text
E_Q q (e xs) ↔ d q = xs
E_Q (e (d q)) q
E_L (d (e xs)) xs.
```

These equations discharge the partial Galois conditions in both directions.
They do not prove `e (d q) = q`. Input/output PERs meet the reflexivity and
transitivity requirements for the nondependent function construction.
`F_Q` respects `E_Q`: decode both executions by `run_preserves` and use equality
of their initial lists. This is the required function-domain membership proof.
An arbitrary function on raw pairs would not satisfy it.

Transporting `F_Q` to lists yields `d ∘ F_Q ∘ e`, equal pointwise to `F_L` by
that same witness. Transporting `F_L` back yields the canonical implementation
`G_Q q = e (F_L (d q))`. For valid `q`, its output is related by `E_Q` to `F_Q q`,
and the heads agree. However, this construction does not establish equality of
the selected raw outputs. To meet the frozen contract, keep `F_Q` as the target
and use its existing compatibility proof; do not substitute `G_Q` without a
separate client contract permitting normalization.

This extra encoder and normalization are mathematical preparation costs even
when a framework generates higher function transfers. The direct route needs
neither. Conversely, a future client asking for canonical representatives could
use that preparation repeatedly. No runtime complexity or measured speedup is
inferred from these formulas.

## Composition and rejection controls

There are two distinct compositions. For concatenated command words,
`run_append` fixes execution order: execute the first word, then the second.
The intermediate state and its relation witness feed the next derivation.
`run_flatMap` supplies the retained command-substitution case; callers do not
reprove the word induction for each replacement.

For representation routes `R₁ : Q → L → Prop` and `R₂ : L → S → Prop`, compose
simulations over the *same* middle operations and observation type. The initial
relation contains an explicit middle state. Each command transforms that state
with the middle operations, preserving both witnesses; observation equalities
compose by transitivity. `Simulation.comp` checks this existential relation.
Its existence in `Prop` is not an executable choice of middle state. A client
requiring a selected intermediate representation must supply it as data.

The partial-Galois instance and its reverse meet through `E_L = Eq`, so their
map composition has a matching middle relation. Changing that relation, for
example from sequence equality to equality of element sets, changes the problem.
A transfer configuration must check compatibility afresh, not reuse the old
composition certificate. Annotated transfers likewise need their second-stage
constant and type witnesses to consume the first-stage results with the required
relation structure; composition is not justified by matching carrier names.

Retain these rejection controls:

- **Hidden layout observation:** a function `f : List Nat → Nat` agreeing with
  raw front length on all `R`-related states would assign both 1 and 2 to
  `[1,2,3]`. The existing `hidden_front_length` example refutes it. Direct
  transfer lacks the observation square; the proposed annotated registration
  would need that false witness; partial-Galois function transport lacks
  `E_Q`-respectfulness. This is failed structure, not inaccessible evidence.
- **Dropping validity:** `q = ([],[1,2])` decodes to `[2,1]`, but its symmetric
  head is `some 1`, not `some 2`. Thus the decoder graph without `Inv` does not
  preserve even the empty-word head client. This is a paper reduction using the
  inspected definitions, not a new checked counterexample.
- **Selected representative reset:** the two valid layouts above cannot both
  equal `e [1,2,3]`. A round trip through the encoder cannot preserve every raw
  layout, even though it preserves the public FIFO contract. Reject any adapter
  claiming exact selected-layout preservation from the PER alone.

## Existing non-isomorphic clients and decision

[#285](higher-order-extensional-comparison.md) already compares function inputs
through a relation and compares results while forgetting costs. Its application
and environment-extension premises must remain explicit; this FIFO success does
not supply a total erasure map on arbitrary behavioral functions. The checked
strong-observation counterexample prevents replacing extensional meaning by beta
counts. Reuse that control if a later adapter admits higher-order clients.

[#284](modular-guarded-streams.md) already transports constructed solutions
through modulo two using a local body square and target uniqueness. Noninjectivity
blocks equality reflection. Relational registration must not conceal guardedness,
solution construction or the operation-preservation premise inside a primitive
named “transfer solution.” These results are calibration fixtures, not new
implementations or a reason to reopen #284/#285.

| Route | Decision and preparation cost | Promotion condition and owner |
|---|---|---|
| Direct logical relation | **Adopt** for this client. Reuse four operation obligations, word induction and composition already supplied by #210. | #290 retains this as the comparison baseline; ordinary callers keep operation-only APIs. |
| Annotated transfer | **Investigate conditionally**. Prepare carrier, constant, recursor, type and equality registrations; produce a kernel-checkable witness without new axioms. Tool integration and annotation debugging remain unmeasured. | #290/#235 should scope a bounded adapter only when a second representation client repeats enough translation work to compare fairly. Freeze the FIFO controls and require a complete term-and-type derivation plus rejected hidden observer. |
| Partial Galois/PER adapter | **Defer implementation**. Prepare encoder, field/invariant proofs, respectful functions and matching composition relations. This FIFO needs only the partial-quotient special case. | #290 owns promotion when a client needs reusable canonical representative or restricted-domain transport. Require an explicit selected-data contract and compare against direct squares before adding shared machinery. |
| Universal equality or arbitrary-observer transfer | **Reject for this relation**. The retained counterexamples refute those strengthened contracts. | Any revised task must state a different relation or permitted observation, not suppress the failures. |

A successful transfer shows that supplied requirements suffice. It does not find
which FIFO operations an arbitrary client uses, identify a weakest interface,
or discover algebraic laws. #291–#294's requirement and theory-interface work
remains distinct. This comparison is not its prerequisite.

Residual work is conditional and owned above; no duplicate issue or immediate
formalization is proposed. The paper target and existing checked counterexamples
resolve the present applicability decision. A promoted adapter must preserve
ordinary clients, exact indexed parser witnesses and noncommutative weights,
then justify any new interface through additional reuse. Prefer existing
`Relational` and `AbstractFIFO` interfaces; an ordered specialization can use
Mathlib order structures where their hypotheses fit, but a partial PER must not
be silently installed as global equality or a total order.

Omitted here are plugin replay, a Lean annotation engine, dependent relator
formalization, performance measurement, author trials, changed logic and higher
identity. None is claimed as delivered. #107 stays paused, #108's theorem stays
unselected and unprepared, #260 stays inactive, and #305/#306 remain outside this
assignment. No frontend, universal AST, global subtyping or kernel axiom is
required by the recommendation.
