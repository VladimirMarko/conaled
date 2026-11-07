# Boundary ordering for the dependent pair theory maps

This is the boundary analysis for
[#344](https://github.com/VladimirMarko/conaled/issues/344). Its independently
fixed rule tables, declarations and selected client are in the
[framework assessment](dependent-calculus-frameworks.md). The calculations
below compare presentations; they do not import a source metatheorem into Lean
merely by citing it. Implementation coverage must be read from the checked
construction and its acceptance record.

## Source contracts

Bauer–Haselwarter–Lumsdaine (BHL), v1, §6.5 assumes sequential contexts, rules
and boundaries. Definition 6.22 maps each symbol to a target expression over
its argument metavariables; application instantiates that template with
translated arguments. Definition 6.24 adds a derivation for each translated
primitive rule. Propositions 6.23/6.25 establish composition and functorial
action. Definition 6.20 separately requires well-formed boundaries over earlier
rules. Raw-map transport does not require acceptability or a semantic model.
These are existing source constructions to port or adapt, not missing results
invented by this project. [BHL §§6.4–6.5](https://arxiv.org/html/2009.05539v1#S6.SS4).

Haselwarter–Bauer (HB) represents metavariable dependencies with abstracted
boundaries. Definition 2.18 checks a rule's metavariable context and conclusion
boundary over its predecessors. Its contextual and context-free presentations
are distinct: the latter adds annotated free variables and assumption tracking.
The context correspondence does not automatically supply arbitrary
syntax-changing theory maps. Theorem 3.18's presupposition result has
well-formed-context hypotheses. Those hypotheses cannot be dropped when
adapting the presentation. [HB §§2.4, 3.2, 4, 6](https://arxiv.org/html/2112.00539v1#S2.SS4).

## The frozen boundaries in sequential form

All the following encodings are our calculations for the pair example. The
ambient variable context Γ is well formed. Each row's metavariables are
introduced in the displayed order; a later entry can refer to an earlier one.
An entry `(x:A) ⊢ B(x) type` binds x in that argument, not in the whole rule.

| Primitive | Ordered argument boundaries | Result boundary |
|---|---|---|
| P | A type; `(x:A) ⊢ B(x) type` | □ type |
| pair | A type; `(x:A) ⊢ B(x) type`; a:A; b:B(a) | □:P(A,B) |
| fst | A type; `(x:A) ⊢ B(x) type`; p:P(A,B) | □:A |
| snd | A type; `(x:A) ⊢ B(x) type`; p:P(A,B) | □:B(fst(A,B,p)) |
| S, pack | The corresponding P/pair entries, independently declared | □ type; □:S(A,B), respectively |
| split | A type; `(x:A) ⊢ B(x) type`; `(p:S(A,B)) ⊢ D(p) type`; `(x:A,y:B(x)) ⊢ e(x,y):D(pack(a:=x,b:=y))`; p:S(A,B) | □:D(p) |

The binder-count vectors are `[0,1]`, `[0,1,0,0]`, `[0,1,0]` and
`[0,1,1,2,0]` for formation, construction, projection and split respectively.
Binder counts establish scope only. The boundaries also retain the classes
of arguments, their types, and dependencies; the counts alone are not a
well-formed dependent theory.

In a direct sequential encoding, introduce A's boundary, extend by its
metavariable, introduce B's boundary in scope x:A, and continue. In the HB
notation the first two entries become `A:□ type` and
`B:{x:A} □ type`. The same replacement of each scoped entry by an abstracted
boundary gives the remaining entries. There is no extra mathematical premise
in this change of display. A machine translation still needs to prove that
metavariable application, binder extension and substitution commute with it.

The comparison therefore favors using one verified scoped syntax for this
bounded experiment, with explicit judgment boundaries and rule certificates.
Adding a second independent HB syntax layer would require a second
capture-avoidance implementation and a bridge before it could reuse the same
raw-map theorem. This is an implementation-cost judgment for the frozen cases,
not evidence that HB is weaker or less appropriate for a context-free frontend.

## First beta must precede the second beta boundary

Write `q = pair(A,B,a,b)`. Before either equation is admitted, the formation
rules give

```text
fst(A,B,q) : A
snd(A,B,q) : B(fst(A,B,q))
b : B(a).
```

The first beta equation has endpoints already in A. Once it is available,
congruence for B yields `B(fst(A,B,q)) ≡ B(a)`. Term conversion then places
`snd(A,B,q)` in B(a), allowing the second beta equation's two endpoints to
share their announced type. The second beta equation cannot itself certify
this conversion without defeating the predecessor discipline.

One valid order is P formation, pair formation, fst formation, snd formation,
first beta, second beta, then eta. The eta boundary needs the earlier formation
rules: `snd(p):B(fst(p))` already makes `pair(fst(p),snd(p))` well typed.
The beta equations need not be claimed necessary just to form that eta
boundary; placing eta last makes it the separately admitted stronger law.

The full-family [semantic fixture](../../Examples/DependentPairTheoryModels.lean)
makes the common-fiber dependency explicit with
`castFiber (B γ) (first_beta γ a b) (second γ (pair γ a b)) = b`.
This is a semantic boundary check. It does not replace the syntactic proof
that the relevant source rule is admitted at its predecessor stage.

## Eliminator macros have the same dependency

In Eη, the primitive split rule and its constructor beta equation precede the
projection macros. For first, choose constant motive A and branch x. Its
formation needs no projection beta; its computation is an instance of split
beta. For second, choose motive `B(first(p))` and branch y. At a constructed
argument the required branch type is `B(first(pack(x,y)))`, whereas y is
initially in B(x). The derived first-beta equation supplies precisely that
conversion. Only then is the second macro well typed and its second-beta
certificate available.

G expands fst and snd to these templates. It must act under the motive's one
binder and branch's two binders. In particular, substituting an expression
for a free variable must weaken it under those binders, leaving the newly
bound variables unchanged. The two nonidentity substitutions in the selected
client test this action at dependent types and selected terms. Tests on only
closed pair values would not establish it.

For a proposed reverse presentation H, the branch application
`e(fst(p),snd(p))` initially lies in `D(pair(fst(p),snd(p)))`. Eta is needed to
convert it to D(p). The flagged projection-only model rejects that step in
general. This diagnoses the missing law without misusing that model as a
separator for primitive dependent elimination.

## Adaptation obligations and what they do not buy

A bounded Lean implementation must identify its substitutions and premise
occurrences and prove its own identity/composition laws. A naturality field on
an arbitrary syntax operation is not, by itself, an encoding of a source
metavariable template. The concrete template expansion must be constructed,
and its binder/substitution equations discharged. If an HB boundary layer is
chosen, it additionally needs flattening and reconstruction maps, compatible
instantiation and boundary-preservation proofs. A report of similar-looking
records is not that bridge.

For each primitive rule, the target certificate must derive the translated
conclusion from translated premise occurrences. Generic proof-tree induction
then derives transport of an entire proof. This separates one-time traversal
and grafting laws from the recurring local certificates needed when adding
Eη. It also separates proof-tree equality in the chosen Lean representation
from judgmental equality of object terms, semantic equality of selected
values, and a round trip of translations. None follows merely from another.

Well-scoped raw syntax is not presupposition validity. Likewise, a valid
full-family model does not establish inversion, uniqueness of typing,
substitution elimination or acceptability for every syntactic presentation.
Only explicitly checked boundary and structural results should be advertised.
Higher identity/J, arbitrary raw assumptions and context-free assumption
tracking remain outside this frozen pair experiment.
