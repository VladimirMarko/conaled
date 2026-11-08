# Proof-theoretic support and classical realizability: bounded next tasks

Commission two independent research tasks now. Keep formal implementation
conditional on their results. The existing [coverage map](semantic-traditions-coverage.md)
and [scaling disposition](architecture-scaling-study/disposition.md) identify
real obligations, but waiting for an incumbent consumer leaves these alternatives
unable to demonstrate their own value. Their relevance follows from the
[language direction](../language-direction.md): one asks how inferential
requirements determine admissible settings; the other gives classical reasoning
an operational interpretation. Neither requires replacing the current architecture.

This reassessment supplies source checks, paper calculations and proposed
acceptance criteria. It supplies no new Lean theorem, execution result or author
productivity measurement. The issue scopes below are proposals for #290 and
#196, coordinated with #235; no tracker status was verified or changed here.

## Support: isolate the usable fragment

The Gheorghiu–Pym manuscript still has a displayed clause labelled disjunction
whose left side uses conjunction and whose second premise omits its formula.
Definitions 2.4–2.6 and Figure 2 nevertheless specify atomic derivability,
implication and consequence under extensions within a fixed basis. The prose
before Figure 2 explicitly requires every premise. Its full classical and
intuitionistic correspondence results use different bases. These facts permit
an atoms-and-implication experiment without repairing the derived disjunction or
quantifier clauses. They do not license the full second-order completeness claim.
[Primary manuscript, pp. 9–12](https://www.cantab.net/users/david.pym/Proof_theoretic_Semantics_for_Second_order_Logic.pdf).

For the proposed experiment, define support by structural recursion:

```text
B ⊩ p       iff p has a finite atomic derivation in B
B ⊩ A → C   iff for every D in the fixed basis with B ⊆ D,
                  D ⊩ A implies D ⊩ C
```

This is an explicit restricted specification derived from those primitive
clauses, not an editorial correction of the manuscript. Use finite Horn atomic
rules with no discharged assumptions. Derive monotonicity by induction on
formula structure and transitivity of inclusion: extensions of an enlarged
base are also extensions of the original base. No completeness theorem is
needed for this derivation.

An original paper fixture makes the proposed task concrete. Take atoms `p,q,r`,
`B₀ = {p ⇒ q}`, `B₁ = B₀ ∪ {⇒ p}` and `B₂ = B₁ ∪ {q ⇒ r}`. Choose the basis
of all finite Horn systems on these atoms. Every extension of `B₀` that derives
`p` derives `q`, so `B₀ ⊩ p → q`; the same argument survives both inclusions.
The derivation of `q` at `B₁` is retained at `B₂`. In contrast, in the singleton
basis `{∅}`, the empty base supports `p → q` vacuously. Enlarge that basis to
`{∅, {⇒ p}}` and the implication fails at the empty base. This rejects
basis-independent support without importing the manuscript's full logic.

Support is a proposition and does not itself retain a chosen derivation. Add
labelled derivation trees as separate data, with an inclusion map preserving
each old rule label. Freeze an independently defined observation of a selected
tree, for example its ordered rule-label trace. Extend `B₂` with an alternative
derivation of `q`; a procedure selecting the shortest available proof may then
change the trace even though support is preserved. Retaining the old tree gives
a possible bridge. This is a proposed proof-relevant enrichment, not a claimed
feature of the source semantics. It must earn its cost against direct
derivation transport.

**Proposed research issue: support and selected derivations across atomic-base
extensions.** Acceptance should require:

1. A frozen recursive definition, basis and rule format, with a clause-by-clause
   source map. Derive implication introduction/application and monotonicity
   within this fragment; do not assume a global soundness theorem as input.
2. The two strict extensions above, the basis-change counterexample, and a
   selected derivation with a separately defined observation. Explain what
   changes when an alternative proof is admitted.
3. A comparison with direct labelled-derivation transport on the same rules,
   observations and extensions. Count semantic setup, recurring obligations
   and the repair needed after adding one inference rule. Truth preservation
   alone cannot satisfy the selected-data subtask.
4. A decision about implementation: construct a reusable bridge, or exhibit the
   precise information lost by support and state the enrichment required.
   Either can complete research. A demonstrated support capability remains a
   result even if the stronger selected-data bridge fails.

This task does not require second-order syntax, a generic proof translator,
geometric models or a universal support library. Those boundaries bound the
experiment; they are not reasons to postpone it. The manuscript ambiguity still
blocks treating its full displayed semantics as an implementation specification.

## Classical realizability: select a principle and an observation

Krivine defines an algebra with terms, stacks, control and a pole closed under
predecessors of reduction. Theorem 1.3 gives adequacy relative to that
interpretation; Proposition 1.6 realizes Peirce's law with `cc`. Theorems
1.12–1.15 separately treat storage and arithmetic realizers. Thus a control
principle and arithmetic interface are available starting points, while
selected-output preservation still requires a separate argument.
[Krivine, §§1–2](https://arxiv.org/pdf/1005.2395).

Select Peirce's law `((A → B) → A) → A` as the classical requirement. The
[earlier effect study](effectful-witness-interpretation.md) compared handler
policies; the [omitted-traditions report](omitted-semantic-traditions.md)
explicitly left this control/pole construction open. A task can therefore be
scheduled without waiting for another effect-policy consumer.

The proposed arithmetic client is bounded search in a supplied finite list of
natural numbers, returning the first even entry, its position, an evenness
certificate and evidence that earlier entries are odd. Specify this result
directly from list order and parity before defining machine semantics. The
fixture `[1,2,4]` admits multiple even witnesses and selects `2`. Use captured
control for early escape from traversal. This client does not need classical
logic to be computable; it tests what an implementation using a classical
control principle preserves. Establish Peirce's realization separately so a
constructive search implementation alone cannot satisfy the task.

Construct a candidate pole from an operational success predicate, rather than
postulating pole membership for the desired program. For a frozen input, let
`Pgood` be processes reducing in finitely many steps to a terminal delivery of
an even witness with a weaker certificate proving position lookup and evenness
only. This certificate excludes the earlier-entries-odd evidence required by
the full client specification. It is backward closed by composition of
reductions. Require an explicit successful process and a terminal rejected
process that cannot reach success. These establish nonemptiness and properness.
This is an original construction proposal; its compatibility with the chosen
algebra and terminal conventions remains work for the task.

Even this proper pole accepts delivery of `4` on the fixture. Therefore it does
not enforce the first-result specification. Define the finer selected-result
observation independently, and prove preservation for the actual program. A
more selective pole may encode that observation, but proving that the program
belongs to it remains an obligation. Membership must not be supplied as an
assumption. The universal pole is an additional rejection control.

Properness also does not imply logical coherence: a proper subset of processes
could still contain every stack execution of some proof-like term. If claiming
a consistent logical interpretation with falsity interpreted by all stacks,
prove that every admitted proof-like term has a stack outside the pole. If this
fails, retain the bounded operational result and explicitly withhold the
consistency claim. Fix the proof-like class, including whether terminal/output
instructions belong to it; otherwise this condition is underspecified.

**Proposed research issue: Peirce control, operational poles and retained search
witnesses.** Acceptance should require:

1. An explicit term/stack machine and permitted proof-like terms. Derive
   adequacy for the selected implicational fragment, including the control
   case, and work through Peirce's realizer. Arithmetic decoding, terminal
   delivery and certificates need their own specified interface.
2. Construct and assess `Pgood`; prove closure, give positive and negative
   processes, reject the universal pole, and state whether coherence holds.
   Distinguish a nontrivial operational interpretation from model consistency.
3. Supply the independent finite-search specification, a control execution
   derivation, and a termination argument restricted to finite inputs. Retain
   the multiple-witness control and an input with no witness, using an explicit
   failure result for the latter. No general normalization claim is requested.
4. Change continuation representation from closures to explicit continuation
   frames. Give the related-state invariant and the simulation needed to retain
   the selected position, numeral and certificate meaning. Also test a changed
   policy that returns a later valid witness; acceptance of that witness by
   `Pgood` must not count as selected-output preservation.
5. Compare the control route with direct finite search on the same input and
   result specification, recording setup, reusable lemmas and the obligations
   of the representation change. Report whether the classical principle adds
   reusable expressiveness, only implementation choice, or unresolved cost.

The required research outcome is a worked construction or an exact obstruction
at one of these obligations, with surviving weaker results named. Lean code is
optional for research acceptance. A later implementation issue must require
checked specializations, statement review, the applicable build/audit and
independent review; a paper adequacy argument cannot satisfy it. Dependent
choice, set-theoretic models and a general extraction library remain outside
this task.

## Scheduling and evidence limits

Run the two research tasks independently under #290, with #196 participating
in the control task. Neither depends on the adjoint, geometry, binding or
probability experiments. At each acceptance, decide a bounded implementation
successor or record an obstruction and the exact additional hypothesis needed.
Do not gate their start on adapting to an incumbent interface. Apply the same
setup and preservation accounting to direct and alternative routes.

The primary PDFs linked above were accessible on 2026-11-08. The support
clause check used extracted text at the displayed source location; no corrected
edition or author clarification was obtained. The Krivine reading covered the
named definitions and theorem statements, not a replay of all proofs. Earlier
reports' source-access failures are historical; neither linked PDF failed in
this reassessment. The operational pole and derivation-observation constructions
above are explicitly proposed calculations, not claims of external or local
formal verification.

This document changes no formal declarations. Its validation is whitespace and
local-link checking; the enclosing implementation workflow owns independent
Standards and Spec review.
