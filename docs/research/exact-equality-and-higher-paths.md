# Exact equality, higher paths and dependent coherence

Research for [#401](https://github.com/VladimirMarko/conaled/issues/401).
Inspected on 2026-11-09 at `78540f8f30ed8cb1afa7dc799a96dac65fec1458`.
Retain explicit higher witnesses and investigate restricted conversion only
where a concrete author task demonstrates a recurring cost. Full reflection
is not a proposed change to Lean or to all conaled interpretations.

## Which equality is being reflected?

**Literature.** [Angiuli, Hou and Harper, CSL 2018](https://drops.dagstuhl.de/storage/00lipics/lipics-vol119-csl2018/LIPIcs.CSL.2018.6/LIPIcs.CSL.2018.6.pdf),
§§2, 5.5 and Theorem 15, presents Cartesian cubical PER semantics with exact
equality pretypes and fibrant paths. Exact equality is uniquely inhabited
precisely when its endpoints are judgmentally equal. General exact equality
pretypes are not Kan: coercion in them would force uniqueness of identity
proofs in the underlying type. The paper's Boolean canonicity does not assert
decidable open conversion in the presence of reflection. Its special discrete
Kan case must not be generalized to arbitrary higher types.

The [RedPRL account](https://www.cs.cmu.edu/~rwh/papers/redprl/lfmtp18.pdf), §4,
likewise distinguishes proof-irrelevant exact equality from relevant paths.
In the [cooltt discussion](https://github.com/RedPRL/cooltt/discussions/186),
Sterling identifies face/cofibration constraints and ML module type equations
as controlled-reflection examples, while reporting automation problems with
full reflection. These are examples of restricted equality assumptions, not
a theorem that every restriction preserves decidable checking.

**Local distinctions.** Lean `Eq` is host propositional equality; an assumption
`h : a = b` can justify rewriting but does not make arbitrary a and b
kernel-definitionally equal. In
[ContextualModel](../../SquareKit/Internal/PathTransport/ContextualModel.lean),
`identity` is model data and `j_beta`/`j_sub` are host `HEq` laws about its
operations. In the cubical model,
[IdentityContraction](../../SquareKit/Internal/Cubical/IdentityContraction.lean)
uses a path with face information: `identityPath`, `identityFace` and
`identityIntro` retain that marking. This is neither an exact-equality pretype
nor Lean equality between endpoints. The marking supports the constructed
identity operations; it grants no reflection rule.

## One dependent task, three approaches

Use the existing coherence task: given a family P and composable paths
p : x → y and q : y → z, compare

```text
v = transport q (transport p u)
w = transport (p · q) u
η : Id (P z) v w
```

The author must form a dependent pair `(v, η)`, reindex it along σ and then τ,
and compare with reindexing along σ ∘ τ. A higher version also varies p by
h : p ⇒ p′ and retains the dependent action on h. This is a concrete task
from the [coherence comparison](dependent-coherence-comparison.md), not a new
claim that a native equality example supplies the higher version.

| Approach | What becomes easier | Remaining obligation or loss |
| --- | --- | --- |
| Full reflection for a separate exact equality | An exact proof equating two type presentations makes conversion usable throughout dependent terms | Construct that exact proof; validate reflection and substitution in every admitted model; arbitrary proof search can enter checking |
| Restricted conversion from admitted face constraints or certified presentation equations | A local checker can discharge a specified boundary/presentation equality | Prove its decision procedure sound in the constrained context and stable under substitution; no general η or higher-path collapse follows |
| Explicit path reasoning | η and the action on h remain observable in each model | Carry transports and their coherence, preferably through reusable author helpers; conversion alone cannot replace these witnesses |

Reflecting η itself requires identifying the higher identity with exact
equality, a stronger and inappropriate change for this task. Reflection of
*administrative type presentations* could remove casts without changing η,
but only when an interpretation validates that exact equation. In particular,
equal decoding does not imply equal presentation records.

## Existing support and the actual gap

**Source audit.** [LocalUniversesBoundary](../../Examples/LocalUniversesBoundary.lean)
retains the decoded-equality/presentation-inequality control and higher-witness
rejection tests. The [coherence report](dependent-coherence-comparison.md)
records `Transport.routes_agree` for the native two-substitution dependent pair.
Its native proof-irrelevant identity omits the nontrivial h observation. These
cases should be reused, not counted as new reflection evidence.

[ContextualOperations](../../SquareKit/Internal/DependentJudgments/ContextualOperations.lean)
proves `jBeta_valid` and `jSub_valid` from the full contextual model laws.
[InterpretationMaps](../../SquareKit/Internal/PathTransport/InterpretationMaps.lean)
already provides `ModelMap` and `j_substitution`. They address semantic coherence;
they are not a decision procedure or a generic source equality reflection rule.
The [cubical source semantics](../../SquareKit/Internal/Cubical/Judgments/Semantics.lean)
already has strict family-substitution equalities. Adding those equalities
again under a new interface would not repair generated-source annotation costs.

The required interpretation for a restricted rule must map its source context,
family, terms and local equality assumption to the corresponding target data;
prove the inferred conversion valid; and commute with substitution, including
substitution that changes which face assumptions hold. Composition must retain
the proof of that rule's admissibility, not merely its conclusion in one model.
Higher paths map separately, with endpoint, composition and dependent-action
comparisons. Reflection back to the source needs a further theorem.

Completed [#409](counted-stack-contracts.md) and
[#410](structural-canonicity-controls.md) distinguish observation/evaluation
contracts. They supply neither the dependent restricted-conversion procedure
nor evidence for changing this task's equality. Compared with
[#407](algebra-and-program-specification.md), the new decision here concerns
exactly which administrative equations can be automated while η and h remain
observable.

## Decision and successor conditions

Defer full reflection and a new exact-equality universe. Existing coherence
machinery suffices to express the task; the unresolved question is whether a
restricted checker reduces author obligations without excluding intended
models. Do not create another generic equality taxonomy implementation.

A bounded successor under #289/#235, coordinated with #399, should select one
recurring generated-source type-presentation obligation from the existing
two-substitution task. Compare the current helper route with a proof-producing
checker for that exact obligation. Require substitution stability, rejection
of the existing equal-decoding/unequal-presentation case, and preservation of
the independent higher observation. Measure repeated author work on a second
use of the dependent task; abandon the checker if the same helper proof already
solves both uses without extra setup. Face constraints are an alternative only
if they express the selected obligation, not a mandatory cubical retrofit.

This proposal preserves direct ordinary Lean clients and does not alter the
kernel. No formal implementation or new build was performed for this report.
A later implementation must pass statement review, checked specializations,
the README build/proof audit and independent review. Claiming automation gains
requires the matched author evidence, not merely fewer casts in a demonstration.
