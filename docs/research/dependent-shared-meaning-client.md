# A dependent client with shared proof and execution meaning

Issue [#356](https://github.com/VladimirMarko/conaled/issues/356) connects the
[#344 dependent translation](dependent-theory-maps.md) with the
[#343 capabilities](progressive-institution-capabilities.md). The public worked
case is `Examples/DependentPairSharedClient.lean`. This report records the
bounded specification, checked connections, and remaining scope.

## Independent specification

The context has one natural-number variable. Set `B(k) = Fin(k + 2)`,
`s(n) = n + 1`, `d(n) = 2*n`, and select `t(n) = n + 1 : B(s(n))`.
The source term projects the second component of the dependent pair
`pair N B (s n) (t n)`. Its semantic result retains both the dependency index
and the chosen component, as a packet `(k : Nat) × Fin(k + 2)`.

First substitute `n := s(k)`, then `k := d(m)`. At `m = 2`, the index used
inside the pair is 5, its first component is 6, and its selected second
component is **6 : Fin 8**. `answer` states `(6, 6 : Fin 8)` independently
of the proof and code compilers. `wrongAnswer` chooses `(6, 0 : Fin 8)`.
It has the same index and an inhabited fiber, but fails the selected-result
contract. No test of satisfiability alone can distinguish these outcomes.

The bounded grammar includes variables, successor, doubling, pair construction,
and dependent second projection. It admits arbitrary finite index expressions
built from those operations. It does not include arbitrary contexts, J, or
arbitrary raw assumptions. This restriction was chosen before defining its
semantic model and code compiler; it is not a restriction of the existing
native pair interfaces.

## What is connected

`DependentBranchSemantics.Model` supplies an operation for each primitive rule,
consuming the actual selected premise values. `TheoryMap.LocalMeaning` compares
the interpretation of each actual rule certificate with the source operation.
`interpret_transport` derives preservation for whole derivations. The premise
compatibility hypothesis and local laws are inputs; a whole-proof commuting
law is not an input.

The client applies that fold in three ways:

1. `SharedTyping.nativeModel` builds actual native dependent typing derivations
   from the actual typed premise derivations. Pair and projection helpers consume
   their child proofs. `native_translate` preserves this retained native proof.
2. `SharedModel.model` computes natural numbers and selected dependent packets.
   Its local laws use projection at the source and dependent case elimination
   at the target. `meaning_expected` checks every closed bounded proof against
   the separately defined mathematical specification.
3. `SharedCode.codeModel` builds an executable code tree. Its evaluator performs
   arithmetic, pair construction and case analysis. Local compiler soundness
   yields `compileCode_sound`; local certificate compatibility yields
   `compileCode_translate`.

A bounded phase pass replays the bounded proof skeleton. The actual raw
translation is **G**, which changes pair into `pack` and dependent projection
into a `split` expression with its dependent motive. `targetProof` calls the
existing `fullG` compiler on the native proof retained as provenance.
`two_stages_native_certificates` identifies the result with the existing genuine
F/G administrative certificate composition followed by erasure. Thus bounded
phase replay is not being presented as a nonidentity raw syntax transformation.

`Code.quote_G` checks the raw syntax change on the independently executable
code. `compiled_target_quote` proves that compiled code quotes exactly the
term in the translated judgment. The general `compiled_image` theorem combines:

- equality of the target proof with actual `fullG` compilation;
- equality of executable-code quotation with the translated raw term;
- equality of code evaluation with the selected source meaning.

These claims share the same bounded derivation. They are stronger than assigning
an unrelated program the desired numerical answer. They do not interpret all
possible elimination-calculus proof trees: the target semantic interface is the
compiled image with retained bounded provenance.

## Composition, substitutions and equality

The institution setting uses environments as models, bounded judgments as
sentences, and the selected natural number or dependent packet as evidence.
Its connection preserves that evidence. `Compatible` combines the proof map
and executable realization map over this one connection. `joint_commutes` and
`two_stage_joint` follow from the local folds and compiler soundness.
`selected_joint` exercises the composed capability at the concrete client.
The existing runtime square is reused through `RealizationMap.square`; its
composition equation is checked.

Identity and two-stage composition are checked for both bounded proof
transport and executable code translation. In addition, the native adapter
connects actual F/G certificate composition. These are separate claims:
equality of a bounded phase skeleton alone would not establish the raw claim.

`successorSubTyped` and the existing `tauTyped` justify the two native dependent
substitutions. `twiceTyped` has the resulting dependent judgment, including its
substituted type; `compiledTwiceTyped` applies actual fullG to it. Raw substitution
coherence and `substituted_target_quote` connect this judgment to the executable
program's quotation. `Code.substitute_run` proves execution in the substituted
environment. Both substitutions change the concrete result, from index 3 to 4
to 6. `substituted_execution` and `target_execution` prove the final selected
packet through compiler soundness and the independent specification.

No equality between the native proof tree produced by substitution and the
canonical final bounded proof tree is asserted. They inhabit the same dependent
judgment. Semantic claims are about the bounded image and its executable term;
this work does not assign proof-irrelevant semantics to arbitrary native trees.

All comparison theorems in this experiment use Lean propositional equality of
selected semantic values, code, or derivations as indicated by their types.
Native object-language typing and equality remain distinct judgments. No global
decidable equality or equality reflection is required. Semantic clients observe
the packet's index and selected component. Compiler clients may inspect code and
raw syntax under the separate quotation and typing contracts. This client does
not introduce another opaque semantic-boundary API.

## Comparison of routes and obligation counts

These are counts of rule families in the checked definitions, not measurements
of author time. The grammar has five `Step` constructors. Each model or compiler
rule definition covers those five families; variable has no premises and the
other families have one. Existing native helpers contain the underlying
context, family and component derivations.

| Route | Setup for this client | Recurring obligation |
|---|---|---|
| Native | Existing fullG certificates, typed substitutions and selected native pair client; five local typing adapters | Supply native typing for a new operation and any required compiler certificate |
| Separate capabilities | Five semantic operations and local preservation cases; five code emitters and local soundness cases; quotation cases for the code grammar | Keep proof and runtime comparisons aligned manually |
| Shared meaning | Reuses those operations and laws; setting, connection, proof map, realization map, and `Compatible` wrappers | New primitive operations still need local typing, meaning, code and quotation laws; whole-tree joint preservation is reused |

`interpret_transport` removes a separate whole-derivation preservation proof
for each suitable local model. Index expressions of greater depth require no
new primitive laws. The shared capability does not discharge the five local
semantic obligations or discover a compiler. Its benefit here is that composition
uses one selected evidence comparison and that the code/proof seam is explicit.
There is no measured agent- or human-productivity claim; #357 owns the comparative
authoring exercise. Existing native clients remain available.

## Statement review and checked applications

The initial mathematical obligation was to connect a computed selected packet
to the actual native translation. The numerical result by itself reduced easily;
the missing connection was local interpretation plus native typing and code
quotation. The development retained that expected result while adding those
connections. Intermediate checked cases exercised the model, code compiler,
quotation and substitutions before the final joint case.

- The generic local theorem quantifies over selected premise values and actual
  certificates. It is specialized to native derivations, semantic packets, and
  code. It does not assume the conclusion it later proves.
- Closed bounded proofs use empty hypotheses. Native typing consumes premise
  proofs, rather than recreating unrelated fixed proofs at each node.
- Code soundness compares an executable recursive evaluator with an independent
  semantic fold. Code quotation additionally establishes the actual G term.
- `answer` fixes both the dependent index and payload. `wrong_selection` and
  `execution_rejects_wrong_selection` reject the same-index alternative.
- Native typing, fragment semantics, and executable evaluation have distinct
  theorem statements. There is no reverse compiler, reflection, general raw
  operational adequacy, or full-calculus soundness theorem.

The entrypoint imports the complete client, bringing all helpers into routine
build and exhaustive proof audit. Candidate acceptance and independent review
are recorded by the orchestration; focused builds are development evidence only.

## Remaining direction

#289/#290 retain general dependent semantics, selected higher identity witnesses,
and relational or wider-logic interpretation questions. This Nat/Fin client does
not exercise path distinctions. #355's Id/J certificate census is not a semantic
model and is not treated as one here. Extending this experiment to that fragment
requires actual local interpretation laws for its additional constructors.
#235 retains integration across traditions. #357 should compare authoring costs
using the explicit local/global distinction above. #107 remains paused,
#108 unselected, and #260 inactive.
