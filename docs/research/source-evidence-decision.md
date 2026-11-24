# Source evidence: bounded contract decision

This is the decision packet for
[#699](https://github.com/VladimirMarko/conaled/issues/699) and the conditional
implementation in [#489](https://github.com/VladimirMarko/conaled/issues/489).
It reuses the completed [#490 comparison](compiler-evidence-comparison.md) and
[#492 MMT study](mmt-compiler-evidence.md). It adds a concrete proposed fragment,
source-to-artifact obligations and implementation order. Production adoption
still requires the owner's decision. No universal evidence API is selected.

## Proposed first slice

Use affine expressions over residues modulo 16: variables, literals, addition,
multiplication by a literal coefficient in 0–15, unit, products, projections and
nonrecursive let binding. State updates are simultaneous. Source expressions
may calculate with nonnegative integers and take a final remainder; the residue
interpretation may reduce intermediate results. The advertised observation is
the canonical residue result, not unreduced intermediate integers.

This is narrower than the general polynomial fragment considered in the
[independent assessment brief](source-evidence-decision/brief.md). Variable-by-variable
multiplication is excluded from the first implementation, because the selected
clients need only constant multiplication and existing word circuits supply
addition. This is a scheduling boundary, not a mathematical limitation or a
rejection of the broader polynomial route.

There are two original-source entry points with the same specified fragment:

- An explicit typed source term, whose evaluator defines its source meaning.
  This remains usable without a quotation layer.
- A named Lean function with a finite, pinned definition dependency closure and
  an ordinary kernel-checked theorem relating that exact function to the selected
  explicit term on admitted arguments. A caller may prove correspondence for a
  semantically equal spelling; syntactic identity is sufficient but not required.

The second entry point is a proposed bounded adapter, not a claim of arbitrary
Lean quotation. Function arguments are the ordered top-level telescope; object
terms use typed variable indices and capture-avoiding let substitution. A closed
coefficient is a parameter of the instance, not an untracked global. Transparent
helper definitions must expand into the fragment, or the caller must supply a
checked correspondence to a supported term with an explicit assumption account.
Opaque computational dependencies, recursion, higher-order values, effects,
variable multiplication and unsupported primitives are refused by this slice.
Broader mathematical interpretations keep their separate contracts.

### Pure client

For `0 ≤ q < 16`, use

```text
D₃(q) = (q, 3*q mod16)
E(x,y) = x
```

Observe both output components and retain these particular functions as data.
Require `E(D₃(q))=q` for every admitted q, and `D₃(E(x,y))=(x,y)` precisely when
`0≤x,y<16` and `y=3*x mod16`. At q=1 the output is (1,3); q=15 gives (15,13).
The alternate spelling `(q,(q+q+q) mod16)` must be accepted after correspondence
is checked. A theorem that merely asserts existence of some decoder is insufficient.

### Initialized state client

Reuse #490's program without weakening its observations:

```text
source initial = (0,0)
admitted input d ∈ {0,1,2,3}
x' = (x+d) mod16
y' = (y+3*d) mod16
output = y'

target initial q = 0
q' = (q+d) mod16
output = 3*q' mod16
R((x,y),q) means (x,y)=D₃(q)
```

Require related initialization and, for every related state pair and admitted
input, equal outputs and related successors. Output is observed after the
simultaneous update. For inputs [3,3], the outputs are [9,2] and the final source
state is (6,2), recovered from q=6. The whole state relation is retained even
though the emitted output is only y'. The claim does not recover arbitrary
unreachable source pairs: (0,1) fails the invariant.

Coefficient 3, modulus 16, input domain, output phase, initialization, primitive
meaning and selected converters are instance parameters. A change to coefficient
5 needs fresh evidence or an explicitly quantified theorem instantiated at 5;
the c=3 receipt cannot silently authorize it. The first acceptance examples use
c=3. Other literal coefficients within the fragment need their own instances.

## Existing implementation and exact gaps

The source pin for this assessment is
`0d3865b344940510428e01f6907cb03dedbfe256`, with the repository's pinned Lean and
Mathlib. The following are inspected existing Lean declarations. Their earlier
integrated checking is retained; this documentation task does not claim a new
formal implementation of the proposed bridge.

| Existing path | Reuse and boundary |
| --- | --- |
| [FirstOrder](../../FirstOrder.lean), `Term`, `eval`, `compile_sound` | Typed variables, products, let and a parameterized primitive vocabulary. Primitive meaning and `Sound` laws are explicit. No arbitrary host function is identified with a term automatically. |
| [FirstOrderSubstitution](../../SquareKit/FirstOrderSubstitution.lean), `eval_subst` | Capture-avoiding simultaneous substitution under lets. Applies to open contexts, not just the selected closed examples. |
| [ReactiveCompiler](../../SquareKit/ReactiveCompiler.lean), `map_sound`, `initial_sound`, `step_sound`, `run_sound` | Compile explicit pure and initialized source terms to stored target morphisms. This preserves the specified source state representation; compression needs an additional relation. |
| [Progress.Feedback.run_related](../../Applications/Progress/Reactive.lean) | General output-list and final-state relation theorem. Instantiate its input relation with admitted-input equality and its state relation with R; do not repeat trace induction in each evidence producer. |
| [RegionalAdmission](../../Applications/FRP/RegionalAdmission.lean) and [RegionalSelection](../../Applications/FRP/RegionalSelection.lean) | Precedents for separate semantic admission, resource eligibility and selection. Their existing `Realization` is specific to Bool/Input clients, not a generic record for these integers. |
| [GraphTranslationValidator](../../SquareKit/Internal/GraphTranslationValidator.lean), `check_sound`, `Validated.source` | A genuine checked source/artifact precedent with exact primitive records and a different accepted proof body. Its graph proposition language does not establish arithmetic correspondence or finite-table checker soundness. Host record lookup and installation remain separate. |
| [Words](../../Applications/Circuits/Words.lean), `decode_encode`, `encode_decode`, `add_correct` | Actual least-significant-bit-first representation, arbitrary-width modular addition, and inverse conversions. Width four fits the selected fragment; coefficient multiplication can expand to repeated addition. |
| [Circuit](../../Applications/Circuits/Syntax.lean), `interpret_compile`, and [execute_correct](../../Applications/Circuits/Execution.lean) | Inspectable target constructors and executable meaning. They supply a first artifact/execution target without requiring a new Wasm backend. |

The lowering must map each residue ground type to `Words.shape 4`, extend that
map over products and ordered contexts, and establish the primitive and let
clauses at those changed types. `compile_sound` for one ground interpretation
does not itself prove this change of ground representation.

The missing work is the chosen source-declaration correspondence, arithmetic
interpretation/lowering connection, whole selected source/artifact package,
and finite-checker soundness. None is supplied merely by importing the rows above.
The initial artifact should be an actual typed `Circuit`, with a selected seed
and body for the state client, consumed by `Circuit.execute`. Byte serialization,
foreign loading and Wasm integration are outside this first slice; later
consumers must establish their own exact artifact connection.

## One semantic contract, distinct evidence routes

The contract is expressed by the following obligations, not by a mandatory
cross-language record. For each instance, retain the original source S, ordered
parameters θ, admitted-input predicate U, explicit typed source e, selected
interpretation route I, artifact A, and executable converter data E/D.

1. **Original source correspondence:** S and e have the same specified meaning
   on admitted arguments under θ. For a native declaration, this must be a
   kernel-checked theorem about that exact declaration and term. For an explicit
   AST source, its documented evaluator is the original meaning. An external
   exporter needs its own adequate connection; a certificate for its output alone
   does not establish correspondence with its input.
2. **Pure preservation:** decoding the selected artifact's output gives exactly
   S's pair result for each admitted q, with the stated E/D recovery laws.
3. **State preservation:** initialization satisfies R; each U-admitted step
   preserves outputs and R using the selected artifact and decoder. The generic
   finite-trace theorem then preserves outputs and recoverable final states.
4. **Artifact association:** the very artifact and primitive meanings consumed
   by the evaluator are those in the checked conclusion. Data equality or a
   proved correspondence to the consumed representation is required. Names,
   hashes, source types and successful process exits alone do not prove this.

Parameters, source/dependency contents, primitive meanings, input/output contract,
converter contents, artifact contents, interpretation and evidence-format versions
belong to one immutable instance. In-memory indexed terms can carry these identities
directly. A host receipt can additionally record digests for lookup, but semantic
checking still relates the actual objects. Cache reuse must re-establish the
instance identity; changed bytes may also be accepted with fresh correspondence.
A running state stays indexed by its accepted executor and representation. A new
receipt cannot cast old state to a new representation; this first slice can start
a new initialized run, while migration requires an explicit proved conversion.

### A. Native correspondence and local proofs

The author supplies the ordinary function-to-term theorem when starting from a
Lean declaration, plus the invariant, initialization, selected-converter and
local-step proofs. The proof checker verifies their full types at the selected
source/artifact instance, and the implementation composes them with generic
compiler and continuation theorems. A theorem about another program, coefficient,
decoder or premise does not inhabit that type.

This route can state uniform results over admitted coefficient parameters and
reuse ordinary arithmetic lemmas. It does not require a finite relation table.
The new adapter must check the original function's actual definition context;
looking up a theorem name and assuming its type is the desired one is insufficient.
An explicit typed-source caller avoids that adapter. The verification dependencies
are Lean's kernel and audited theorem dependencies, plus the stated host boundary
for environment inspection and execution. No new axiom or arbitrary reflection
principle is proposed.

### B. Finite evidence with a separately proved checker

The producer supplies a pure table covering every admitted q and a finite
relation of source/target states. A small total checker must verify domains,
initial membership, agreement with the selected D, output agreement, and closure
under every admitted d. Require exactly one row for every canonical q, with its
source state D(q), and reject out-of-domain or duplicate-key rows. Check all
sixteen pure inputs separately. This explicit coverage establishes the advertised
local law on the entire graph R, not merely a closed reachable subrelation. For the selected relation, sixteen triples and four
inputs give 64 edges. It must evaluate the actual source and artifact objects,
not trust outputs copied into a table. D and E remain selected executable data.
The source-to-term connection in obligation 1 is still required; finite checking
of an exported AST cannot certify an unrelated native declaration.

Prove `check = accepted` implies obligations 2–4 under obligation 1, without an
assumed semantic-correctness field in the certificate. Derive the fixed E/D round trips from the shared definitions
and invariant where possible, rather than repeating proof fields per caller.
Establish the checker on
the complete finite domains, including binding and type validation. Kernel-checked
reduction of a concrete acceptance equation is one implementation mechanism;
compiled checker execution needs its own declared execution trust boundary.
No arbitrary external byte parser is required in the first in-memory format.

This is a genuinely different evidence-producing route: finite data and exhaustive
checking replace author-supplied invariant proofs. Its soundness proof may be
written in Lean without making Lean proof terms the certificate author's language.
The existing Python checker is only a diagnostic precursor and cannot be promoted
into production by wrapping its Boolean answer in a native record.

### Alternatives on the same clients

| Route | What it can establish here | Why it is or is not the first implementation |
| --- | --- | --- |
| Native local proofs | Exact same source, converter, pure and transition equations; possible uniform coefficient theorem | Recommend as one accepted producer, with a real original-source bridge. General Lean imports remain unsupported. |
| Proved finite table checker | Same selected equations and reachable-state simulation on the finite domains | Recommend as a second producer of the same bounded guarantees. Formal checker soundness remains work; finite coverage is not suitable for an unbounded-domain claim. |
| Symbolic polynomial certificate | The selected affine identities and the broader polynomial identities from #490 | Mathematically viable. The current Python normalizer is not soundness-proved, and still needs separate source, initialization, bounds and artifact checks. Defer another format until symbolic parameter reuse is a concrete requirement. |
| Theory-indexed interpretations, optional MMT publication | Can organize the same requirements and composed judgments without imposing the compiler host | Retain as a complementary organization. #492's arithmetic/source adequacy and complete composed executable route were not established; its failed composite attempt is an encoding result, not mathematical refutation. Publication adds no missing source theorem by itself. |
| Common extensible proof language | Could encode both symbolic proofs and checked finite results | No additional shared producer requirement here establishes a benefit over A/B; its parser, extension semantics and adequacy would be new obligations. Defer universal adoption. |
| Hash/name/type-only acceptance | Identifies selected data or type shape | Reject as a semantic gate: the wrong-output mutation remains well formed, and rebinding its digest does not prove the transition equation. |

The first five are not ranked by measured productivity. A/B offer a bounded
comparison of distinct author obligations while reusing one continuation proof.
Native setup includes local lemmas and theorem application; table setup includes
complete finite evidence and regeneration after changed domains. Both need source
binding and artifact maintenance. A normalizer offers symbolic reuse but adds its
own proof and diagnostic obligations. Larger finite domains may reverse practical
costs; no author-effort experiment is claimed here.

## Compiler host and verification mechanism

A compiler reimplemented in Rust or OCaml can preserve this programmer contract:
it may still submit native proofs to Lean and produce finite data for an independent
checker. Keep the same source meaning, supported evidence capabilities, parameters,
selected witnesses and actual artifact association. The compiler host does not
select the source logic. Reimplementing the checker requires a proved refinement,
a justified extraction/execution connection, or an explicit additional trust
assumption; tests alone do not transfer its soundness theorem. Changing verification
foundations requires justified interpretations of the previously accepted judgments
and witnesses, not just a compatible wire format. A future external serializer and
loader must connect their actual payload to the same checked objects. Mathematical
preservation supplies no empirical evidence that physical hardware obeys its model.

## Two nonidentity interpretations and selected data

The first map sends integer expressions and congruence modulo 16 to residue
expressions/equality in `Z/16Z`. It maps literals and addition, and interprets
literal multiplication accordingly. It loses distinctions such as 0 and 16.
Require evaluation compatibility for every valuation of the open context and
compatibility with simultaneous substitution, including under lets.

The second map sends residues to canonical four-bit values and then to the
existing Boolean word representation. Its addition is `Words.add 4`; constant
multiplication is a selected finite sequence of additions. Require interpretation
of each primitive and use `encode_decode`/`decode_encode` for recovery. Composing
these obligations gives agreement between direct integer evaluation followed by
remainder and the selected circuit execution, for the same context and parameters.
The existing code supplies some component theorems, not this entire new composition.

Transport D componentwise through those same maps. The selected bit-level decoder
must decode to D₃(q), not merely have the same range or be one possible inverse.
Likewise preserve E and the relation R. Equality of final observations and selected
converter values is required; equality of proof objects or reflection of all
integer propositions is not. A diagram for these specific relations is:

```text
original declaration/explicit source --correspondence--> typed affine source
       |                                                  |
       | admitted integer meaning                         | congruence interpretation
       v                                                  v
canonical residue observations <---------------------- residue expression
       ^                                                  |
       | selected encode/decode laws                      | word/circuit lowering
       +----------------------------------------- actual typed Circuit
```

Exact integer temporary bounds remain separate. The old Python source evaluates
with six-bit exact temporaries on its fixed expressions; that does not describe
the four-bit modular circuit. Ring equality cannot prove integer order, absence
of exact intermediate overflow, latency, or physical device behavior. A mathematical
interpretation of a noncomputable operation is not ruled out universally, but the
requested executable fragment rejects such a dependency without an effective
realization. No fixed hierarchy of all possible realizations is being adopted.

## Acceptance and rejection cases for both routes

| Change/request | Required outcome and concrete discriminator |
| --- | --- |
| Original source coefficient 3 becomes 5 with old evidence | Reject stale association. Even after rebinding identities, D₃ is wrong at q=1: (1,3) versus (1,5). Fresh uniform/instance evidence must justify any changed instance. |
| Modulus 16 becomes 8 | Reject stale association and unsupported first-slice modulus. q=3 distinguishes the decoder's second component: 9 versus 1. A theorem for 16 is not a theorem for 8. |
| Artifact emits 2*q' | Reject semantic correspondence: from q=0,d=1 source emits 3 but target emits 2. A fresh hash does not repair it. |
| Initial source becomes (0,1), target stays 0 | Reject R at initialization even if a supplied step lemma is otherwise valid. |
| Request recovery of every integer or every source pair | Reject the claim: 0 and 16 have the same quotient image; D₃(E(0,1))=(0,0). Preserve the advertised domain rather than silently weakening it. |
| Unsupported oracle, saturation, effects or variable multiplication | Return unsupported for this source fragment; do not run it in the ordinary fallback. New semantics require a new admission contract. |
| Wrong binder/parameter order | Reject source correspondence unless independently proved. For `x+3*d`, x=1,d=0 yields 1, whereas exchanging roles yields 3. Binder labels alone have no semantic significance. |
| Missing/replaced decoder | Refuse the selected-witness claim even if some decoder exists or outputs alone agree. D₅ at q=1 does not recover the selected state. |
| Encoder replaced by constant zero | Reject `E(D(q))=q`, already at q=1, even if output traces happen to agree. |
| Input d=16 | Reject before the transition. A raw numeral is not an admitted d merely because its residue is zero. |
| Different source spelling `q+q+q` | Accept fresh checked correspondence to 3*q on the admitted domain; original bytes and receipt may differ. Both routes retain the exact pair observation. |
| Missing resource/latency evidence | Semantic admission may pass. No total-memory, latency, or speed claim follows from four stored bits. Preserve a supported baseline and the optimization diagnostic. |
| Unsupported evidence format or missing proof | Return unsupported/missing evidence, not mathematical impossibility. A supported original source can use its checked uncompressed baseline. |

Native route tests must exercise actual expected theorem types and checked
source functions. Finite route tests must exercise the proved checker, including
omitted relation rows, forged outputs and malformed typed inputs. The current
Python diagnostics establish neither of those production gates.

## Executed evidence and independent assessment

[The diagnostic](../../experiments/source-evidence-decision/probe.py) replays the
unchanged #490 probe and checks all sixteen pure inputs, the alternate syntax,
selected encoder recovery, coefficient-5 counterexamples, an unsupported primitive,
and two failed overstrong recovery claims. [The retained result](source-evidence-decision/probe-results.json)
records both source hashes. It retains #490's 341 traces per route, 1,280 finite
interpretation comparisons, and mutation/fallback controls. These are executed
Python assertions and source inspection, not kernel proofs of A, B or the full
lowering. Arbitrary-length state preservation relies on the stated step contract
and the existing generic continuation theorem, not bounded testing.

Run `direnv exec . python3 experiments/source-evidence-decision/probe.py`.
The output is deterministic at the pinned probe sources; compare it with the
retained JSON. No compiler or dependency pin changes are part of this task.
The exact native/finite production comparison remains the proposed #489 work.

Three independent assessments were completed before synthesis:
[contract](source-evidence-decision/contract.md),
[implementation/use](source-evidence-decision/implementation.md), and
[alternatives](source-evidence-decision/alternatives.md). Their initial texts are
preserved verbatim; the contract report appends a separately saved circuit-source
supplement. Each inspected the pinned sources without reading the others or a
coordinator verdict. All had the shared brief and published prior recommendations;
this is independence of assessment, not blindness to prior evidence or model
diversity. A later factual circuit-source pointer was disclosed in their reports.
No assessor ran a build or experiment; the root ran the diagnostic above.

All three favored the same bounded semantic contract with two distinct evidence
routes. Their agreement does not establish the proposed checker or bridge. The
following premises were checked against the code and reconciled:

- **Coverage:** the old finite checker proves initialization/closure for its
  submitted relation. Decoder agreement alone gives inclusion in R, not total
  coverage of R. This machine's d=1 can force reachability of all q, but relying
  on that argument would require its own proof. The proposed checker explicitly
  checks all sixteen decoder rows and all pure inputs. It therefore promises
  the same universal local contract as route A without a hidden reachability lemma.
- **Target scope:** existing word laws cover inverse conversion and modular addition,
  not arbitrary multiplication lowering. The first production fragment is explicitly
  narrowed to affine expressions; constant multiplication uses repeated addition.
  The original broader brief and assessments are retained. General polynomial
  semantics and alternate evidence formats are not declared impossible.
- **Source and artifact:** neither the graph validator nor the Bool-specific
  regional record is the missing arithmetic bridge. The implementation spec uses
  their particular precedents and the generic `run_related`, while requiring
  source correspondence and exact selected artifact consumption as new work.
- **Witnesses and running state:** fixed E/D equations can be derived once; finite
  data must still retain the selected operations. Source/representation changes
  cannot relabel live state. The packet now makes both boundaries explicit.
- **Symbolic alternative:** it fits both chosen programs. Its coefficient normalizer
  can still reject a valid finite-function equality: the paper example
  `8*q*q mod16 = 8*q mod16` follows because q(q−1) is even, while polynomial
  coefficient maps differ. This example is outside the narrowed affine slice;
  it remains a discriminator for a future broader symbolic format. No new proof
  or execution of that separator is claimed.

No assessor identified a missing mathematical fact that requires another general
research programme before the owner can choose this bounded slice. Formal checker,
source and lowering proofs remain implementation obligations, with no productivity
ranking established. The ordinary independent Standards/Spec reviews assess this
packet separately from these three design perspectives.

## Conditional implementation and owner decision

If the owner selects this packet, #489 can proceed in these bounded steps:

1. Define the affine source/primitive instance and the immutable source/parameter/
   artifact contract. Keep existing `Term` and direct clients usable. Add the
   two specified source programs and their checked native function-to-term
   correspondences, including different syntax, capture-avoiding binding and
   parameter rejection cases.
2. Construct the selected typed circuits and original-to-residue-to-word comparison,
   consuming the existing word/circuit laws. Keep actual seed/body and selected
   E/D in the conclusion. Establish pure and local transition contracts and reuse
   `run_related` for initialized finite traces.
3. Add a separate finite-data checker with proved soundness and checked acceptance
   equations for these same instances. Connect its conclusion to the same compiler
   and continuation results as native proofs. No semantic proof field may stand
   in for checking the supplied certificate.
4. Exercise both producers through actual artifact consumption and all applicable
   controls above. Retain supported-source fallback and diagnostics; do not make
   one producer or a quotation layer mandatory for existing clients. Run the
   integrated build/audit and independent Standards/Spec review.

Completion requires both distinct evidence producers and the same selected
semantic contract, not only an inventory or a paper checker. A serialized importer,
external proof-language framework, general variable multiplication, native runtime
verification, Wasm emission and author-productivity trial are not prerequisites.
A later consumer must name any additional boundary it needs.

Proposed owner decision, ready to accept or amend:

> Approve #489 for the affine modulo-16 fragment and the pure D₃ and initialized
> two-register clients specified here. Require both native correspondence proofs
> and a separately proved finite-data checker to establish the same original-source,
> selected-converter and actual typed-circuit contracts. Use the existing circuit
> evaluator as the first execution target, retain direct explicit-source clients,
> and keep resource claims separate. Native Lean proofs are one supported route,
> not the universal source/evidence interface. No broader importer, proof language
> or framework is adopted by this decision.

No further general architecture review is needed to make that choice. The remaining
owner choice is whether to authorize this fragment and these two evidence capabilities.
If the owner instead requires a foreign surface language as the original source,
the single next discriminator is that language's bounded exporter/interpretation
contract for these two programs; choose it before starting its production bridge.
#489 stays `needs-triage` until the decision is recorded. #699 completes on this
reviewed preparation, without silently making the decision itself.
