# Evidence routes for backend admission

Recommend a bounded implementation comparison with a semantic contract shared
by a native proof adapter and a separately proved finite-certificate checker.
Keep their author interfaces distinct. The backend should consume their
justified conclusions about the selected program, interpretation and artifact,
not require a particular compiler implementation language. This is a proposal
for the owner of [#490](https://github.com/VladimirMarko/conaled/issues/490),
not an adopted API, framework or universal proof language. Production work in
[#489](https://github.com/VladimirMarko/conaled/issues/489) remains deferred
until the owner records the contract and supported source fragment.

The comparison adds a [replayable diagnostic probe](../../experiments/compiler-evidence/probe.py)
to the required [MMT study](mmt-compiler-evidence.md). Two different checkers
feed the same executable admission and selection functions: one checks symbolic
polynomial identities, the other checks a supplied finite simulation relation.
Both justify eliminating a state register that the specified baseline analysis
cannot eliminate. Neither Python checker is kernel verified. The mathematical
arguments, executed cases, and remaining proof obligations are distinguished
below. No existing Lean client, declaration, import, dependency or trust axiom
changes.

## Scope and evidence versions

Issue snapshot date: 2026-11-12, #490 updated `2026-11-12T01:56:38Z`, with the
owner's required-input comment; #489 updated `2026-11-12T01:18:49Z`; #492
updated `2026-11-12T01:56:39Z`. Repository input is
`51b6e507579acc45ead0fced6489fb5b8d640a63`, which publishes #492. Full issue
snapshots and validation receipts are retained outside the source diff in the
implementation handoff. The source file above is the durable probe artifact.

| Evidence | Version, inspected scope and limitation |
|---|---|
| Existing repository contracts | Input commit above; source inspection of the named declarations below. Their previous checking status is inherited, not a new check of this probe |
| MMT | #492's pinned source `71814b0fec9c1f2dbe7d677ab65bb433bc90ec08`, executed release 27.0.0, pinned LF/LATIN archives and recorded failures. No rerun or extension of its whole study |
| Rabe and Kohlhase | [*A Scalable Module System*](https://kwarc.info/people/frabe/Research/mmt.pdf), preprint 17 December 2012, definitions 30/32, theorems 34/48; independently reopened for this comparison |
| CompCert | [Commented development 3.18, 31 August 2026](https://compcert.org/doc/index.html), especially [Allocproof](https://compcert.org/doc/html/compcert.backend.Allocproof.html). Source/document inspection, no build or import |
| Lean choice | [Lean v4.35.0, `Init/Classical.lean`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Classical.lean), `axiomOfChoice`, noncomputable `choose`; no new use in this change |
| Quantum semantics | [SQIR `134fb942265091baa3e3972f78f72da41827351f`, `DensitySem.v`](https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/SQIR/DensitySem.v), and [CoqQ v1, 22 July 2022](https://arxiv.org/abs/2207.11350v1). Inspected sources, not rebuilt |
| Oracle interpretation | Ahman and Bauer, [*Sheaves as oracle computations*, arXiv:2602.22135v2, 28 April 2026](https://arxiv.org/html/2602.22135v2), §§2–4. Relevance assessment only |

## The contract precedes the evidence representation

Four choices must remain distinguishable. A compiler has an implementation
language. A programmer uses a source language with judgments and meaning. A
backend supplies operations and observations with requirements for the requested
guarantee. An evidence route supplies checking and interpretation connecting the
source judgment to that guarantee. Coincidence of implementation and source
language establishes none of these connections by itself.

The proposed semantic admission claim for a stateful source `P`, target `A`,
input predicate `U`, observation relation `O` and selected state relation `R`
has the following content. Its presentation is mathematical, not a proposed
mandatory record:

1. The initial source and target states satisfy `R`.
2. For every related pair of states and every input satisfying `U`, the
   source and target transitions produce `O`-related outputs and `R`-related
   successor states.
3. The selected executable encoder/decoder, if required, realizes that relation
   on the admitted states. Existence of another converter is insufficient.
4. The interpreted artifact denotes the target transition in item 2, including
   primitive meanings, widths, parameters and the observation convention.

These hypotheses yield finite-trace preservation by induction. Input admission
and the next-state relation supply the induction hypotheses; output relations
compose pointwise. This is one generic continuation argument for all evidence
routes. Different schedules can satisfy it: more general transitions may use
stuttering simulations, causal relations or approximation contracts instead.
No source evaluation strategy is imposed on every backend by this example.

Requirements for bounded storage, latency, progress or probabilistic delivery
are additional conclusions under their own models. Ranking orders candidates
already eligible for the requested guarantees. It cannot manufacture a missing
semantic proof or decide arbitrary propositions. Runtime-varying premises need
sound executable guards or maintained invariants before an affected operation.
A changed parameter invalidates evidence indexed by its old value unless a
uniform theorem covers the change.

A mathematical backend need not have executable artifacts or physical hardware.
Keep these four questions separate:

| Question | Example of the additional obligation |
|---|---|
| Interpretation and preservation | Does this setting validate the used operations, principles and observations? |
| Artifact generation | Does the emitted description denote the selected target object? |
| Effective execution | Is there an executable realization, including the retained witness and input protocol? |
| Physical realization | Does a device implement the model within the stated error and timing assumptions? |

A noncomputable mathematical interpretation may answer the first question
without the last three. The supported structure and principles depend on the
interpretation. This does not select a philosophy in which the verifier's
foundation is determined by the hardware. An oracle or hypercomputational
execution assumption does not, by itself, grant a new deductive rule.

## Existing contracts to reuse

| Current construction | Reuse in a bounded implementation; remaining obligation |
|---|---|
| [`ReactiveCompiler.initial_sound`, `step_sound`, `run_sound`](../../SquareKit/ReactiveCompiler.lean) | Primitive soundness lifts to the explicit source seed/body and stored target morphisms. Preserve this direct client. A representation-changing relation and foreign source association need their own bridge |
| [`Regional.Realization`, `semantic_preservation`](../../Applications/FRP/RegionalAdmission.lean) | Selected state interpretation, initialization and local step proof feed `run_related`. Reuse the continuation theorem rather than asking each author for a trace induction |
| `Regional.assessAdmission`, `unknown_is_not_impossible` in the same module | Existing semantic admission can succeed while resource analysis is unsupported. Its finite catalog is not a checker for arbitrary foreign proofs |
| [`Selection.eligible`, `select`, `selected_execution`, `selected_continuation`](../../Applications/FRP/RegionalSelection.lean) | Eligibility and ranking are separate. State remains indexed by the chosen executor in `Session`. Changed evidence does not authorize casting live state to another representation |
| [`DependentTheoryMaps.OperationMap.act_subst`, `TheoryMap.transport`, `comp_transport`](../../SquareKit/DependentTheoryMaps.lean) | Reuse rule-local transport, substitution compatibility and composition where judgments fit. These results do not prove adequacy of a new arithmetic encoding or preservation of arbitrary dependent witnesses |
| [`GraphEmissionPure.ArtifactDenotes`, `emit_denotes`](../../SquareKit/Internal/GraphEmissionContract.lean) | Existing bounded emitter connects its concrete Lean expressions to declaration meaning. Its scope does not identify an arbitrary user declaration with an exported source |

These are source-inspected regression clients, not a claim that the proposed
Python formats already instantiate their Lean types. The [preservation inventory](preservation-contract-inventory.md)
retains other observation families and their stronger obligations. No module
boundary or ADR is changed by this report.

A primary implementation precedent for a separate validator is CompCert's
register allocation: `Allocproof` states structural checks and a forward
simulation theorem under its successful transformation relation. This supports
the distinction between producing a candidate and validating its particular
translation. It does not prove our checker or make its finite relation adequate
for every language. [CompCert 3.18, Allocproof](https://compcert.org/doc/html/compcert.backend.Allocproof.html).

## Stateful example and baseline

Retain #492's source without changing the observation to make compression easy.
States are `(x,y)` with `0≤x,y<16`; initialization is `(0,0)`; input is
`d∈{0,1,2,3}`. The simultaneous update and output are

```text
x′ = (x+d) mod 16
y′ = (y+3*d) mod 16
output = y′
```

The baseline is independent interval analysis and an eight-state-bit layout.
Its invariant `0≤x,y<16` admits `(0,1)`, which cannot be reconstructed from
`x=0` using `y=3*x mod16`. Thus those intervals do not justify this compression.
A stronger automatic relational analysis might establish it; no impossibility
of automatic discovery is claimed.

The programmer's invariant is `y=3*x mod16`. The selected decoder is
`D(q)=(q,3*q mod16)` and encoder is `E(x,y)=x`. The compressed artifact starts
at `q=0`, updates `q′=(q+d) mod16`, and emits `3*q′ mod16`. It stores four
state bits. `E(D(q))=q` for every canonical `q`, and `D(E(s))=s` for invariant
states only. This retains both source-state observations, not just the output.

In integers, the source sums are at most 18 and 24, and decoder multiplication
is at most 45. Six-bit exact temporaries suffice; the final values are reduced
modulo 16. A four-bit exact temporary violates this contract even where
four-bit *modular* arithmetic would yield the same final residue. That
alternative needs an explicit realization argument. Resource claims here count
declared persistent state bits only, excluding temporaries, reconstruction work,
allocation, total circuit area and elapsed time.

### Route A: algebraic evidence

The author supplies multiplier 3, the selected decoder, and source/artifact
association. The probe substitutes `x=q`, `y=3*q` into the source and normalizes
both sides of each required equation as sparse polynomials over `Z/16Z`:

```text
source_x′ = q+d = target_q′
source_y′ = 3*q+3*d = 3*(q+d) = D(target_q′).y
source_output = target_output
```

Initialization is checked independently. Polynomial coefficient equality is a
sufficient equality proof in this ring: literals, addition and multiplication
preserve evaluation by structural induction, and distributivity justifies
normalization. It need not be a complete decision procedure for equal functions
over a finite ring. A normalization mismatch is failed evidence, not a theorem
that every possible proof is impossible. Input and temporary bounds are checked
in nonnegative integers, outside the quotient theory.

This is an implemented restricted algebraic certificate route, not an executed
native Lean proof route. A native author could instead prove these equations
using their own invariant lemmas and supply a justified adapter. That third
route is a proposed follow-up, not measured evidence in this report.

### Route B: finite simulation evidence

The author supplies sixteen triples `(x,y,q)` describing a relation, with the
selected decoder as separate executable data. The checker reads the submitted
relation; it does not regenerate and trust a claimed invariant. It checks the
initial triple, validates decoder agreement for every triple, and checks all
four admitted inputs for every triple. Each successor triple must occur in the
relation and its outputs must agree. Omitting a needed row fails closure.

The mathematical soundness argument is induction on input-list length: initial
membership starts the induction, checked closure maintains it, and checked
output agreement gives the next output. It does not need ring normalization,
a multiplier hypothesis or a proof language for symbolic algebra. The checked
relation need only cover reachable execution from the admitted initialization;
it need not list every source state. The sample lists all sixteen represented
states, giving 64 checked edges.

This method can certify finite non-polynomial machines that Route A cannot
express. Route A can reuse its symbolic calculation across parameterized ring
models once their hypotheses and realization proofs are provided; a finite table
must be regenerated or justified uniformly when the state/input domain changes.
Neither route is a syntactic wrapper around an asserted native Lean record.
They use different evidence and different acceptance algorithms, and share
only their intended simulation conclusion and concrete realization checks.

### Admission, selection and execution in the probe

The probe binds evidence to canonical JSON bytes for the source, artifact and
selected decoder, plus the interpretation version. The source bytes include
input domain, initialization, primitive meaning, modulus and observations.
The artifact bytes include transition, output, initial state, widths and layout.
A digest match is an identity check; the checker still verifies correspondence
against those actual objects. Rebinding a bad artifact to a new digest does
not make its equations pass.

`source_realization` independently checks the source semantics, initialization,
input/observation contract and exact temporary bounds before `select` can choose
any executable route, including the baseline. An unsupported source refuses
execution even with no optimization certificate or an empty input list.
`admit` checks identity, supported semantics, realization bounds and the selected
evidence route. `select` admits the compressed candidate only with that semantic
acceptance and an independently checked claim in `declared-state-bits-v1`.
For a supported source, missing or rejected optimization evidence retains the
source interpreter with two four-bit registers. Without resource evidence, semantic admission succeeds but the
state-saving selection falls back. `execute_selected` executes the chosen
machine and checks every input before its transition. The diagnostic is retained
when selection falls back, rather than being hidden by the successful baseline.

The same executable JSON objects are checked and interpreted in this probe.
There is no external source exporter, emitted native code, unchecked executable
loader or persistent receipt cache. Hashes do not authenticate provenance or
prove an exporter correct. This restricted association is useful evidence for
#489's future boundary, not its implementation. Malformed external payloads,
parser security, denial-of-service limits and concurrent mutation are outside
this in-process fixture; production validation needs an immutable input snapshot
and a complete parser/checker contract.

## Two intermediate interpretations and route agreement

The probe exercises this fragment through two nonidentity translations, following
#492's mathematical route but with independently executed representation checks:

| Translation | Action on meaning, judgments and data |
|---|---|
| Integer polynomial/congruence presentation to `Z/16Z` polynomials | Map literals to residue coefficients and `+`,`*` to ring operations, retaining variables and interpreting congruence as equality. `q+16` and `q` share an image. Normalize after the supplied relational substitution. Integer order and exact bounds remain separate judgments |
| Ring polynomials to four-bit values | Map canonical coefficients and variable values to little-endian bit tuples. Evaluate with ripple-carry addition and shift/add multiplication, discarding overflow at four bits. The representation and operations change; the decoder's two components and their observations remain explicit |

The direct route evaluates the integer expression then takes its canonical
remainder. The composed route normalizes over the ring then evaluates with bit
operations. The executable comparison uses five expressions, including both
forms of the invariant calculation, `q+16`, and a nonlinear polynomial, at all
256 pairs of four-bit variable values. These are 1,280 finite comparisons, not
a formal proof for all expressions. The production artifact in the probe is
the exact-integer JSON interpreter with final remainder; the bit interpretation
is a separate exercised lowering, not emitted machine code.

The paper agreement argument quantifies over every expression of the stated
polynomial fragment and every valuation. Quotient compatibility proves the
first map preserves evaluation. Bit-vector addition and multiplication realize
residue addition and multiplication; structural induction proves the second.
Both maps commute with substitution because their operation clauses commute
with valuation substitution. Compose those equations to obtain direct/composed
agreement. The context includes `x,y,q,d`, the relational hypothesis and input
bounds. Bounds are retained in the integer realization context, never translated
into a nonexistent compatible ordering of the quotient ring. Simultaneous
state substitution is required.

Parameters such as modulus, coefficient and widths are indices of this contract.
The selected decoder transports as a term with pointwise output equations.
Equality of final observations is promised, not equality of proof objects or
recovery of all integer distinctions: `0` and `16` have equal quotient images.
For dependent witnesses, agreement must act on types and terms and commute with
substitution and witness transport. This nondependent example does not discharge
those coherence obligations. An identity route is available only when judgments,
primitive meanings and observations coincide.

MMT offers a possible publication mechanism for these requirements. Its paper
composition theorem assumes a regular foundation and total morphisms, including
metamorphisms; typing/equality preservation does not follow merely from a parsed
view. #492 checked individual LF theories/views, but its composite syntax attempt
failed. It did not check this complete arithmetic route; legacy Lean importer
adequacy and source correspondence remain unresolved. Retain that negative
engineering evidence when judging setup cost. [Rabe and Kohlhase, definitions
30/32 and theorems 34/48](https://kwarc.info/people/frabe/Research/mmt.pdf), and
[the pinned study and logs](mmt-compiler-evidence.md#pinned-mmt-implementation-and-the-executable-probe).

## Separating cases and their checking status

| Case | Result and evidence |
|---|---|
| Source coefficient changes from 3 to 2 | Both routes reject old bindings, and also reject freshly bound old relation evidence. First input 1 independently separates outputs 2 and 3 |
| Initialization changes to `(0,1)` | Both reject the old binding and then the initialization correspondence after rebinding |
| Modulus changes to 8 or primitive meaning to saturation | Old binding fails; rebinding reaches unsupported contract diagnostics. The source-only gate refuses execution with either fresh evidence or no evidence, including an empty trace. This is absent route support, not mathematical impossibility |
| Artifact output becomes `2*q` | Old binding fails; fresh binding fails output correspondence in both routes |
| Input 16 arrives | Executable input check rejects before a transition. The theorem only covers 0 through 3; a larger domain needs fresh arithmetic and admission evidence |
| Four-bit exact temporaries or three-bit state layout | Bound/layout checks reject both routes; state values such as 15 and temporary value 45 explain the failures |
| Decoder changes to `(q,q)`, is omitted, or relation loses a row | Digest/decoder/closure checks reject as applicable. Neither a theorem name nor a Boolean can replace selected executable data |
| Different syntax `y+(d+(d+d))` | Both routes accept fresh evidence. Different source bytes with the same denotation are allowed |
| Semantic evidence but no resource claim | `admit` accepts semantics; resource admission returns unknown and selection falls back. Output equality does not prove storage, latency or progress |
| No extra proof | Ordinary source interpreter remains executable and yields the same tested traces; compressed eligibility is unknown, not proved impossible |
| Store `y=2*x mod16` but retain `x` observations | `x=0` and `x=8` collide. Executable collision plus the paper functional argument refutes a total reconstructing inverse under these observations |
| Store `y=3*x mod16` instead | Paper positive case: use selected decoder `x=11*y mod16`, since `3*11=1 mod16`. This extension is algebraic, not a stronger logic |

All prototype statuses rejecting a certificate mean that particular evidence
was not accepted. A counterexample to a requested equation can establish its
failure; an unknown checker format, an unsupported parameter or a failed proof
attempt cannot establish impossibility of compilation. The probe reports
`rejected-evidence` with the specific cause for invalid supplied evidence, and
`unknown` for missing evidence or an unsupported contract. This retains the
distinction already present in native regional admission.

### Existence, stronger principles and internal equality

An extension from `∀x,∃y,R(x,y)` to a selected global function requires a choice
principle or stronger constructive data. In a setting admitting choice it can
justify semantic existence of a realization; it does not produce executable
code matching the artifact. Lean v4.35.0's choice theorem and noncomputable
selection illustrate the distinction. Neither probe route pretends to implement
this extension. The capability must remain expressible in a future evidence
interface even if an effective backend rejects its missing executable witness.
[Lean `Init/Classical.lean`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Classical.lean).

For a logical separator, retain #492's two-world intuitionistic model `w₀≤w₁`,
with `P` true only at `w₁`. At `w₀`, `P` is not forced and `¬P` is not forced,
so unrestricted excluded middle cannot be imported unchanged. The constructive
statement `¬¬(P∨¬P)` loses branch data and cannot substitute for a selected
decoder. These are paper arguments, not new Lean countermodels. Changing the
interpretation can preserve a translated statement while changing what it says;
forward preservation does not imply reflection of source derivability.

There is also a witness-sensitive risk beyond propositional truth. Equal
quotient images do not recover the original integer; a locally inhabited sheaf
need not have a chosen global section; agreement after forgetting dependent
identity witnesses does not establish agreement of the retained witnesses.
The [existing extension/descent study](all-model-representation-extensions.md)
and [dependent reassessment](dependent-architecture-reassessment.md) own those
stronger contracts. They remain adoption tests, not obligations erased by the
success of the finite example.

Ahman–Bauer's oracle modalities offer a relevant account of reasoning relative
to specified answers, and their sheafification/equifoliate-tree distinction
exposes loss of intensional query information under quotienting. The paper's
§2 assumes impredicative `Prop`, extensionality, proof irrelevance, propositional
equality and definite description; §4 adds the needed quotient-inductive
construction. It is not assumption-free evidence for arbitrary internal settings.
A possible later application is to distinguish semantic oracle-relative existence
from an executable query protocol and its resource observations. No imported
formalization or new workstream is proposed here. [Ahman–Bauer v2, §§2–4](https://arxiv.org/html/2602.22135v2).

### Quantum observation test

Retain #492's focused counterexample. In a Hilbert-space interpretation with
linear isometries and tensor product, copying the basis states fixes the images
`|0⟩↦|00⟩` and `|1⟩↦|11⟩`. Linearity then sends `|+⟩` to the entangled state
`(|00⟩+|11⟩)/√2`, whereas two independent copies would give four basis amplitudes
of `1/2`. Joint measurement has probability zero of `01` in the former and
`1/4` in the latter. Thus importing an unrestricted cartesian copying law with
that observation is invalid. Restricting inputs to classical basis labels is
a positive specialization; restricting observation to individual computational
basis marginals would hide this counterexample and weaken the contract.

This is a paper calculation, not a quantum backend implementation. SQIR's
pinned `c_eval` models sequential superoperators and measurement branches;
CoqQ proves an object program logic sound for a denotational semantics in Coq.
These sources demonstrate that a quantum object language and ordinary verification
metatheory can coexist. They do not make arbitrary classical operations available
on quantum states. Ideal-channel preservation, measurement probabilities,
finite-precision gate realization, device noise and physical timing remain
separate obligations. [SQIR density semantics](https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/SQIR/DensitySem.v),
[CoqQ v1](https://arxiv.org/abs/2207.11350v1).

## Comparison and author obligations

The alternatives can be combined; they answer different parts of the problem.
The rows are design assessments on this client, not measured productivity claims.

| Approach | Reusable content and recurring author work | Trusted dependencies and diagnostics | Assessment |
|---|---|---|---|
| Direct semantic interfaces with language-specific adapters | Native invariant, representation and step lemmas remain ordinary mathematics. Authors supply the local relation and realization data; generic continuation is reused | Native checker plus adequate source/artifact adapter. Unmet local equations can be exposed as goals; a host theorem name alone is insufficient | Retain as the native route and regression client. Cross-language adapters remain substantive work |
| Shared extensible proof language | Producers can reuse one vocabulary of supported derivations. New rules must declare requirements and checked interpretations; a fixed arithmetic core cannot express every desired principle | Shared parser/checker, normalization, extension discipline and encoding adequacy. Unsupported rule diagnostics can identify the missing extension | Investigate only after clients demonstrate common proof content. Defer a universal AST and mandatory migration |
| Theory-indexed judgments and composed interpretations | Share named requirements, local rule maps, contexts and witness-sensitive comparisons. MMT can publish this organization, while existing local theory maps serve compatible fragments | Adequacy of each encoding, totality, foundation rules, software/plugins, source maps and exporters. #492's parse/setup failures are real author costs | Investigate publication where reused heterogeneous routes justify it; do not adopt MMT software from this example |
| Multiple checked certificate formats | Algebraic evidence or finite relations can reach the same semantic gate. Authors choose reusable symbolic proofs or finite data; generic continuation belongs to the backend contract | Each checker needs its own soundness argument, versioned semantics and diagnostics. Finite counterexamples are concrete; normalization failures are less conclusive | Preferred bounded comparison. Additional formats must preserve the same advertised capability and witness contracts |

A theorem prover can produce a finite certificate, a common proof language can
carry a proved checker result, and a theory graph can describe either route's
requirements. Those combinations do not eliminate the checker's soundness or
the exporter-to-source obligation. Conversely, keeping a native interface does
not require making native Lean proof terms the contract for every programmer.

The executed author inputs are small but not a controlled author trial:
Route A supplies a multiplier and decoder; Route B supplies sixteen relation
triples and that decoder. Both include exact association. The one-time work
includes semantics, polynomial normalization or relation checking, bounds,
binding, independent baseline admission and diagnostics. No independent authors, repair-time measurements or
resource benchmarks were collected. The five-expression composition check and
mutation suite measure diagnostic behavior, not author productivity. A larger
state space increases finite-certificate work; symbolic reuse can avoid that
enumeration while requiring more proof-library infrastructure. Neither alone
establishes a general advantage.

## Reimplementation outside Lean

Moving the compiler to Rust, OCaml or another host can preserve source judgments,
primitive semantics, interpretation requirements, artifact descriptions,
accepted evidence capabilities and diagnostics. It can keep using Lean as an
independent verifier for the native route. Authors still write their existing
source proof; the compiler invokes a checker or receives a checked certificate
instead of asking authors to rewrite the proof in its new host language.

The implementation must reproduce the exact artifact association, versioned
serialization, input protocol, selected converters and verifier invocation.
An untrusted producer may emit candidates for an independently sound checker;
a verified compiler may instantiate a general preservation theorem. Both still
need a link to the artifact actually consumed. Replacing the verification
foundation is a separate undertaking: demonstrate justified interpretations
for the previously accepted rules and witnesses, or report a deliberate loss
of advertised capability. Changing the host cannot silently justify that loss.

For this probe, Python, its integer arithmetic, JSON semantics, both checker
implementations and the running interpreter are trusted. SHA256 identifies
inputs but supplies no semantic theorem. A production checker proved in Lean
would still need its evaluation/extraction and artifact-consumption boundary
stated; a proof checked in another foundation needs the corresponding trust
account. No new kernel or trust axiom is recommended.

## Validation and statement review

Replay with the repository environment:

```sh
direnv exec . python3 experiments/compiler-evidence/probe.py
```

The recorded run uses the pinned development shell, serialized CPU 0 execution,
and checks both positive routes, all stated mutations, no-proof/resource fallback,
source-gate rejection with fresh or absent evidence, valid-source fallback after
rejected optimization evidence,
341 traces per route of lengths zero through four, and the 1,280 composed/direct
interpretation comparisons. The trace count is `1+4+16+64+256`; arbitrary-length
preservation relies on the stated induction argument, not this bounded replay.
The output includes source/artifact/decoder hashes and precise rejection causes.
No Lean or MMT proof of these checkers, universal substitution theorem, or
complete compiled artifact route is claimed. The earlier #492 individual LF
successes, failed composite attempt and unproved arithmetic route remain as
published.

Statement review applied the example-driven counterexample checks to the paper
claims. The simulation quantifies over every related state and admitted input,
not just observed test runs. Both initial and successor obligations are required.
The decoder equations hold only on their stated domains. Integer bounds are
not inferred from modular equality. The baseline intervals have a concrete
unrecoverable state, but the result does not exclude stronger analysis. Choice
establishes semantic selection only under its additional principle; quantum
copying fails for the retained joint observation. These reviews found no reason
to weaken the independent expected output or erase a witness to make the example
pass. Formalization of checker soundness and the full interpretation route is
remaining implementation work.

## Requirement coverage and bounded follow-ups

| #490 requirement | Delivered evidence; remaining decision or obligation |
|---|---|
| Implementation-independent evidence and four alternatives | Semantic admission contract, comparison and host-reimplementation account; owner has not selected a production representation |
| Stateful added capability and two different routes | Symbolic polynomial checker and finite simulation checker admit the same compressed artifact beyond the interval baseline; both checkers still need formal soundness |
| Several interpretations, at least two nonidentity, direct/composed agreement | Integer/congruence → ring polynomials → four-bit operations, paper substitution argument and executed comparisons; no universal checked coherence theorem |
| Exact source/artifact/parameter/primitive association | Digest rejection plus freshly rebound semantic mutation failures; foreign source/exporter correspondence remains #489 |
| Executable witness and stronger-principle extension | Retained decoder, witness-loss rejection, choice and intuitionistic separators; no executable witness extracted from mere existence |
| Input/overflow/resource/progress distinctions | Runtime guard, integer intermediate bounds, layout check, separate resource eligibility; no latency, total-memory or physical progress claim |
| Semantic equality with different syntax and no-extra-proof path | Positive repeated-addition source and fallback execution; native clients unchanged |
| Actual admission and selection, continuation reuse | Executed `admit`/`select`/`execute_selected`; existing native continuation contracts identified, no production integration yet |
| Quantum and mathematical backends | Joint-observation copying separator and four separate realization questions; no requirement of physical execution for mathematical interpretations |
| MMT required input, author effort, trust, diagnostics | #492 findings and failures retained; no new full MMT study or causal productivity result |

Propose these follow-ups, subject to the owner's contract decision, with no
new issue or architecture adopted by this report:

1. **#490 decision record:** choose the bounded source fragment, exact observation
   and input contract, accepted evidence capabilities, trust policy and fallback
   behavior. Retain this comparison's alternatives and limitations as evidence.
2. **#489 correspondence implementation:** bind an existing explicit-source client
   and a selected author-proof route to actual lowerings. Preserve direct native
   calls. Prove or validate source/export correspondence, both nonidentity
   interpretations and selected decoder realization; replay the separating cases.
3. **#490/#290 checker comparison:** prove finite-certificate acceptance sound,
   compare it with a native semantic proof adapter on this same machine, and
   run matched independent author tasks. Include a non-polynomial finite machine
   and a parameterized symbolic case so either route can expose the other's cost.
4. **#235/#36 extension gate:** require a witness-sensitive dependent client and
   a named stronger principle before generalizing evidence interfaces. MMT
   publication can be evaluated under #290 if reused heterogeneous routes justify
   its setup; the failed composite probe is not a reason to infer impossibility.
5. **#487/#488 execution consumers:** consume only admitted, exactly associated
   artifacts; retain state/session indexing, explicit migration conversions and
   resource/progress contracts. This research does not reopen their explicit-source
   milestones or authorize an unproved bridge.

Defer production importers, a common universal proof AST and framework adoption.
Reject admission based only on matching names, hashes, process exit status,
existence of some witness, or an unsupported transfer of laws. Preserve native
interfaces and allow stronger mathematical targets when their interpretations
justify the required principles.
