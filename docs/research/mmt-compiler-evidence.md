# MMT for compiler evidence across interpretations

Investigate a bounded MMT publication and checking experiment; defer framework
adoption and a production importer. MMT supplies named theories, dependencies
and composable interpretations, but the inspected implementation does not
supply the source-to-artifact contract needed by
[#492](https://github.com/VladimirMarko/conaled/issues/492). In particular,
checking a view cannot establish that its declarations describe the program
being compiled. These findings inform the open comparison in
[#490](https://github.com/VladimirMarko/conaled/issues/490), not a selected API.

The stateful example below retains a programmer's invariant, a selected decoder
and executable realization data through two nonidentity interpretations. Its
mathematics is reusable without MMT. A separate executable MMT probe tests
small LF theories and views; it does **not** check the stateful interpretation.
The earlier [#294 comparison](theory-network-comparison.md) remains bounded
positive evidence for algebraic proof reuse, not a universal verdict.

## Evidence and inspected versions

Inspection date: 2026-11-12. Repository base:
`38ae62f9ec55ab482dcab29c6bece957ee3c3ace`, Lean 4.35.0. This change adds no
formal declarations, importer, dependencies or trust axioms. Local source
inspection and the Python probe do not constitute Lean verification.

| Material | Exact version and evidence |
|---|---|
| MMT source | [71814b0fec9c1f2dbe7d677ab65bb433bc90ec08](https://github.com/UniFormal/MMT/tree/71814b0fec9c1f2dbe7d677ab65bb433bc90ec08); `src/build.sbt` selects Scala 2.13.4; version file says 27.0.0 |
| Executed MMT | Release [v27.0.0](https://github.com/UniFormal/MMT/releases/tag/v27.0.0), tag commit `fca5d7e12db5b4e9d6329590f9d25380017981d8`; downloaded `mmt.jar` SHA256 `e481c037e5785f3e6da4fa3110b683a98aced3ea9a0a7499f374a7d194565c3d`. Release binary was not rebuilt or proved to correspond to source |
| Foundation archive | [MMT/urtheories 05f2c91b00373c611eb66e26ede27510f97f65b2](https://gl.mathhub.info/MMT/urtheories/-/tree/05f2c91b00373c611eb66e26ede27510f97f65b2), especially `source/lf.mmt` |
| Logic encodings | [MMT/LATIN2 48d8ce4d6d1bccbee8d746a3a519f07625ea2c5e](https://gl.mathhub.info/MMT/LATIN2/-/tree/48d8ce4d6d1bccbee8d746a3a519f07625ea2c5e); source inspection only |
| Quantum comparison | [SQIR 134fb942265091baa3e3972f78f72da41827351f](https://github.com/inQWIRE/SQIR/tree/134fb942265091baa3e3972f78f72da41827351f), `SQIR/UnitarySem.v`, `DensitySem.v`; not rebuilt |
| Probe runtime | OpenJDK 21.0.12+8 and repository direnv Python 3.13.15; serialized with `flock /tmp/conaled-wave-20261111/build.lock`, CPU 0 |

Disposable sources, receipts and failed attempts were retained outside the diff
at `/tmp/conaled-wave-20261111/492-handoff`. The reproduction sections below
contain the essential inputs; that temporary directory is not a durable public
artifact dependency.

## What the preservation theorems require

In [Rabe–Kohlhase, *A Scalable Module System*](https://kwarc.info/people/frabe/Research/mmt.pdf),
17 December 2012 preprint, Definition 30, pp. 60–61, regularity requires
normalization-compatible equality, equivalence/congruence and context
conversion, and preservation by flat assignments respecting declaration types
and definitions throughout meta-theories. Definition 32 makes totality include
the metamorphism. Theorem 34, pp. 61–63, assumes a fixed regular foundation:
well-formed composition is associative with identities; total morphisms compose;
iterated application agrees with composite application. Typing and foundational
equality preservation require totality; composition congruence requires total
second morphisms. Theorem 48 proves regularity for the paper's LF foundation.
These are conditions on a mathematical foundation, not certification of any
Scala plugin implementing similarly named rules.

[Rabe's dissertation](https://kwarc.info/people/frabe/Research/phdthesis.pdf),
2008, Definitions 5.22–5.23 and Theorem 5.24, pp. 104–105, distinguish encoding
from adequacy. Model adequacy requires model expansion (surjectivity on model
objects); proof adequacy requires fullness of the proof functor, relaxable to
fullness after quotienting to provability. Each adequacy condition supports its
own reverse-consequence direction; forward transport alone needs neither.
Thus an encoding that forgets a selected witness may preserve provability
without meeting this compiler's data contract.

[Rabe, *How to Identify, Translate, and Combine Logics?*](https://kwarc.info/people/frabe/Research/rabe_howto_14.pdf),
§3.2, Theorem 3.51, considers logical morphisms `sem : Syn → Sem, Δ` and
`r : Sem → Sem′, Δ′`, with the second semantics their induced composite.
Proofs and truth/falsity witnesses transport. Theorem 3.52 additionally requires
model-conservativity of `r` to retain models and reflect denotational validity.
Theorem 3.56 requires a commuting proof-to-model morphism for soundness;
completeness additionally requires classical proof theory and
model-conservativity. An inconsistent premodel is not an acceptable substitute
for a model. This rules out reading a syntactic translation as an unconditional
change-of-logic equivalence.

A theory declares operations and judgments. Its meta-theory determines how
those declarations are typed and compared. A view supplies their images;
a metamorphism must interpret the source meta-theory when that changes.
Object equality, the foundation's conversion judgment and equality of
interpretations are separate. For compiler use, identify which equality the
backend actually observes before selecting the interpretation.

## Stateful capability beyond the baseline

This is a deliberately specified research client, not a claim about the current
FRP implementation. Source states are pairs of unsigned residues `(x,y)` in
`{0,…,15}²`. Initialization is `(0,0)`. An input `d` is in `{0,…,3}`. The
simultaneous transition and post-transition output are

```text
x′ = (x+d) mod 16
y′ = (y+3*d) mod 16
output = y′
```

The baseline is **independent interval analysis**, with two four-bit state
registers. Its state invariant is `0≤x,y<16`; it admits `(0,1)` and cannot
justify reconstructing `y` from `x`. A relational analysis could discover the
relation; this example is not a lower bound on all automatic analysis.

The programmer supplies `I(x,y) : y ≡ 3*x (mod 16)`, and proves initialization
and preservation. Initialization is `0≡3*0`. Given `I`, congruence and
distributivity yield

```text
y + 3*d ≡ 3*x + 3*d = 3*(x+d) (mod 16).
```

Reduction modulo 16 retains this congruence. Since both resulting components
are canonical representatives, `y′ = (3*x′) mod 16`. Induction on the input
list establishes the invariant for every reachable state, including arbitrary
finite lengths. The executable selected decoder is
`decode(q)=(q,(3*q) mod 16)`; `encode(x,y)=x`. On invariant states,
`decode(encode(s))=s`; on four-bit states, `encode(decode(q))=q`.
These equations preserve the actual selected representation, not merely an
existential statement that some representation exists.

The candidate artifact stores `q`, starts at zero, updates
`q′=(q+d) mod16`, and emits `(3*q′) mod16`. Its correctness obligations are
initial correspondence, transition correspondence and output agreement.
Together they imply equality of output lists by induction, reusing the same
continuation theorem for each supplied invariant. Input admission remains an
explicit premise. The prototype rejects inputs outside the interval; a deployed
input checker or environmental invariant would have to enforce it.

Intermediate arithmetic matters. `x+d≤18`, `y+3*d≤24`, and `3*q≤45`.
Five bits suffice for the two source sums; six suffice for decoder
multiplication. The prototype declares six-bit temporaries uniformly and
checks these bounds. Four-bit modular multiplication also computes the final
residue, but that is a different operational contract and requires its own
argument. A checked exact integer multiplication cannot simply be relabelled
as an overflowing machine multiplication.

The resource observation is four state bits versus eight for the specified
baseline register layout. It is not a theorem about total hardware area,
latency, energy or Python storage. Reconstruction adds arithmetic. Semantically
equal artifacts may have different costs; selection requires a separately
validated resource model and ranking policy.

### Two nonidentity interpretations and their contexts

The following is a paper derivation plus the bounded executable checks below,
not a checked MMT graph of arithmetic.

| Stage | Translation and retained data | Required justification |
|---|---|---|
| Integer congruence presentation `T` to ring presentation `R` | Send integer expressions to residue classes in `Z/16Z`, addition/multiplication to ring operations, congruence to ring equality. Send `I` to `y=3*x` and its derivation to the ring calculation. Retain input bounds and canonical representatives as separate realization judgments | Quotient well-definedness and ring laws; this is **not** a translation of arbitrary integer equality, order or division into ring equality |
| `R` to bitvector presentation `B` | Send residues to canonical four-bit vectors, ring operations to modular bitvector operations. Retain the term `q↦(q,3*q)` as a decoder and the six-bit arithmetic realization | Bijection of residues with four-bit vectors; compatibility of modular operations, decoding and exact intermediate computations; selected widths and parameters remain explicit |

The first map is noninjective on integers (`0` and `16` have one image); the
second changes carriers and operations. Neither is an identity on native
Lean judgments. Integer bounds stay in an accompanying realization theory;
pretending that the quotient preserves their order would make the route
ill-defined. This separation is a requirement on the proposed encoding, not
an existing MMT feature automatically selecting the right fragment.

For contexts of ring variables, translate each variable's type and each
assumption, and extend valuations componentwise. For a substitution `σ`,
structural induction on variables, literals, `+` and `*` gives
`F(t[σ])=F(t)[Fσ]`, using quotient compatibility; the bitvector map satisfies
the analogous law. Proof steps use transitivity, congruence and the named ring
laws. The state-update substitution maps `x,y` simultaneously, so a sequential
mutation of `x` before evaluating the old `y` is not this substitution.
Bounds are obligations in the extended context `x,y<16,d≤3`, discharged by the
displayed inequalities, not erased by the map.

A direct integer-to-vector interpretation that takes the canonical remainder
agrees with the composite on literals and operations; induction gives agreement
on every expression of this fragment. The chosen decoder agrees pointwise,
as does its output equation. No equality of independently produced proof
objects is promised. For dependent families, this comparison would also need
action on types, substitution and transported witnesses, as required by the
[transport inventory](preservation-contract-inventory.md). The simple ring
client does not discharge those higher obligations.

## Extensions, changes of logic and separating cases

An algebraic extension asks to store `y` instead and reconstruct
`x=11*y mod16`. Its extra premise is a chosen inverse of multiplier 3;
`3*11≡1`. Multiplier 2 fails: `2*0≡2*8`, so an inverse retaining the `x`
observation is impossible for those assignments. If clients observe only `y`,
forgetting `x` can still be sound. This is an additional algebraic capability,
not a stronger logical foundation.

A genuinely stronger logical extension permits general representative
selection from mere existence. For arbitrary `X`, family `Y x`, and relation
`R x y`, it asks for

```text
(∀x, ∃y:Y x, R x y) → ∃f:(∀x,Y x), ∀x, R x (f x).
```

The chosen `f` could discharge an abstract representation-existence obligation
when a constructive section is unavailable. Lean 4.35.0's
[`Classical.axiomOfChoice`, `choose` and `propDecidable`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Classical.lean)
provide the corresponding theorem and noncomputable selection operations.
The stronger evidence remains useful for semantic reasoning in an accepting
foundation. It does not supply executable decoder bytes, their time bound,
or equality with the specific decoder chosen by an artifact. For the finite
ring client we retain the explicit decoder instead; using choice is unnecessary.
A backend requiring an executable section must still receive one and its
compatibility proof. Its compiler host language does not change that obligation.

For an explicit logical separator, use an intuitionistic two-world frame
`w₀≤w₁`, with atom `P` true only at `w₁`. At `w₀`, neither `P` nor `¬P` is
forced, hence `P∨¬P` fails. This is a paper countermodel to unchanged import
of unrestricted excluded middle into that semantics. Conversely
`¬¬(P∨¬P)` has a constructive derivation: assuming its negation gives `¬P`
(by injecting any proof of `P`), which itself injects into the disjunction,
a contradiction. Changing the conclusion in this way preserves a weaker
negative observation; it does not recover a branch or selected data.
We do not claim to have constructed a full negative translation of Lean or
Agda. A theory-specific metamorphism must map **all** used rules, including
choice if used, with a justified interpretation. A classical Set model is
one possible target, not a model of every desired intensional or cubical
source judgment with its observations retained.

The source/artifact boundary has additional paper separators. No production
manifest gate or mutation-test suite is implemented here:

| Change | Consequence |
|---|---|
| Change source coefficient to 2 but reuse the coefficient-3 certificate | Transition correspondence fails, e.g. first input 1; hashes must change and semantics must be rechecked |
| Change initialization to `(0,1)` | Invariant fails before the first transition |
| Admit `d=16` under the old five-bit source-sum claim | `y+3*d` can exceed the justified intermediate range; modular semantics alone does not validate exact temporaries |
| Supply only `∃decode` or discard the chosen decoder | No connection to the actual reconstruction code; admission needs data and a compatibility proof |
| Reuse a receipt for changed artifact bytes | Receipt identity check rejects; matching hashes alone never proves correspondence |
| Replace arithmetic by different syntax with the same denotation | Can be accepted through a checked semantic correspondence; byte equality is not required between different programs |
| Keep output equality but omit cost evidence | Semantic admission may succeed; a state-bit or latency ranking is unsupported |

Unsupported exporter routes are missing evidence, unlike the inverse and
Kripke counterexamples, which refute specified assignments/observations.

## Pinned MMT implementation and the executable probe

The inspected
[`MMTStructureChecker`](https://github.com/UniFormal/MMT/blob/71814b0fec9c1f2dbe7d677ab65bb433bc90ec08/src/mmt-api/src/main/info/kwarc/mmt/api/checking/MMTStructureChecker.scala)
collects rules from context (`prepareCheck`), delegates object judgments,
and checks view totality (`checkElementEnd`, lines 526–527;
`checkTotalTop`, lines 571–579). Its own comment before `check` warns that an
element is marked checked independently of errors. The
[`check` shell action](https://github.com/UniFormal/MMT/blob/71814b0fec9c1f2dbe7d677ab65bb433bc90ec08/src/mmt-api/src/main/info/kwarc/mmt/api/frontend/actions/CheckAction.scala)
uses `ErrorLogger`. Consumers must inspect diagnostics, not a checked marker
or process status alone. These two files have no diff between the inspected
head and the executed release tag; that does not prove binary correspondence.

The LF archive registers Scala rules for universes, Pi, lambda, application,
beta and extensionality. Its dependency setup is part of the trusted software
configuration. No claim is made that all registered extensions implement
exactly the LF regularity proof above.

The small probe has three theories over this LF: `A` declares `a:type`,
`x:a`, and `chosen:a=x`; `B` declares `b:type,y:b`; `C` declares `c:type,z:c`.
The views map `(a,x)` to `(b,y)` and `(b,y)` to `(c,z)`. It tests selected
defined data and total assignments, without an object arithmetic theory.
The complete native syntax is:

```text
namespace https://conaled.example/492❚
import lf http://cds.omdoc.org/urtheories❚
theory A : lf:?LF =
 a : type❙
 x : a❙
 chosen : a ❘ = x❙
❚
theory B : lf:?LF =
 b : type❙
 y : b❙
❚
theory C : lf:?LF =
 c : type❙
 z : c❙
❚
view f : ?A -> ?B =
 a = b❙
 x = y❙
❚
view g : ?B -> ?C =
 b = c❙
 y = z❙
❚
view missing : ?A -> ?B =
 a = b❙
❚
```

To replay, download the pinned release jar, clone the pinned urtheories, and
put this file at `probe-archive/source/probe.mmt`. Its
`META-INF/MANIFEST.MF` contains `id: conaled/492` and
`narration-base: https://conaled.example/492`. Run `java -jar mmt.jar --file
probe-build.msl --noshell`, with this script, replacing the two paths:

```text
mathpath archive /absolute/path/urtheories
mathpath archive /absolute/path/probe-archive
build MMT/urtheories mmt-omdoc meta.mmt
build MMT/urtheories mmt-omdoc module-expressions.mmt
build MMT/urtheories mmt-omdoc lf.mmt
build conaled/492 mmt-omdoc
check https://conaled.example/492?A mmt
check https://conaled.example/492?B mmt
check https://conaled.example/492?C mmt
check https://conaled.example/492?f mmt
check https://conaled.example/492?g mmt
check https://conaled.example/492?missing mmt
```

The final run checked `A`, `B`, `C`, `f` and `g` without diagnostics.
The deliberately incomplete view produced `invalid element
https://conaled.example/492?missing: view is not total` during both build and
explicit checking, yet the process exited **0**. This is observed evidence
that exit status alone is insufficient for this command path. The report
counts the diagnostic as rejection, not the process status as acceptance.
Positive-only and final negative logs are retained separately.

Earlier attempts are retained: the documentation's `read FILE` command was
rejected by this release's shell grammar; `lf?LF` incorrectly resolved a
relative URI, repaired to `lf:?LF`; omitting the component separator before
`=x` made the intended definition fail to supply a total view. These are
specific setup/authoring failures, not logical impossibilities. Archive build
and explicit checks replaced the obsolete shell command.

An additional attempt at a defined composite view used `abbrev COMPOSE ?f; ?g`.
It failed with `unbound token: ;` and a build error (`last of empty list`);
that attempt exited 3. Earlier `=` and `:=` spellings failed at the view
parser. The final reproducible probe omits that declaration. Composition
remains a paper/source-supported capability here; no successful executable
check of the composite or evaluation of the transported `chosen` term is
claimed. This bounded failure does not refute composition in MMT.

## Source logics and engineering obligations

The pinned
[`LeanImporter.scala`](https://github.com/UniFormal/MMT/blob/71814b0fec9c1f2dbe7d677ab65bb433bc90ec08/src/mmt-lean/src/info/kwarc/mmt/lean/LeanImporter.scala)
expects a low-level text export, parsed by the bundled trepplein-derived
checker. It compiles declarations into an environment, emits definitions and
elaborated declarations/reduction rules, freshens binders, and translates
universe levels. This is evidence of a substantive importer, not evidence for
a supported Lean 4.35.0 export path. The inspected
[LATIN Lean encoding](https://gl.mathhub.info/MMT/LATIN2/-/blob/48d8ce4d6d1bccbee8d746a3a519f07625ea2c5e/source/foundations/lean/cic.mmt)
contains universe operations, typing and equality rules. One concrete version
alignment concern is that the importer lambda case emits `Lambda`, whereas
this encoding declares `Lam`. Resolve and check the actual pairing before
claiming support. No Lean import was executed here.

The inspected
[PL-to-FOL example](https://gl.mathhub.info/MMT/LATIN2/-/blob/48d8ce4d6d1bccbee8d746a3a519f07625ea2c5e/source/logic/fol_like/pl-sfol.mmt)
represents propositions by Boolean terms and deduction by equality to true,
with explicit connective/rule assignments. It labels its view not total.
This illustrates both how a change of logic is represented and why presence
in a library is insufficient certification. No totality theorem for LATIN2
as a whole is inferred from either this example or the successful LF probe.

Reuse [#115's Agda inspection](agda-internal-retention.md): Agda 2.8.0.2,
Cubical `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`, ordinary
`--safe --without-K` and separate `--safe --cubical --guardedness` cases.
Completed interfaces retain dependent types, checked bodies, modes,
conversion dependencies and generated clauses. `step` being reflexivity does
not erase its cubical conversion obligations. Selected paths and transported
witnesses survive there; runtime output cannot replace them. That study's
Monodromy JS compilation failed with `CubicalCompilationNotSupported`.
This report does not rerun it or claim an Agda-to-MMT importer: none was found
in the inspected MMT/LATIN2 file inventory, which is a bounded search.

Lean can produce native proofs and explicit executable converters for the
ring client; Agda can express the constructive fragment too. Their native
elaboration/checking is separate from export adequacy. For broader source
support, retain universes, substitution, equality/conversion, opacity,
inductives, quotient/cubical rules and relevant modalities, together with the
actual dependency closure. Proof irrelevance in a target cannot justify
forgetting a source witness observed by a consumer. Identity transport is
valid only for judgments whose meanings align, not because both systems use
similar names.

## Capability and obligation matrix

| Obligation | MMT contribution | Encoding/backend responsibility |
|---|---|---|
| Names, theory dependency and reusable views | Explicit graph, imports, morphism application | Exact version/closure and reject unresolved or partial dependencies |
| Typing and equality | Foundation-specific checking machinery; conditional preservation theorem | Regular mathematical foundation, correct executable rules, source adequacy |
| Change of logic | Meta-theories and metamorphisms | Interpret every used rule and its hypotheses; retain source meaning |
| Composition | Reusable morphism composition | Correct stage assignments; context/substitution compatibility; coherence for alternate routes |
| Selected term/witness | Terms can remain named definitions and be translated | Preserve dependent observations and prove relation to chosen executable data |
| Programmer invariant | Can publish proof and obligations | Source proof, initialization, transitions, input assumptions |
| Executable code | Can publish a description of code | Code semantics, faithful serialization/export and correspondence to exact artifact |
| Stronger principles | Can expose extension dependencies | Target validation; conservativity/model expansion when claimed; no automatic executable choice |
| Resources and ranking | Can represent separately specified judgments | Cost model, quantitative proofs, measurements when needed, policy |
| Sound checker acceptance | Diagnostics and extensible rule implementation | Trusted implementation or independent checking; errors, gaps, timeouts and unresolved goals must reject |
| Hardware realization | No automatic physical guarantee | ISA/gate implementation, noise/error, timing and external input assumptions |

## Alternatives on this same admission problem

All alternatives must establish the same initial/step/output equations for the
recorded source and four-bit artifact, retain `decode`, and account for input
and temporary bounds. The following are architectural comparisons, not measured
author-productivity results.

| Route | Expressiveness and proof reuse | Author effort, trust, diagnostics and maintenance |
|---|---|---|
| Direct semantic adapter | Reuse native invariant and simulation lemmas; other contracts remain native | Small recurring interface for this client; each new source/target pair needs a justified adapter. Native checker plus source/artifact bridge remains trusted |
| Extensible common proof language | Shared checking and generic composition for admitted rules; extension mechanism must permit stronger capabilities | Frontend export and rule adequacy are upfront work; unsupported rules can be identified precisely. A fixed arithmetic fragment cannot be the ceiling; extensions increase checker/maintenance obligations |
| Theory-indexed MMT publication | Explicit logic requirements, dependencies and named intermediate interpretations; native interfaces can coexist | Useful for heterogeneous libraries, but archive/rule/version setup and adequate exporters are additional work. Generic error locations need source mapping. Scala runtime/plugins join trust unless output is independently rechecked |
| Multiple checked certificate formats | Native proof certificate and finite transition-table certificate can justify the same backend gate through different checkers | Authors may choose native reasoning or finite checking; reusable continuation theorem belongs at the common semantic boundary. Each checker needs soundness and versioning, with separate diagnostics and trust dependencies |

For a genuinely different second evidence route, finite enumeration can certify
all 64 transitions of the selected state space and all 16 outputs, whereas
the programmer's ring proof uses induction/congruence for arbitrary traces.
These are different evidence production methods. The executed enumeration is
not yet a certified checker; wrapping its Boolean answer in a Lean record
would not fix that. #490 should compare a proved table checker against a
native proof route, at the same artifact gate, including failures and author
repair effort. MMT can publish either format's theory and compose justified
interpretations; it need not replace their native checkers.

A compiler reimplemented in Rust, OCaml or another language could retain these
contracts and accepted source evidence capabilities. Portable obligations are
program/primitive semantics, selected observations, parameters, certificate
schema/version and the relation to exact output bytes. Implementation work
includes producing matching manifests, preserving serialization, invoking or
replacing checkers, and validating each lowering. An untrusted compiler can
emit independently checked translation certificates. A verified compiler can
instead supply a general preservation theorem instantiated at the produced
artifact, still with an extraction/execution boundary. Neither choice requires
programmers to author host-language proof terms. Continuing to use Lean as a
verification foundation while moving the compiler host is coherent; replacing
that foundation must preserve advertised evidence capabilities through further
checked interpretations, not silently reject formerly accepted mathematics.

## Quantum counterexample and observations

For a finite quantum target, take tensor-product Hilbert spaces, linear
unitary gates, density operators, sequential composition, and measurement
instruments. Observe measurement probabilities `tr(Pρ)` or the full output
density operator, according to the contract. Tensor product is not a
cartesian product with unrestricted copying of arbitrary states.

Here is a direct paper separator. A linear isometry copying both basis states
with a fixed blank would send `|0⟩` to `|00⟩` and `|1⟩` to `|11⟩`.
Linearity sends `|+⟩` to `(|00⟩+|11⟩)/√2`; two independent copies of `|+⟩`
would instead give `( |00⟩+|01⟩+|10⟩+|11⟩ )/2`. Computational-basis joint
measurement distinguishes them: the former has zero probability of `01`,
the latter probability `1/4`. Their one-qubit marginals in that basis agree,
so a marginal-only contract loses the needed distinction. Copying classical
basis labels can be admitted with that restriction; unrestricted copying
cannot be imported unchanged. For a deterministic channel allowing an
environment, purification would require `c=c²*e` for the overlap
`c=|⟨0|+⟩|=1/√2` and an environment overlap with `|e|≤1`, again impossible.
This extends the obstruction to the finite-dimensional channel model, under
its isometric-dilation assumption. A compiler interpretation preserving a
cartesian diagonal as this arbitrary-state operation has no such realization.

The pinned [SQIR density semantics](https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/SQIR/DensitySem.v)
implements sequential superoperator composition and adds measurement branches;
`c_equiv` quantifies over well-formed matrices with positive dimension.
`seq_congruence` uses well-formedness preservation. Its
[unitary semantics](https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/SQIR/UnitarySem.v)
separates exact matrix equivalence from equivalence up to global phase.
The observation must be specified before transferring either equivalence.
[CoqQ](https://arxiv.org/abs/2207.11350), v1 (2022), separately demonstrates a
quantum object language and program logic verified against denotational
semantics in Coq. These are examples of quantum programs verified in an
ordinary mathematical metatheory, not a requirement that the verifier adopt
quantum logic. No SQIR or CoqQ proof is imported here.

Physical assumptions remain separate: gate calibration, environmental noise,
measurement fidelity, finite precision and execution/control timing. A theorem
about ideal density operators does not establish their error bounds. A
probability law is also not a deterministic guarantee of each outcome; neither
an MMT view nor classical metatheory removes that difference.

## Reproducing the semantic probe

The following Python program generates the exact source and artifact bytes
as canonical JSON and checks the selected decoder against independent source
and artifact expressions. Run it in an empty disposable directory with the
repository's `direnv exec . python3 /path/stateful.py`. The recorded SHA256s
are identifiers, not mathematical evidence. The JSON is a small executable research IR interpreted with exact Python
integers, not native machine code or an existing repository compiler output.
The range checks justify the declared finite temporaries in this model.
The computation checks every
finite state/input case; the arbitrary-trace conclusion additionally uses
the paper induction above. Python and its interpreter are trusted for this
experiment; no Lean or MMT acceptance follows.

```python
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
C=lambda n:['const',n]
S=lambda n:['state',n]
D=['input']
add=lambda a,b:['add',a,b]
mul=lambda a,b:['mul',a,b]
mod=lambda a:['mod',a,C(16)]
source={'init':[0,0], 'input':[0,3], 'step':[mod(add(S(0),D)),mod(add(S(1),mul(C(3),D)))], 'out':S(1)}
artifact={'init':[0], 'input':[0,3], 'step':[mod(add(S(0),D))], 'out':mod(mul(C(3),S(0))), 'state_bits':4, 'temporary_bits':6}
def ev(e,s,d):
    op,*a=e
    if op=='const': return a[0]
    if op=='state': return s[a[0]]
    if op=='input': return d
    x,y=(ev(t,s,d) for t in a)
    return {'add':lambda:x+y,'mul':lambda:x*y,'mod':lambda:x%y}[op]()
def step(p,s,d):
    assert p['input'][0]<=d<=p['input'][1]
    return [ev(e,s,d) for e in p['step']]
def digest(p): return hashlib.sha256(json.dumps(p,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def decode(q): return [q[0],3*q[0]%16]
assert source['init']==decode(artifact['init'])
for x in range(16):
    q=[x]; s=decode(q)
    assert ev(source['out'],s,0)==ev(artifact['out'],q,0)
    for d in range(4):
        assert step(source,s,d)==decode(step(artifact,q,d))
        assert x+d<32 and s[1]+3*d<32 and 3*x<64
seen={tuple(source['init'])}; frontier=list(seen)
while frontier:
    s=frontier.pop()
    for d in range(4):
        t=tuple(step(source,s,d))
        if t not in seen: seen.add(t); frontier.append(t)
assert seen=={tuple(decode([x])) for x in range(16)}
assert (0,1) not in seen # admitted by independent intervals, violates invariant
assert (11*3)%16==1
assert (2*0)%16==(2*8)%16 and 0!=8
for name,p in [('source',source),('artifact',artifact)]:
    (ROOT/(name+'.json')).write_text(json.dumps(p,sort_keys=True,separators=(',',':')))
receipt={'source_sha256':digest(source),'artifact_sha256':digest(artifact),'reachable_states':len(seen),'checked_transitions':64,'checked_outputs':16,'selected_decoder':'x -> (x, 3*x mod 16)','state_bits':[8,4],'temporary_bits':6,'evidence':'finite exhaustive Python check, not MMT or Lean theorem'}
print(json.dumps(receipt,indent=2))
```

The run returned:

```json
{
  "source_sha256": "37120bee842932863b9fec708d307977a829d3c3d0942cee909f6a1721172470",
  "artifact_sha256": "b53201eaa26d498902ed7f56d92afe5055b637b7e298034a52808cca2fe37c05",
  "reachable_states": 16,
  "checked_transitions": 64,
  "checked_outputs": 16,
  "selected_decoder": "x -> (x, 3*x mod 16)",
  "state_bits": [
    8,
    4
  ],
  "temporary_bits": 6,
  "evidence": "finite exhaustive Python check, not MMT or Lean theorem"
}
```

## Recommendation and remaining decision work

Adopt the mathematical discipline of explicit assumptions, retained witness
terms and compositional interpretation obligations. This recommendation does
not adopt MMT software or a common proof representation. Investigate MMT as
an optional publication/orchestration layer where several object logics and
reused intermediate views make that work worthwhile. Defer a Lean/Agda
production importer, and reject any admission policy equating parsed content,
a successful process exit, or a theorem name with certified artifact behavior.

A bounded follow-up should check the **whole stateful route**, including
source association, both semantic translations and executable decoder, then
inject the failures listed above. Compare direct/native proof and a sound
finite-certificate checker at the same backend gate; optionally publish their
requirements as MMT theories. Preserve the no-extra-proof baseline. Record
which proofs are reused, frontend repairs, diagnostic quality and recurring
author effort separately from one-time infrastructure setup. Success on the
ring client must not remove the dependent-witness and quantum observation
tests from the broader language direction.

#490 still owns the interface choice, which evidence formats are accepted,
the exact artifact/admission boundary, fallback behavior and the measured
comparison. #489 owns the production source/program association after that
contract is selected; #487/#488 retain migration and artifact execution.
#290 owns reusable theory publication, coordinated with #235/#36 for source
judgments, dependent coherence and extension requirements. Missing adequate
source exporters, verified checker acceptance, and a complete arithmetic MMT
encoding remain explicit gaps. Neither the small LF check nor the finite
Python run resolves them.
