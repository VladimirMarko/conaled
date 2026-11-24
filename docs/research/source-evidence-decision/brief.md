# Bounded source-evidence decision: independent assessment brief

Input revision: `0d3865b344940510428e01f6907cb03dedbfe256`. Assignment #699
prepares an owner decision for #489. It does not implement or adopt a production
bridge, universal evidence API, source logic or proof language. Full issue
requirements are saved outside the source tree in `/tmp/conaled-699-evidence/spec.md`.
The prior #490/#492 studies are completed evidence, not architecture decisions.

## Shared fragment and observations

Assess two programs in an acyclic first-order residue-expression fragment:
variables, nonnegative literals, addition/multiplication, explicit final remainder
modulo 16, unit/products/projections and let binding. No recursion, higher-order
values, arbitrary opaque definitions, effects or new primitive semantics.
A named finite dependency list may supply definitions after expansion to this
fragment or a separately checked semantic correspondence; names alone do not
establish that correspondence. Parameters include modulus, coefficient, input
contract and arithmetic interpretation. Bind them to each accepted artifact.

Pure client: `D_c(q) = (q, c*q mod 16)`, with `0 ≤ q < 16`, fixed `c=3` in the
bounded comparison. Observe both components; retain the selected encoder
`E(x,y)=x`, the decoder itself, `E(D(q))=q`, and `D(E(s))=s` only on the invariant
`y=3*x mod16`. Different syntax uses `q+q+q`. Changing c to 5 requires new
instance evidence or an explicitly uniform theorem, never reuse of c=3 evidence.

Stateful client from #490: `(x,y)` begins at `(0,0)`; admitted inputs `0≤d≤3`;
simultaneous update `x'=(x+d)%16`, `y'=(y+3*d)%16`, observation `y'`.
Selected target: `q=0`, `q'=(q+d)%16`, output `3*q'%16`, decoder D3 above.
Require related initialization, output agreement, and preservation of the whole
selected state relation `(x,y)=D3(q)` after every admitted input. The baseline
may keep both registers. Four persistent bits versus eight is not a claim about
total memory, work or latency. Exact integer temporaries in the old diagnostic
have six bits; modular four-bit execution requires a separate realization law.

## Candidate routes to assess

A. Native proof adapter: accept ordinary Lean proofs of correspondence for the
selected source declarations/typed explicit source, initialization, relation,
step and exact artifact. Kernel-check the theorem's full type at those exact
objects, not only its name. Generic compiler and continuation results should be
reused. Do not claim a complete Lean quotation/importer already exists.

B. Finite certificate route: a producer supplies an explicit pure input/output
table and a finite state relation/closure table. A separately proved checker
validates all admitted finite inputs, initialization, selected decoder agreement,
successor closure and exact output/artifact semantics. It must bind the original
source, parameters, primitive version, artifact and converter. This is distinct
evidence data/checking, not merely a wrapper around an assumed native semantic
record. A native Lean declaration still needs a checked declaration-to-source
connection; table validation of an unrelated AST cannot provide it. An external
explicit AST can instead be the original source under its specified semantics.

C. Reviewed complements: symbolic polynomial certificates, theory-indexed
interpretations/MMT publication and a common extensible proof language. Identify
which requirements they can discharge on these same examples, which facts remain
unproved, and what concrete need would justify selecting them for the first slice.
Do not reject a route merely because it lacks a current adapter.

For A/B, compare the same advertised semantic conclusions and selected data.
Possible first production scope may include both routes or stage them; distinguish
contract selection from implementation sequencing. Do not make the compiler host
language part of the general programmer contract.

## Composition and trust questions

Retain the integer-congruence to Z/16Z interpretation and its nonidentity
little-endian four-bit realization from #490. State evaluation and simultaneous
substitution laws, direct/composed agreement, and action on the selected decoder.
Integer order/exact intermediate bounds do not follow from ring equality. The
first map loses distinctions such as 0 versus 16; global reflection is invalid.
Both source programs and target must refer to the same selected parameter values.
Distinguish mathematical interpretation, effective execution, emitted artifact
association and physical/environment assumptions; these are particular relations,
not a universal hierarchy.

Require concrete decisions for stale/wrong program, changed coefficient or modulus,
unsupported primitive, wrong initialization, unpreserved integer distinction,
missing selected witness, changed representation, unmet input premise, and a
positive changed-syntax correspondence. Semantic admission without resource proof
must not claim a bounded or faster implementation. Unsupported original sources
must not enter a fallback interpreter that lacks their semantics.

## Evidence to inspect

- `FirstOrder.lean`: intrinsically typed Term, eval, compile_sound and explicit
  primitive Sound laws. `SquareKit/FirstOrderSubstitution.lean`: eval_subst.
- `SquareKit/ReactiveCompiler.lean`: source, initial/step/run/map_sound.
- `Applications/Progress/Reactive.lean`: run_related (generic finite traces).
- `Applications/FRP/RegionalAdmission.lean`: example-specific Realization and
  semantic_preservation; do not advertise this Bool/Input record as the generic
  integer record. RegionalSelection separates eligibility and ranking.
- `SquareKit/Internal/GraphTranslationValidator.lean`, GraphEmissionContract,
  GraphEmissionSquares, and `docs/research/graph-translation-validator.md`:
  checked bounded graph source/artifact precedent, not arithmetic admission.
- `docs/research/compiler-evidence-comparison.md` and
  `experiments/compiler-evidence/probe.py`: exact #490 examples, two different
  unverified Python checkers, mutations and 1,280 composed interpretation cases.
- `docs/research/mmt-compiler-evidence.md`: #492 preservation hypotheses, limited
  LF checks, failed composite attempt and missing arithmetic/source adequacy.
- `docs/language-direction.md`: mathematical targets, host independence,
  complementary presentations, local adoption and stronger-witness boundaries.

No new Lean formalization is requested by this decision task. The existing
Python replay and a bounded pure-client diagnostic may be executed by the main
agent; they are not checker soundness proofs. Source inspection and paper arguments
must be labelled as such. External claims need primary-source inspection; prefer
the already pinned local evidence when it answers the question.

## Independent perspectives and protocol

1. Contract/foundations: sufficiency, source connection, quantifiers, selected
   witness preservation, interpretation composition and rejection controls.
2. Implementation/use: exact caller and builder obligations, reusable proofs,
   immutable artifact binding, diagnostics, maintenance and host reimplementation.
3. Alternatives/generality: compare A/B/C on the same requirements; test whether
   a simpler or wider justified contract serves the clients without silent loss.

Inspect the pinned sources. Do not read other reviewers' reports or any root
recommendation until initial reports are saved. Return recommendation, strongest
retention evidence, concrete concerns with locations, smallest useful correction,
remaining discriminator, prior exposure and validation limits. Reports go to
`/tmp/conaled-699-evidence/{contract,implementation,alternatives}-initial.md`.
No source edits, tracker writes, other-session contacts or nested challenge.
Read-only checks are allowed; do not run parallel Lean builds. Three initial
reports will be preserved verbatim and reconciled before independent Standards
and Spec acceptance review. Agreement is not a correctness vote.
