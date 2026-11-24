# Independent contract assessment for #699

Input revision: `0d3865b344940510428e01f6907cb03dedbfe256`. Perspective: contract and foundations. This is decision preparation, not production adoption.

I recommend selecting one bounded semantic contract with two admissible evidence routes: ordinary Lean correspondence proofs and a separately proved finite certificate checker. Keep their evidence interfaces distinct. The contract should name the original source, explicit source meaning, admitted inputs, exact selected encoder/decoder, target semantics and artifact association. Implementing the native route first is defensible sequencing, but it must not silently make native Lean judgments the general source contract or describe the finite route as already implemented. The finite route is mathematically sufficient for both supplied finite clients once its checker and original-source association obligations are discharged.

The strongest retention evidence is the combination of the existing typed compiler theorem, substitution theorem and relational continuation theorem. Their quantifiers already cover the reusable work. `FirstOrder.lean:119` proves compilation sound for every intrinsically typed term and environment, given the primitive and cartesian laws in `Sound` at line 91. `SquareKit/FirstOrderSubstitution.lean:78` handles open simultaneous substitution, including let binders. `Applications/Progress/Reactive.lean:93` lifts local related-state preservation to output lists and final states for arbitrary finite related input lists. Neither evidence route needs a separate trace induction per program. The proposed comparison should retain these results and ordinary explicit-source clients.

## Exact conclusions and scope

Let `Q = {q : Nat | q < 16}`, `S = Q × Q`, and `U = {d : Nat | d ≤ 3}`. These are canonical representatives of residues; a signed integer presentation can be related separately. Fix coefficient 3 and modulus 16 in every source, interpretation, converter and artifact object. Define `D(q) = (q, (3*q)%16)` and `E(x,y)=x` as selected executable data.

For the pure client, require the exact original source function on every `q ∈ Q` to agree with the explicit source evaluation, and require the exact artifact interpretation to return both components of `D(q)`. Retain `E(D(q))=q` and `D(E(s))=s` on `I(s) := s.y=(3*s.x)%16`. The latter is false for unrestricted pairs, for example `(0,1)`. The round trips follow from these definitions and the invariant; they need not become independent caller proof fields if a shared specialization derives them. The selected operations must nevertheless remain identifiable in the conclusion. Existence of some encoder or decoder does not identify these operations.

For the initialized client, write `R(s,q) := s=D(q)`. Require related initialization and, for every `s,q,d`, `R(s,q)` and `d∈U` imply equal post-transition outputs and `R(s',q')`. The source transition is simultaneous and uses old `x,y`; the target transition is `q'=(q+d)%16` with output `(3*q')%16`. This supports all finite admitted traces from initialization, including the empty trace, and preserves the entire retained source state through `D`. It does not claim that every arbitrary source state is represented. Source `(0,1)` is outside this selected relation.

`ReactiveCompiler` already distinguishes the source evaluator from stored compiled target morphisms: `source`, `initial_sound`, `step_sound` at line 37, `run_sound`, and `map_sound` at line 73. Its current result uses the same state representation on the two sides. The compressed-state relation is additional instance evidence consumed by `run_related`; it is not supplied by `compile_sound` alone. `Applications/FRP/RegionalAdmission.lean:40,98` demonstrates this division with its selected `Realization` and `semantic_preservation`, but that record is specifically `Plan Input Bool` with a Boolean state observation. It must not be advertised as the required generic integer record.

The named fragment is adequate for the two clients: variables, nonnegative literals, addition, multiplication, final remainder, unit/products/projections and let, with finite acyclic dependencies. Existing `Term` supplies the structural syntax, but `FirstOrder`'s additive example lacks nonzero constants and arbitrary multiplication. A residue primitive interpretation and its laws remain required. Admission of a dependency name alone is insufficient. Require an expanded supported definition or a checked semantic connection under the exact parameter environment. The brief's restriction on recursion, effects, higher-order values and arbitrary opaque definitions should be preserved.

## Evidence route obligations

| Obligation | Native proof adapter | Finite certificate checker |
|---|---|---|
| Original source | Check a theorem at the exact native declaration, parameters and dependency environment, relating it to the supported source meaning. A source theorem's name or an unrelated true proposition is insufficient. | If explicit AST bytes are the original source, the specified parser/semantics provides the starting object. If a native declaration is original, separately establish declaration-to-AST correspondence. A table checked over an exporter result cannot establish that connection by itself. |
| Program meaning | Kernel-check the complete theorem type and proof at the selected source, target, assumptions and witnesses, under the repository's audited axiom policy. | Supply data tables. A proved checker evaluates the fixed source and artifact semantics itself and checks data agreement. Its successful result must imply the same semantic conclusions, without an assumed semantic-correctness field in the certificate. |
| Pure coverage | Quantification over every admitted input. | Verify coverage of all 16 admitted `q` values, uniqueness or an unambiguous table lookup, and exact pair outputs. A table that merely lists several valid samples is insufficient. |
| State coverage | Initialization and a universal local simulation over `R` and `U`. | Verify initial membership, decoder agreement, every admitted input for every relation row, successor membership and output agreement. Relate the accepted finite relation to the advertised `R`, rather than claiming a stronger universal relation without justification. |
| Selected data | The theorem's objects include `E`, `D`, initialization and selected target representation. | The checked manifest and data include the same selected objects. Validate their equations rather than accepting an existence flag. |
| Artifact | Prove that the particular target/artifact object denotes the transition used by the semantic proof; account for emitted and loaded representation if present. | Check the actual artifact interpretation against table semantics, or supply a separate proved emission/loader connection. Checking a producer's proposed semantics is insufficient for an unrelated executable. |

For this exact initialized example, relation coverage need not introduce a new independent assumption: initialization at `q=0`, closure under admitted input `d=1`, and the selected target transition force every canonical `q` to occur. Decoder agreement then fixes the corresponding source state. This is a paper derivation, not a new checked theorem. A production contract can either prove that coverage fact for this instance or check full coverage explicitly. The existing Python finite checker (`experiments/compiler-evidence/probe.py:171`) checks a supplied relation's initialization and closure, not an explicit global coverage condition. Its generic advertised conclusion should therefore remain finite simulation from the checked initial state until the stronger instance fact is established.

The existing graph validator is useful evidence for the source/artifact boundary. `SquareKit/Internal/GraphTranslationValidator.lean:33,69,77` checks an exact source-translated theorem type, actual theorem record, environment, body and metadata before deriving `Validated`. `GraphEmissionContract.ArtifactDenotes` and `GraphEmissionSquares.source_emission` connect particular core artifacts to source meaning. These are bounded graph results, not arithmetic importers. The documentation also retains the live-environment lookup, reification and compiled-checker boundaries. Reuse the discipline, not an unsupported claim that these files already admit arbitrary Lean arithmetic declarations.

Identity checks and semantic checks serve different purposes. A stale digest should reject an old receipt, but rebinding a changed object to a fresh digest must still run semantic checking. Bind the complete immutable objects used by validation and execution: original source/dependency snapshot, expanded source, input contract, primitive version, coefficient, modulus, observation convention, selected converters, target representation, artifact and evidence/checker version. If hashes are used operationally, state their identity assumption or confirm exact object equality; hashing does not prove source correspondence or authenticate provenance. The proof should quantify over those actual objects, with the driver responsible for handing the same objects to execution.

## Composition through nonidentity interpretations

Use a quotient interpretation `F` from the integer expression/congruence presentation into `Z/16Z`, and a representation interpretation `G` from residues to little-endian four-bit vectors. On scalar values, `F(n)` is the residue of `n`; `G` is the selected bit encoding. Extend both componentwise over products and environments. The required evaluation equations are of the form

```text
F(eval_Z(t, ρ)) = eval_R(F(t), F(ρ))
G(eval_R(u, ν)) = eval_bits(G(u), G(ν))
```

with the relevant canonical-representative comparison where an integer output is requested. The corresponding open substitution equations are `F(t[σ]) = F(t)[Fσ]` and the analogous equation for `G`, under their chosen syntax or semantic equality. Prove them from variable, literal and primitive clauses, then extend over unit, products, projections and let. The state substitutions are simultaneous. `eval_subst` establishes the existing single-meaning substitution fact; the inter-interpretation compatibility still requires the new primitive/value relation laws.

Composing the evaluation equations gives direct/composed agreement for every supported term and valuation, including let-bound open terms. Check the selected decoder explicitly:

```text
(G×G)(F×F)(D_Z(q)) = D_bits(G(F(q)))
```

for canonical `q`, with `E`'s corresponding projection equation. This preserves selected data pointwise; it does not identify independently produced proof objects. The report's nondependent fragment does not establish preservation of arbitrary dependent witness types or their transport coherence.

The first map loses integer distinctions: `F(0)=F(16)`. Thus it cannot reflect unrestricted integer equality, order, or exact intermediate bounds. The execution contract must retain integer range premises separately. Four-bit modular add/multiply can implement final residues once `G`'s operation laws are proved. That does not make four-bit exact multiplication correct: `3*15=45` exceeds a four-bit exact result. Six-bit exact temporaries suffice for the old fixture's specified expressions, as recorded in #490; this is separate from the proposed modular implementation.

The #490 diagnostic compares five expressions at 256 pairs of variable values, as confirmed by its `self_test` loop. Those 1,280 checks cover neither all fragment syntax nor checker soundness. The #492 arithmetic composition argument is paper evidence. Its reported LF checks and failed composite attempt must not be upgraded to a checked arithmetic/source correspondence chain. I did not rerun or independently inspect external MMT sources in this assessment; these are limits of the pinned study, not fresh claims about the framework.

## Concrete admission decisions

These cases should be part of the conditional implementation specification. Rejection of supplied evidence should be distinguished from a proof of semantic impossibility.

| Case | Required decision and reason |
|---|---|
| Old evidence with a changed source or artifact | Reject stale identity binding. After rebinding, require fresh semantic acceptance at the actual objects. |
| Source coefficient changes from 3 to 5; target and decoder remain at 3 | Reject correspondence. At initialization followed by `d=1`, the source output is 5 and target output is 3. The pure client also differs at `q=1`. |
| All objects change coherently to coefficient 5 | Old instance evidence remains invalid. Fresh evidence or an explicitly uniform coefficient theorem may admit the new instance if the selected scope allows it. The bounded comparison itself remains coefficient 3. |
| Modulus becomes 8 | Old binding and four-bit residue interpretation cannot be reused. Classify as unsupported by the selected modulus-16 slice unless a separate instance and realization are supplied; it is not a theorem of impossibility. |
| Saturating multiplication or an opaque foreign primitive | Refuse the unsupported semantic connection. Do not run a fallback interpreter that only implements exact nonnegative arithmetic. |
| Source initialization becomes `(0,1)` or target initialization changes alone | Reject selected initial relation before any step, including an empty input trace. |
| Claim integer `0=16` because their residue images agree | Reject the unpreserved property. Forward congruence preservation supplies no global reflection. |
| Selected decoder absent, or replace it with `(q,q)` | Reject missing/incorrect selected data. At `q=1`, `(1,1)` fails the required `(1,3)` state. An existential decoder theorem is insufficient. |
| Replace selected encoder by constant zero | Reject its round-trip obligation, already at `q=1`, even if execution's output trace is unchanged. This tests whether the advertised encoder was retained. |
| Change little-endian representation or declared width without a new interpretation | Reject stale representation binding and require the relevant operation/decoder law. Same residue values alone do not establish the bit-level artifact contract. |
| Feed `d=4` or pure `q=16` | Reject at the admitted-input boundary before executing the affected operation, unless a new contract/evidence extends the domain. The arithmetic might happen to work, but the selected theorem does not authorize that use. |
| Replace `3*q` by `q+q+q` | Accept with fresh binding and checked correspondence, preserving both pure outputs and all local state obligations. Syntax identity is not required. |
| Semantic evidence succeeds without a resource proof | Permit only the semantic conclusion. Do not claim bounded total storage, speed or latency. A four-versus-eight persistent-state-bit claim requires its named layout model. |

## Complements and smallest correction

Symbolic polynomial certificates can discharge the residue equations without enumerating inputs; #490's polynomial checker is distinct from a native proof adapter and currently unverified Python. It does not by itself discharge initialization, selected witness identity, original-source association, integer bounds or artifact execution. It becomes useful when symbolic reuse across coefficients/moduli or repeated larger finite domains gives a concrete reason to add a proved normalization checker. The finite checker remains sufficient for this fixed domain, regardless of whether it has a current adapter.

Theory-indexed interpretations and MMT publication can name and organize the two interpretation steps. A valid theory view alone cannot identify the original program or emitted artifact. Select that mechanism for the first slice only if a named consumer needs reusable published theory/view composition and the required source adequacy and selected-data comparisons are provided. A common proof language would need rule soundness, a justified translation of source judgments, and retained witness semantics. These clients supply no failed requirement that makes such a language necessary before bounded admission. Defer that larger selection without asserting that the language cannot serve these examples.

The smallest useful correction is to make original-source correspondence and the exact common semantic conclusion explicit in the decision packet, then state the two distinct routes that may establish it. Add pure input coverage and selected encoder recovery to the finite route's acceptance criteria. Derive relation coverage and round trips where available; avoid demanding redundant per-caller proof fields. Preserve explicit-source and native direct entry points. An implementation outside Lean must retain the same mathematical judgments and exact object associations, and either provide a checked implementation refinement or state the additional trusted checker/parser/runtime assumptions. The compiler host language alone settles none of those obligations.

No missing mathematical fact blocks this bounded contract recommendation. The single next implementation discriminator is an end-to-end, kernel-checked instance starting from the selected original-source form, carrying both evidence routes to the same semantic conclusion at the exact artifact and selected `E,D`, with the changed-syntax positive case and a freshly rebound wrong-source case. If the chosen original form is a native Lean declaration, the declaration-to-supported-source connection is the first prerequisite of that discriminator. A successful table checker over unrelated ASTs would not pass it.

## Independence and validation limits

I received only the shared brief, issue requirements and this perspective assignment, then inspected the pinned code and studies named above. I did not read other initial reports or a coordinator recommendation, contact another session, perform tracker operations, edit source files, run Lean builds, or execute the Python probe. The local Git status was clean when inspected. I have no prior task involvement established in this conversation; the brief and prior studies themselves contain proposed recommendations, so this is not an assessment without exposure to candidate arguments.

This report distinguishes inspected existing theorem statements/proofs, reported historical checks, and new paper reasoning. It does not establish current build/audit success, production checker soundness, parser or driver correctness, complete quotation/importing, or physical deployment assumptions. All new equations and separating cases here are paper-level specifications for the conditional implementation and acceptance review. Only this report was written, outside the source tree.
# Circuit-source supplement to the independent contract assessment

This note follows the saved initial assessment. The coordinator supplied an additional factual pointer to `Applications/Circuits/Words.lean` and `Execution.lean`; no other perspective or recommendation was disclosed. I inspected those files at `0d3865b344940510428e01f6907cb03dedbfe256`. The initial report remains unchanged.

`Words.lean:36,41` proves the encode/decode round trips between `BitVec n` and the product-shaped Boolean representation. Lines 133–142 define modular circuit addition and prove that decoding its execution equals `BitVec` addition at arbitrary width. `Execution.lean:19,28` defines structural execution and proves agreement with the circuit's digital value. These give concrete reusable ingredients for the selected four-bit realization.

For these coefficient-3 clients, two modular additions compute `3*q`, and likewise `3*d`; composition and pairing can retain the selected first component. This is a proposed specialization using the inspected proofs, not a checked construction produced by this assessment. It makes a circuit execution endpoint plausible without a multiplication primitive. The remaining contract obligations include the integer/residue comparison, selected `D/E` equations, initialized simulation, exact chosen circuit association, and any emitted-byte or runtime connection being claimed.

The full named source fragment includes multiplication of two variable expressions. The inspected word addition result does not establish such a lowering. A decision packet should choose one of three precise scopes: add and prove a general modular multiplication lowering; keep the full source semantics/evidence fragment but expose circuit realization only for the separately supported subclass; or narrow the first source slice explicitly. A checked semantic rewrite of this selected constant multiplication into addition suffices for these examples, but does not prove a compiler for arbitrary multiplication. This affects implementation sequencing and supported executable targets, not the sufficiency of the native-proof or finite-certificate semantic contracts.

This source inspection supports reuse and does not change the initial recommendation. No builds or experiments were run, and no source files were edited.
