# Checked internal proof authoring (#50)

## Question and provenance

Does a bounded helper interface remove obligations from authors of graph,
associativity, Frobenius, and a nested interval application? This investigation
implements [#50](https://github.com/VladimirMarko/conaled/issues/50), whose
requirements were updated on 2026-10-18, starting at the accepted #46 commit
`bf44600db27758b7346731233a4109cbcab4bf7b`. It compares checked derivations over
the existing restricted calculus. It makes no usability or performance claim
beyond these cases.

The earlier [frontend experiment](../history/internal-language-frontends/Frontend.lean)
is unchanged. The new comparison is retained in
[`Examples.InternalAuthoring`](../../Examples/InternalAuthoring.lean).
Its `Direct` and `Helpers` namespaces are experimental evidence, not an
additional supported frontend. They intentionally repeat proofs to compare
caller obligations. Both use the same formula definitions and `Derives` types.
Graph and associativity baselines remain the unchanged `Graph.forward/backward`
and `Associativity.forward/backward`; direct Frobenius and nested proofs are
in `InternalAuthoring.Direct`.

## Derivation and application

The initial missing connection was source derivability for arbitrary `H` and
`P`. The semantic presheaf Frobenius law already existed. A concrete Set
logical equivalence could already be proved directly, but that would not
connect the consumer to the source calculus.

`SquareKit.Internal.Substitution` supplies syntax identity and composition
laws, including composition through lifted substitutions. The head-witness
cancellation law states that inserting a context variable below a binder and
then instantiating at that variable restores the original formula body.
`Rules.existsHere` uses this equality with the existing existential introduction
rule. It proves `P ⊢ (∃ P).shift` without a semantic premise.

`Frobenius.forward` and `backward` derive
`H ∧ (∃ x, P) ⊣⊢ ∃ x, H.shift ∧ P`. `H` is a formula in the outer context;
it cannot mention the new witness. The forward proof uses retained-assumption
elimination. The reverse eliminates the witness and builds the conjunction.
`Frobenius.inSet` applies Set soundness to these exact derivations.

`Presheaf.frobenius_valid` applies `Model.sound` to the same proofs and obtains
equality of context subfunctors. `frobenius_semantic_comparison` independently
specializes the existing semantic law to these interpreted predicates. That
law has `P` first; commuting both intersections gives the source's `H`-first
order. `Model.formula_substitution` identifies weakening with preimage along
projection. `frobenius_evaluation` obtains the objectwise Set equivalence from
validity and the general `Model.evaluation` theorem. Neither comparison is
used as an escape from source derivability.

`ConditionedComposition.forward/backward` combine relational associativity
with Frobenius. The antecedent has witnesses in the order C then B; the
conclusion binds B then C and retains R, S, T and the fixed context condition.
The outer existential body still contains an inner existential. The condition
is moved under the outer binder; this experiment does not flatten or move it
past every conjunction under the inner binder.

`Relational.compRel_condition` exposes the interpreted derivation to ordinary
callers. `IntervalAnalysis.nonnegative_composition` specializes it to the
existing `representation.Rel` (interval containment), any interval-producing
relation R, any rational realization relation T, and `0 ≤ z`. The output z
is free and fixed while both intermediate witnesses vary. R, containment,
and T are all retained; no decoder, well-formedness assumption, or choice of
a unique contained point is introduced.

## Obligations compared

| Caller obligation | Named rules and direct syntax | Bounded helper variant |
|---|---|---|
| Formula construction and variable addressing | Typed `.zero`/`.succ` positions; graph context `[a,c]`, associativity `[a,d]`; author calculates positions under each binder. | Identical formulas and positions. Helpers do not name or infer variables. |
| Arbitrary-body shifting | Direct Frobenius writes the lifted shift, `.zero` witness, and cancellation rewrite in each direction. | One `existsHere` call per direction discharges those insertion and cancellation obligations. Author still writes `H.shift` and chooses which body to introduce. |
| Witness selection | Graph reverse chooses `f(a)`; each associativity direction chooses the head and then the next variable. | Same witnesses. The graph reverse uses the already-existing `existsWitness`; the helper does not find a witness. |
| Assumption rearrangement | Associativity forward explicitly swaps the conjunction before `existsElimWith`. Nested proofs project H and cut the other branch through associativity. | `eliminateLeft` owns the swap; `frame` owns the projections and cut. Remaining projections in associativity are unchanged. |
| Required annotations | Sort/signature parameters, formula context types, and explicit `F := F` where relations alone cannot determine the arrow signature. The direct head-introduction proof specifies its body and lifted substitution. | Same declaration annotations. `existsHere` needs the body, but no separate substitution annotation. Helpers infer retained assumptions from the expected sequent. |
| Repeated proof work | General syntactic cancellation must be proved once, then applied explicitly at each arbitrary-body witness introduction. | Same cancellation proof, hidden at call sites by `existsHere`. Graph forward and associativity backward receive no new benefit. |
| Set model adapter | Carriers, arrows, relation predicates; use `sound`. | Identical. No helper-specific interpretation or soundness proof. |
| Presheaf model adapter | Sort functors, natural arrows, stable product predicates; use `Model.sound` and `evaluation`. | Identical. No new naturality, substitution or Frobenius fields. |
| Ordinary application caller | Supply R, S, T, H and endpoints to `compRel_condition`, or R, T, input and output to the interval specialization. Establish hypotheses for concrete instances. | Identical public calls. No syntax, environment, model argument, conversion, instance setup, or repeated logical proof. |

These are obligations visible in the checked source, not timings or a count of
proof lines. `frame` and `eliminateLeft` remove specific rearrangements, but
leave typed addressing, witness selection and most projections untouched.
The graph regression confirms that adding helpers does not automatically
improve an already short proof. The comparison does not test a custom
elaborator, named binders, proof search, or translation of arbitrary Lean proofs.

## Checked cases and statement review

[`Examples.Frobenius`](../../Examples/Frobenius.lean) connects the following
independent expectations to the public interpreted results:

- The interval `[-2,3]` contains 1, and realization `z = x + 1` gives output 2.
  `accepted` transports that two-witness fact through `nonnegative_composition`.
- The same relation realizes -1 from -2, but `rejected_negative` rejects its
  nonnegativity condition. `negative_realization` establishes that the relation
  premises themselves are satisfiable.
- Output 5 is nonnegative but would require the contained value 4.
  `rejected_outside` uses the interpreted reverse direction and the retained
  containment and realization hypotheses to derive the contradiction.
- An empty intermediate carrier cannot gain a witness by rearrangement.
- `Capture.same_sort` puts the free output and witness in the same rational
  sort. `shifted_rejects` rejects a negative free output even though the witness
  predicate is reflexive; `captured_accepts` shows that incorrectly testing the
  witness instead would accept 0. Types alone cannot detect this scope error.
- The two-stage presheaf from #46 supplies a fine witness `(2,7)` under free
  sections `(3,9)` and `(4,0)`. The evaluated source theorem supplies the fine
  existential; `formula_restrict` transports it to the coarse object. The
  semantic comparison is instantiated on the same nonconstant model.
- A local sequent notation mixes direct and helper proofs beside unchanged
  `Graph.inSet`, interval addition and rational numeral instances. The helpers
  install no notation or instances; the local notation ends with its section.

Statement review covered every new declaration by the following dependency
groups. Syntax laws quantify over arbitrary typed substitutions, including
under binders; their conclusions are equalities of syntax, not semantic
validity. `lift_shift_instantiate` identifies the head witness and keeps every
older variable's position. `existsHere`, Frobenius, framing and left elimination
produce restricted sequents only. They add no constructors, assumptions,
connectives or inhabitedness requirements. The direct and helper graph,
associativity and nested statements have identical endpoints and conjunction
order. Existing graph/relation clients remain imported unchanged.

The model claims distinguish subfunctor equality, Set equivalence and the
comparison between them. Existential witnesses are sections at the selected
object, not global sections. The nested model interprets its condition symbol
as a predicate on the free output; its second binary argument is intentionally
unused because the restricted signature has only binary atoms. The public
relation theorem quantifies over arbitrary relations and keeps both
intermediate witnesses. The interval specialization reuses the existing
many-valued representation, including its behavior on reversed bounds.
Concrete positive and negative instances establish nonvacuity and check which
hypothesis rejects each endpoint. Helper declarations add proofs in `Prop`;
the ordinary runtime representations are unchanged.

During elaboration, polymorphic function equalities in substitution proofs
needed explicit implicit sort binders. The concrete rational witness needed
an explicit `ℚ` annotation because typeclass search did not unfold the model
carrier. Rational `1 + 2 = 3` required normalization rather than definitional
equality. These were local elaboration obligations; the existing public
call sites needed no changes. No elaboration-speed measurement was made.

## Run and audit

From the repository root:

```sh
direnv exec . lake build Examples.Frobenius
direnv exec . ./check.sh
```

The first command checks the comparison module, new application, and their
retained examples incrementally. The second recompiles all project modules
from source and runs the exhaustive transitive axiom audit with the existing
whitelist. Both comparison variants are imported by the public entrypoint
through `Examples.Frobenius`, so no separate experimental audit exemption or
temporary artifact is needed. The original historical experiment keeps its
own existing run instructions and contents.

## Stage A assessment and recommendation

The #38 and #45 slices established graph and arbitrary-relation source proofs
and ordinary Set consumers. #46 added the constructed presheaf interpretation,
soundness, and evaluation comparison. This investigation adds a source
Frobenius proof reused across those models, a two-witness interval consumer,
and a checked comparison of bounded authoring helpers.

Adopt `Rules.existsHere` as a bounded helper alongside the current named rules.
It removes a repeated, formula-generic substitution obligation in both
Frobenius directions. Keep `frame` and `eliminateLeft` as preserved experimental
evidence for now: the cases demonstrate their limited effect but do not yet
justify a broader assumption-management interface. Existing callers need no
migration. If another proof needs repeated framing or right-retained
elimination, promote the corresponding checked lemma individually.

This supports the tested Stage A fragment and its semantic separation. It does
not complete Stage B, establish general authoring usability, or select another
model interface. Named-variable addressing, larger signatures, deeply nested
assumption search, and elaboration cost remain untested. Those gaps do not
supply evidence for a full sheaf, dependent, geometric, or cohesive architecture.
