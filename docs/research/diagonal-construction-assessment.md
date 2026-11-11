# Diagonal construction and interpretation laws

This is the bounded investigation for [#444](https://github.com/VladimirMarko/conaled/issues/444),
following [Paradoxes and theorems](paradoxes-and-theorems.md).
The [native contract](diagonal-construction-contract.md) preceded the formal
interface. The checked implementation is
[DiagonalConstruction](../../SquareKit/DiagonalConstruction.lean), with
[consumers](../../Examples/DiagonalConstruction.lean).

## Construction, interpretation, and consequence

The construction has two independent carriers: codes `A : Type u` and values
`Y : Type v`. Evaluation `e : A → A → Y` and an operation `h : Y → Y` determine
`diagonal e h a = h (e a a)`. `Selected e h` retains a particular code `c` and
pointwise representation evidence `∀ a, e c a = h (e a a)`. Evaluation at that
same code gives the selected witness `e c c`; `Selected.fixed` proves it fixed.
This is a conditional proof. There is no axiom asserting representation for
arbitrary evaluation or an evaluator for unrestricted truth.

The direct baseline calls Mathlib's
[`Function.exists_fixed_point_of_surjective`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Function/Basic.lean#L367).
`Selected.ofSurjective` additionally chooses and retains a code. Choice occurs
in this optional constructor; the proof from a supplied `Selected` needs no
search or choice. Selecting a code for this particular diagonal is weaker
than representing every function. The Boolean constant-false consumer is
inhabited although its two constant rows cannot represent every Boolean function.
The singleton consumer satisfies even the full surjectivity hypothesis.
Boolean negation has no fixed value, so `no_negation_representation` rejects
selected representation, and `no_boolean_surjection` rejects full coverage.

[Lawvere, *Diagonal Arguments and Cartesian Closed Categories*, pp. 136–138](https://www.its.caltech.edu/~matilde/LawvereDiagonalArgCartesianClosedCats.pdf)
proves the corresponding categorical result from weak point-surjectivity.
His points are global elements; they need not detect equality of morphisms.
The Set fixture here uses pointwise equality of functions and retains one
chosen representative for one operation. It does not formalize the full
categorical theorem, its presheaf embedding, or a general truth interpretation.
The paper also explains the finite-product formulation without exponentials;
our native proof requires neither a CCC interface nor exponentiation laws.

## Maps and the failed stronger law

`Map e h e' h'` contains a code function `f : A → B`, a value function
`g : Y → Z`, and precisely these local laws:

```
g (e a b) = e' (f a) (f b)
g (h y)   = h' (g y)
```

Thus the evaluation square has upper arrow `e : A × A → Y`, lower arrow
`e' : B × B → Z`, left arrow `f × f`, and right arrow `g`. The step square
has upper arrow `h`, lower arrow `h'`, and both vertical arrows `g`.
`diagonal_preserved` combines these squares at repeated inputs. These are
ordinary function equalities, not an unspecified truth-preservation relation.
Identity, composition and associativity are checked for these records. No
category instance, equivalence of arbitrary theories, or generic functor is
claimed.

To transport a selected representation, `Map.selected` additionally takes
surjectivity of `f`. Its proof reaches each target input by a source input.
`witness_preserved` retains the selected value, including which code produced
it. Surjectivity is sufficient here, not claimed necessary for every map.

The rejected stronger rule would remove that coverage premise. The consumer
`partialPresentation` has source codes `Unit`, target codes `Bool`, Boolean
values, identity steps, and sends the sole code to false. Source evaluation
is constantly true; target evaluation is `e' b a = !b`. Both local laws hold,
and the source code represents its diagonal. But at target input true the
translated row evaluates to true while the target diagonal is false.
`cannot_transfer_representation` checks this contradiction. The failure is a
missing input obligation, not a map arbitrarily changing a designated truth.

The alternative is a covered map. Independent equivalences of code and value
carriers construct `presentationMap`; `recode_recover` and `restep_recover`
recover evaluation and the step operation, while `recover_code` and
`recover_witness` recover the selected observations. This tests the alternative
on the same diagonal contract. It does not repair the rejected map by silently
changing its target.

Forgetting from selected constructions to their fixed-point values is also
checked to lose information: `witness_forgetting_not_injective` uses two
Boolean codes with singleton values. Both satisfy representation and yield
the same value, but their codes differ. Consequently the forgotten value
cannot support a left inverse recovering every selected code. Forgetting this
information alone produces no contradiction. The paradoxical Boolean
presentation appears only when one additionally demands incompatible
representation and negation laws.

## Existing interpretation routes

| Route and decision | Reused proof and remaining obligations | Cost for this fixture |
|---|---|---|
| Direct Lean/Mathlib: adopt | Existing existential theorem; supplied selected representation yields the fixed witness. | Two carriers, evaluation, step, and one representation equation. This remains the native entrypoint. |
| Construction maps: adopt | Evaluation and step laws compose; diagonal and selected witness preservation are reused across presentation changes. | Two functions and two local laws, plus code coverage when representation must transport. |
| Existing compiler: adopt for construction; reject as automatic representability transport | `Compiled.term` duplicates the same bound variable. `compiled_diagonal` calls `CategoricalCompiler.compile_sound`; `compiled_selected` combines that result with the selected proof. A `rawTarget`/`rawSound` Boolean consumer supplies all backend obligations. | Existing compiler has one base sort, so this consumer specializes to `A = Y : Type`. General `Sound` supplies the entire supported signature's laws, although this term uses only variables, pair, primitive and composition. No source-program substitution or new compiler correctness proof is needed. |
| `DependentTheoryMaps.TheoryMap.transport`: investigate for a derivation-level successor; defer encoding this elementary proof | Local certificates translate each rule using images of its indexed premises; `transport_graft`, identity and composition preserve derivation assembly. | Must first encode judgments, representation assumptions, equality rules and certificates. The current fixture's native equality proof does not automatically become a derivation in that interface. |
| Institution `ProofMap`: defer for this fixture | Its `map` and `commutes` require proof translation and compatibility with semantic evidence under a `Connection`. | Must supply both proof systems, interpretations, sentence/model/evidence connection and its laws. It neither discovers a proof map nor supplies missing reflection. |
| Map to an erased paradox presentation: reject as unconditional theorem transport | Code erasure and local evaluation preservation are useful, but neither implies target representation or sound truth rules. | A usable theorem map would need those additional certificates; the retained counterexamples exclude the proposed unrestricted shortcuts. |

The compiler retains bindings through its existing `Var`/`Term` types; both
variable occurrences are `.here`. It compiles the construction, not a syntax
of the fixed-point derivation. The native interface has no object-language
substitution operation to preserve. In contrast, `TheoryMap` retains indexed
premise occurrences and its graft law explicitly addresses substitution of
derivations. These are different observations, not interchangeable meanings
of proof transport.

Existing [UniformOperations](../../SquareKit/UniformOperations.lean) already
recovers selected syntax from an explicit naturality law and rejects uniform
choice under its stated equivariance requirement. It motivated retaining the
selected code here, but its finite-variable result is not this diagonal theorem.
[AssemblyCutFold](../../SquareKit/AssemblyCutFold.lean) already uses
`Code.fixed_point₂` for a computable program equation. That recursion theorem
concerns program evaluation and its computability obligations, not surjection
onto all total functions. [SelectedFeedback](../../SquareKit/SelectedFeedback.lean)
retains a chosen feedback witness and adds output congruence or guarded
uniqueness where needed. This fixture does not infer uniqueness or unrestricted
trace from its selected fixed point. None of these existing results is replaced.

## Curry–Löb: paper-level test

[Löb, *Solution of a Problem of Leon Henkin*, pp. 115–117](https://math.umd.edu/~laskow/Pubs/713/Lob.pdf)
assumes deductive closure, definable substitution and stated provability
conditions. The conclusion is: if `T ⊢ □A → A`, then `T ⊢ A`.
A modern derivation uses necessitation, distribution
`□(P → Q) → (□P → □Q)`, positive introspection `□P → □□P`, and a diagonal
sentence `L ↔ (□L → A)`:

1. Necessitate `L → (□L → A)`. Distribution and introspection yield
   `T ⊢ □L → □A`.
2. Given the theorem `□A → A`, derive `□L → A`, hence `L`.
3. Necessitate `L`, then obtain `A`.

The paper's original conditions are not literally this modern three-law list.
Its final paragraph gives the truth-based paradox. With transparent truth,
`C ↔ (C → A)` yields `C → A` by assuming `C` and applying its forward
implication, then yields `C`, then `A`. Erasing provability into transparent
truth would therefore add a reflection rule absent from the proof above.
Consistency is unnecessary for Löb's implication itself. For consistent `T`,
its instance `A = ⊥` excludes a theorem `□⊥ → ⊥`. External soundness is not
an internal theorem asserting reflection.

For a successor experiment, the proposed bounded syntax is a graph with a
named self-reference node, a quotation edge to that node, an implication node
with parameter `A`, and an operation tag `Truth` or `Provability`. Forgetting
the tag preserves the graph and its binding/reference edge. The above two
rule traces give distinct interpretations of this graph. A naive inverse
that inserts `Provability` while retaining the transparent-truth elimination
rule would need a certificate for reflection; at bottom the stated consistency
condition excludes it. This is an obstruction to that rule map, not an
obstruction to retaining the graph. No total truth evaluator is needed.

This syntax and rule comparison is assessed on paper, not implemented Lean
arithmetization. A checked successor would have to specify quotation and
capture-avoiding substitution, prove or explicitly parameterize a diagonal
lemma, define its derivation calculus, and certify necessitation, distribution
and introspection. It must keep theorem-level necessitation distinct from
necessitation under arbitrary hypotheses. The arithmetic realization of those
conditions and consistency assumptions would remain separately owned.
A Boolean semantic fixed point is not a syntactic diagonal lemma.

## Statement review and development evidence

The native obligations were fixed before the shared map interface. The
examples expose the required selected witness, a satisfiable strong premise,
and a failure of a plausible weaker map contract. Implementation failures due
to missing imports or elaboration are not mathematical counterexamples.

| Claims | Statement review |
|---|---|
| `Selected.fixed`, `baseline`, `ofSurjective` | `A` and `Y` have independent universes. The selected code is data in `Type`; representation is evidence in `Prop`. The theorem proves the fixed equation for that code, while the baseline concludes only existence. The optional choice constructor makes no computational search claim. |
| `Map` laws, identity/composition, `diagonal_preserved` | Evaluation quantifies over both source codes; it says nothing about target codes outside the image. Step preservation quantifies over all source values. Composite laws reuse both component laws. |
| `Map.selected`, `witness_preserved` | The target code is exactly the translated source code. Coverage is an explicit additional hypothesis. Witness equality is through the supplied value map; no injectivity or uniqueness is assumed. |
| Presentation recovery | Independent equivalences recover the raw evaluation and step functions and selected code/value. Recovery does not extend to arbitrary noninvertible maps. Proof fields are propositions; their syntactic derivation trees are not retained. |
| Boolean rejection and positive consumers | Obstructions have supplied hypotheses, not new axioms. The singleton surjection and Boolean selected case demonstrate inhabited inputs. The omitted-code counterexample satisfies both local map laws. |
| Compiler consumers | The public compiler theorem supplies denotation equality. The actual raw backend satisfies `Sound`; the selected result still uses representation evidence. This checked compiler comparison has one base carrier in universe zero. |
| Erasure consumer | Noninjectivity concerns the code retained in `Selected`, not proof irrelevance. Equal values with distinct codes rule out arbitrary full recovery from values. |

Focused checks, acceptance results and review dispositions are recorded in the
candidate handoff. A successful focused compilation alone is not the required
integrated build and exhaustive proof audit.

## Discovery and follow-up ownership

The fixture exposes obligations that a tool can display: the representation
equation, code coverage needed by a selected transfer, backend soundness laws,
and rule certificates needed by a derivation map. Checking a proposed
certificate is already meaningful. Finding a suitable evaluation, a useful
carrier translation, the right equality notion, or a rule correspondence
still requires search and mathematical judgment. The sufficient hypotheses
here are not claimed weakest. No author trial was conducted, so no productivity
or automatic theorem-discovery result follows. This respects the distinction
in [the requirement trial](proof-requirement-author-trial.md) and the
[theory-network comparison](theory-network-comparison.md).

Adopt the selected native fixture and its covered construction maps. Retain
the compiler application as a construction-preservation consumer. Investigate
the bounded tagged self-reference/rule-certificate experiment under
[#290](https://github.com/VladimirMarko/conaled/issues/290), coordinated with
[#235](https://github.com/VladimirMarko/conaled/issues/235). Its acceptance
should require both a Curry derivation and a Löb derivation in an explicitly
chosen calculus, a structure-preserving tag erasure, and a checked failure of
the extra reflection certificate under explicit consistency assumptions.
The diagonal lemma may be a named conditional interface initially, but the
report must not present that interface as proved arithmetization. Compare
`TheoryMap.transport` against the native derivation before adding a universal
syntax. Root orchestration owns publication and deduplication of this proposed
successor; this report does not assert that a new issue has been created.

Defer general categorical Lawvere formalization until a consumer needs it;
[#109](https://github.com/VladimirMarko/conaled/issues/109) remains the owner
for recursion/compiler interpretations. Reject automatic theorem transport
from unqualified code erasure, unrestricted truth interpretation, and the
claim that compilation proves representation. These boundaries leave the
existing compiler, selected-feedback and computable-recursion results intact.
