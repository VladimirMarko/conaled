# Alternatives and generality assessment

Retain native `combine` and its `Combination` recovery contract. The evidence supports investigating operation-transport helpers before a shared signature-amalgamation interface. The two current examples vary carriers, observations and action algebra, but exercise one operation shape. They do not establish recurring author work across different operation families. This is a limit on the evidence for adoption, not a reason to exclude a competing foundation from research.

The strongest retention evidence is the conjunction of complete ordered-state recovery with a noninjective observer, and the rejection theorem over alternative joint carriers. `Examples/NativeModelCombination.lean` supplies `observation_not_injective`, `right_recovers_order`, `no_invariant_alternative`, and the independently constructed `flipped`. These demonstrate a useful contract beyond the formula `o ∘ e`: actual recovery maps let the theorem reject invariance in every presentation with the same overlap. Removing the result contract in favor of only direct composition would lose that public quantification boundary.

## Source and exposure

I inspected commit `e80c51d968925be3809ba3acc3259de7041b504b` in `/tmp/conaled-wave-20261111/design-challenges/source`, including the complete `Applications/ModelCombination/ActionObservation.lean` and `Examples/NativeModelCombination.lean`, their two linked research records, `SquareKit/Combinators.lean`, and `SquareKit/Institutions/Capabilities.lean`. I inspected the declaration inventory of `SquareKit/RepresentationExtension/Models.lean`, not all its implementations. Applicable architecture, domain, language-direction and statement-review guidance informed this assessment. ADRs 0002 and 0010 preserve distinctions between relational recovery and isomorphic recovery and between construction and independently specified composition evidence.

This agent has no prior involvement in the implementation and received only the common brief and this lens assignment. I did not read another lens report or coordinate conclusions. The agents use the same model family; this is no evidence of model diversity. Source inspection and the paper arguments below are the only validation performed. No Lean experiment, build, audit, external literature verification, or author-effort trial was run. Existing research reports are historical evidence, not independent verification of their external citations. I make no new attribution to those external papers.

## What the current construction already derives

`Combination` (ActionObservation.lean:24) requires supplied equivalences `left : Z ≃ X` and `right : Z ≃ Y`, preservation of the state points, the separate result constant, action preservation through `left`, and observation recovery through `right`. `combine` (line 41) constructs those fields with identity left recovery and `out := o ∘ e`.

The API already derives the useful consequences: `overlap_point`, `out_eq`, `left_reduct`, `right_reduct`, `mixed`, `action_output`, and `output`. In particular, `mixed` follows from `mul_smul` for every observer. It supplies no evidence that arbitrary interaction laws can be generated. `differentConstant` and `independent_result_constant` reject any proposal to make the result constant equal to the point observation without changing the admitted models.

A potential comparison helper is also derivable. For two results C on Z and C' on Z' with the same supplied overlap e, define `h := C.left.trans C'.left.symm`. Then h preserves the points and action, and `C'.out (h z) = C.out z` follows from the two `out_eq` equations and the equal-overlap equations. The inverse action preservation needed here follows by applying the injective `C'.left` and cancelling its inverse. No new proof field should be requested of the caller. This is a paper derivation, not a checked declaration. It would be worth extracting only when a consumer compares presentations; the current rejection theorem already works without it.

## Competing formulations

| Candidate | Inputs and mathematical capability | Evidence that would justify it |
|---|---|---|
| Native records and function composition | Existing action, observer, explicit pointed equivalence. Current constructor and recovery results remain direct. | Already supported by both native callers and `flipped`. |
| Transport of operations along equivalences | For an operation whose input and output carriers change, conjugate by the input equivalences and inverse output equivalence. Prove recovery and transport its stated equations. | A second operation shape exposes repeated cancellations or law-transport proofs that helpers actually remove. |
| A many-sorted equational signature interface | Named sorts and operations, explicit common reduct isomorphism, and side equations. A term interpreter can prove operation/equation recovery uniformly over open terms. | Multiple independent signatures and changed arities reuse the same construction and induction; existing native callers remain usable without manual syntax bookkeeping. |
| Relational or synchronized recovery | A relation or compatible decoded values can admit redundant or unequal carriers. | A client explicitly needs this weaker recovery and supplies operation compatibility. The singleton rejection must remain scoped to invertible recovery. |
| Spatial descent or gluing | Local data over a cover and compatible transition maps address a different combination problem. | A client supplies actual spatial overlap and coherence data; the present inputs contain neither. No claim of a checked gluing construction follows here. |

The operation-transport and signature alternatives can stand independently of existing `Connection` or square interfaces. Their merits depend on the operations and laws they construct. An incumbent adapter is unnecessary for considering them.

For the signature candidate, a concrete paper design is to choose left carriers on common sorts, retain each side's private carriers, and define each right operation by `j_out⁻¹ (f (j_in₁ x₁, …, j_inₙ xₙ))`. Here every j is a supplied common-sort equivalence or an identity on a private right sort. Cancellation proves operation recovery. Induction on well-sorted open terms under arbitrary valuations transports side equations. Common-operation compatibility is a genuine input requirement: where both sides already define an operation, the common reduct equivalence must preserve it. It cannot be reconstructed from a bare carrier equivalence. This argument assumes named total operations, disjoint private names, agreed common arities, and only the union of side equations. It does not establish dependent-sort transport, partial operations, higher identity, or additional mixed axioms.

This separates two cases often confused by a broad combination API. Laws of an operation newly defined by conjugation can follow from the supplied operation's laws. Stronger laws imposed on retained operations may fail and need independent justification. The existing invariance rejection is an example of the latter.

Relational synchronization is a substantive alternative when the intended guarantee changes. `Squares.synchronized` and `synchronize` (Combinators.lean:29–39) construct agreement over decoders and preserve it from two supplied commuting squares and agreement of their specification functions. They do not manufacture compatibility for independent operations. Nor does an agreement subtype generally have invertible projections onto both entire input carriers. Replacing `Combination` with that contract would therefore weaken the current rejection statement and lose exact whole-carrier recovery unless extra hypotheses restore it. That is a contract change, not a discovered defect in `Combination`.

`SquareKit.Institutions.Connection` carries an already supplied reduct and selected-evidence map; its `comp` composes these. `Compatible` groups supplied proof and realization maps. These are useful composition interfaces but do not themselves supply the missing joint model construction. Adding an institution wrapper alone would not discharge the transport obligations identified above.

## A third operation family selected before interface design

Use an independently supplied binary state operation `b : Y → Y → Y` with associativity and a supplied unit, retaining the existing action on X and observer on Y. This tests a state-valued output, two transported arguments, and transported algebraic laws. It is a different operation shape from the existing observation `Y → D`.

A concrete proposed fixture uses the existing `List Nat` / `List Nat × PUnit` equivalence and independently specifies concatenation on the paired carrier. Define the new operation on X by

```text
bX x x' := e.symm (b (e x) (e x'))
uX := e.symm uY
```

Recovery `e (bX x x') = b (e x) (e x')`, associativity, and unit laws follow by cancellation and the corresponding side laws. The native prefix action and length observer stay unchanged. This would consume existing checked `list_native`, `list_point`, `ordered_expected`, and `observation_not_injective`; the new binary-operation results would need their own checking.

Do not require prefixing to be an endomorphism of concatenation. On the proposed fixture, prefix [8] applied to `[1] ++ [2]` gives `[8,1,2]`, while concatenating prefix [8] applied to each operand gives `[8,1,8,2]`. This paper counterexample separates side-law transport from a false mixed law. A useful positive law instead is prefixing the first operand: `p • (xs ++ ys) = (p • xs) ++ ys`, using append associativity. Its proof depends on the chosen prefix action, so a generic combination theorem should not invent it for every action.

Run the same contract through direct native definitions, selected transport helpers, and a bounded signature interface. Record independently supplied input proofs separately from derived recovery/law proofs and infrastructure setup. Count repairs and obligations remaining at the caller, not just total declarations. Include a second use of the binary family or a changed operation arity after freezing each candidate interface, so an implementation tailored to the initial fixture does not appear reusable by construction. A third toy instance alone is insufficient adoption evidence.

A further discriminating case should give the common reduct an actual operation, not only a point. Supply carrier equivalences that preserve the point but fail to preserve that common operation, and require a proposed generic interface to identify the exact missing compatibility premise. The current API is not defective for omitting this premise: its shared reduct is only the pointed carrier. A broader interface that silently conflates overlapping operations would be defective.

## Recommendation and unresolved questions

The smallest useful next step is the frozen binary-operation comparison above. Keep native `combine` as a candidate that can win. Extract selected conjugation/recovery helpers only if that comparison reveals recurring work; consider a general signature construction if it removes repeated open-term or axiom-transport proofs across independently specified operation families. Retain alternative-foundation research without requiring migration of the current example first.

No established defect in the current construction emerged from this lens. The main risk is promoting two instances of one operation family into evidence for a universal model-combination abstraction. The converse risk is treating the brevity of `o ∘ e` as evidence against general operation transport, although it has no transported state-valued output and proves no arbitrary side-equation induction. The proposed binary fixture distinguishes these cases.

Whether shared helpers reduce author effort, whether arbitrary signatures have a usable native front end, and whether a concrete client needs relational or spatial recovery remain unanswered. The recommendation preserves all listed native observations and both rejection theorems. It authorizes no architecture adoption, implementation, issue creation, or publication change.
