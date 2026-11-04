# Frozen composed theory-reuse fixture

For [#294](https://github.com/VladimirMarko/conaled/issues/294). Frozen before
route adaptation; the companion report records the freeze commit. Inspected
repository base: `2525b12052e4c85c57f9050dbf18f7a36ba2ef19`.
This is a paper comparison, not a timed author trial or checked Lean artifact.

## Mathematical task

Use a carrier M, binary multiplication, unit e, associativity, both unit laws,
and distinguished elements a,u satisfying a*u=e. The argument must publish a
selected solution of a*y=x, for every x, with observed data exactly u*x.
The selection is part of the task: an existential assertion alone is insufficient.
Equality is ordinary extensional equality in the models below. Proof objects
need not be identical; selected elements must be preserved by interpretation.
There are no dependent indices beyond the solution family indexed by x.

Extend the theory by precisely one principle:

    C_a : ∀y z. a*y = a*z → y=z.

Use this principle to show u*a=e and that the selected solution is unique.
Do not silently strengthen C_a to cancellation at every element, assume a
chosen inverse operation in the base, or demand proof irrelevance in order to
identify selected elements.

## Two successive interpretations

First interpret this theory into the theory of groups with one distinguished
element g: M becomes the group carrier, a becomes g and u becomes g⁻¹.
Second interpret pointed groups into integer addition with a distinguished
integer n: the group product becomes +, unit becomes 0, inverse becomes
negation, and g becomes n. Retain n as a parameter, not a fixed integer.
Both interpretations and their composite must include law assignments.

The composite selected solution must be -n+x. Specialization at n=2,x=5 must
return 3, with its equation 2+3=5. The argument using C_a must pass through the
same two interpretations. A direct arithmetic proof of existence without the
selected data does not satisfy the comparison.

## Target missing the principle

Use the monoid of functions ℕ→ℕ with multiplication f*g=f∘g and unit id.
Interpret a as truncated predecessor and u as successor. This target must
accept the base argument. It must reject a total interpretation of the
extension with these fixed assignments, using an explicit failed instance of
C_a and of u*a=e. The extension failure must not prevent publishing the base
argument separately.

## Matched routes and boundaries

Compare native operation/law interfaces and a presented theory with total
views on exactly these contracts. Show declaration assignments, identity and
composition, model reducts, translated derivations, and selected data. Explain
which author obligations recur and which model/foundation work is reusable.
A partial view dropping C_a cannot certify extension theorem transport.

Inspect foundation regularity and encoding adequacy before appealing to MMT's
transport theorem. Inspect institution satisfaction/reduct laws and distinguish
sentence truth from proof or data transport. Explicitly examine a changed-logic
boundary on paper, including rule meanings or a rejection in this fragment.

Compare keeping native interfaces, a bounded adapter, and a theory-network
organization that may replace today's organizing assumptions. None is excluded
because it cannot immediately be embedded in current generated syntax. Existing
#277 and #284 results constrain recovery, without defining all eligible designs.
