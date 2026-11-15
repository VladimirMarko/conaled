# A represented function client on one coin tape

Issue #545 connects the existing Boolean function client to executable prepared
rows. The implementation samples a finite function code once, retains it while
sampling two further inputs, and computes the original client record
`(b, t, b xor t, (b xor t) xor u)`. Each draw starts at the preceding draw's
actual returned cursor. The function calls are pure computations of the retained
values; the implementation performs those computations when returning the record.

`Applications/Probability/RetainedSampler.lean` supplies the three-row composition.
Its second row may depend on the first value, and its third row may depend on both
earlier values. `evaluates_iff` characterizes execution in both directions,
retaining all three absolute cursors and exact transition counts. `event_mass`
uses the existing stopped-cursor freshness theorem to factor the complete joint
value law. It does not assert that selected outcomes are independent when the
later row depends on earlier outcomes.

The finite measure `valueLaw` is a mathematical observation of these executions.
`valueLaw_apply` proves that every measurable event has exactly the mass of the
corresponding actual finite derivations. Thus the measure is connected to the
machine, including its possible nontermination, rather than assigned as a
separate probability specification. `ae_terminates` establishes almost-sure
termination for the countable supported first and second carriers; exceptional
tapes are not erased from the execution relation.

## Full records and represented functions

`Examples/OperationalSamplerSubstitution.lean` prepares the fair Boolean rows
using the explicit `finTwoEquiv` enumeration. It proves that all eight input
triples have mass 1/8, then proves `seedLaw_eq` for the complete triple measure.
`nativeLaw_apply` connects the returned client records to actual evaluations, and
`nativeLaw_eq` identifies that law with the independently specified
`SamplerClient.selected` applied to three fair inputs. The code and first query
input remain in this native record.

`interpret` converts the retained finite code to its entire Boolean function and
keeps both call results. `whole_function_law` identifies the resulting measure
with the existing admitted `retainedTwo sampled query next` client. Its target
measurable space is explicitly the QBS-generated sigma algebra of the complete
function-and-results product. Finite source types supply measurability of the
observation maps; the existing QBS morphisms supply the admitted represented
client. No representation is selected by classical choice in executable code.

`whole_function_replacement` then reuses `SamplerSubstitution.twice_replaced`,
which was proved through the public two-stage substitution API. Equality is of
the complete semantic function observation. It identifies neither the chosen
codes at the same seed nor their tapes, cursors or execution costs. General QBS
bind and executable adequacy for arbitrary QBS programs remain owned by #497.

## Separating executions

The fair example reads three two-bit blocks. At fuel 6 it returns
`(false, true, true, false)` and cursor 6; at fuel 5 it has not returned. A second
example uses a non-dyadic third row with weights 1/3 and 2/3. After two fair draws,
its block `1111` is rejected and `0110` is accepted. The complete run returns
cursors 2, 4 and 12 and needs fuel 12. The selected triple
`(false, true, true)` has mass 1/6, proved through the generic operational theorem.
Another checked continuation selects the biased or fair third row according to
the first query result. Its two cases exercise value-dependent row selection.

Copying a sampled function code uses one draw. Independently resampling it uses
the returned cursor for a second draw. Their `(false, true)` event masses are
respectively zero and 1/4, although the individual code laws are fair. Restarting
the second draw at the original cursor also gives zero mass to that event, and
the checked run returns cursor 2 after four transitions of rereading. Code
interpretation is injective, so these are differences between complete sampled
functions, not merely differences between redundant encodings.

The earlier marginal and seed-reuse counterexamples remain available in
`SamplerClient` and `Examples.SamplerSubstitution`. The new controls concern
actual row machines and returned cursors. They make no claim about physical
random sources, continuous distributions, mixing, or the runtime cost of
evaluating arbitrary functions.

## Statement review

The composition keeps each value together with its absolute returned cursor.
Its evaluation equivalence preserves exact work in both directions; only the
declared value measure hides cursors and work. The mass theorem permits dependent
later rows and is not a product-independence claim about arbitrary outputs.
Finite-event disjointness follows from deterministic evaluation uniqueness.
The client law is proved before mapping to semantic functions or projecting
call-result marginals. The biased continuation and copied/resampled/reused
controls exercise the retained operational distinctions. Candidate build,
exhaustive audit and independent review receipts are kept outside this report.
