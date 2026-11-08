# Authoring and statement checks

Develop the general construction and its checked uses together. Start with an
independently expected case from the task, express the missing obligation, then
connect it through the route's public interfaces. An unrelated syntax or import
error is a setup failure, not evidence of a mathematical obstruction. Reuse
existing cases when they already expose an obligation; do not manufacture a
failure. Every check, including `#check`, uses the attempt wrapper.

Review each new claim's quantifiers, types, implicit parameters, assumptions and
conclusion. Check that hypotheses hold in the intended applications and are not
circular or vacuous. Inspect definitions behind notation and coercions when
necessary. State which equality and direction the claim establishes. Preserve
the independent specification when repairing a proof; do not weaken it to make
the attempt pass. `sorry`, `admit`, and added axioms do not discharge obligations.

A checked numerical calculation can verify an expected result without showing
that it follows from the intended general theorem. The required specializations
must consume the general result. For example, deriving a sequence law and then
applying it to an empty sequence checks that connection; calculating the empty
case separately does not connect it. A proof by `rfl` can be appropriate when
reduction establishes the independently intended equation.

Use existing operations, maps and laws where their hypotheses fit. Keep native
judgments, executable representations and selected meanings distinct, and prove
the requested connections. Preserve the chosen component of a dependent result;
an inhabitation claim does not identify it. Separate mathematical correctness,
host-language encoding, and observed author effort. Local helpers are allowed;
changes to the frozen interfaces are not.

In the activity and outcome records, use plain prose and exact observations.
Record failed approaches, assistance and uncertainty with their evidence. Do not
infer general productivity, performance or architectural superiority from this
one task. Do not invent time or token measurements. The complete protocol governs
stopping, acceptance and what is counted as author work.
