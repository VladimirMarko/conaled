# Connected normal-form cases, fixed before their first compiler check

These cases consume the generic normal-form theorem. They preserve the four
independent arithmetic expectations from the frozen148 draft: the zero
polynomial has exponent0, constant7 has exponent7, X has exponent2, and
2X²+3X+5 has degree2, coefficient sum10 and exponent12. The last polynomial
evaluates to5,10,19 at inputs0,1,2 respectively.

For each of the four polynomials, the checked application must retain every
natural input N, including0 and1. Its proof must apply
eval_le_power_add_exponent and identify that polynomial's fixed exponent;
an unrelated arithmetic proof of the inequality does not exercise this reuse.
The mixed polynomial's degree and evaluations are separate exact observations.

The parent theorem revision149 has already passed the recorded normal-form149b
development query. These new cases have not yet been compiled. This is research
outside C147, not installation, whole-library acceptance, independent review,+a machine construction, or a conventional NP/effectivity claim.
