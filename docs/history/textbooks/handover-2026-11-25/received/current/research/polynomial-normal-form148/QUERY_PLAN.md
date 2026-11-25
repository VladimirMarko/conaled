# Next actual query — no execution yet

After the active exact-C147 whole check and its immediate verification sequence,
use the recorded native route without output injection or resource overrides.
The draft imports only pinned Mathlib/core modules, not concatenated project
proofs. Bind the draft, frozen expectations, native/toolchain inputs and its
four explicit import sources. Record every actual attempt separately.

Compile the entire draft with `-EhasSorry`, without `-o`, and then use these
ordinary queries in a bound carrier containing the exact draft body once:

```lean
#check Resources.PolynomialTime.NormalFormDraft148.exponent
#check Resources.PolynomialTime.NormalFormDraft148.eval_monotone
#check Resources.PolynomialTime.NormalFormDraft148.eval_le_coefficient_sum_mul_power
#check Resources.PolynomialTime.NormalFormDraft148.eval_zero_le_exponent
#check Resources.PolynomialTime.NormalFormDraft148.eval_one_le_exponent
#check Resources.PolynomialTime.NormalFormDraft148.eval_le_power_add_exponent
#check Resources.PolynomialTime.NormalFormDraft148.exists_power_add_bound
set_option pp.all true in
#check Resources.PolynomialTime.NormalFormDraft148.exists_power_add_bound
#print axioms Resources.PolynomialTime.NormalFormDraft148.eval_le_power_add_exponent
#print axioms Resources.PolynomialTime.NormalFormDraft148.exists_power_add_bound
```

The expected scope is seven readable statements, one selected expansion and
two selected axiom roots. Read the actual emitted output in full with any
abbreviations explicitly disclosed. A successful development query would not
install the lemma, discharge the original whole-library review, establish a
conventional verifier contract, or upgrade any textbook qualification.
