# Failed attempts and boundaries

The [failed signature source](signature-failed.lean.txt) and its
[build log](signature-failure.log.txt) preserve an unsuccessful elaboration attempt.
The operation interpretation was held in an anonymous local instance. Simplifying
term semantics did not unfold that instance to the supplied operation, leaving
`Structure.funMap` projections in the goal. Naming the instance and including it
in the simplification resolved these proofs. Replacing every `letI` mechanically
with `let` also exposed a let binder to `intro`; the final theorem statements keep
the required instance binder. These were encoding errors, not failed equations.
Earlier drafts also used a nonexistent associativity alias and the reserved word
`structure` as a definition name. The final code states the associativity equation
explicitly and calls the interpretation `suppliedStructure`.

The concrete pair carrier initially left PUnit's universe unconstrained, producing
universe metavariables in the transported operation. Annotating the selected
carrier as Type fixes that bounded example. The generic helpers and signature
transport still quantify over independent source and target universes.

The [FIFO import attempt](module-failure.log.txt) failed because the existing
`AbstractFIFO` file does not use Lean's module system. The new consumer now uses
the repository's compatible legacy import form. No existing FIFO source or
interface was migrated. All failures preceded acceptance validation; archived
`.lean.txt` files are evidence, not checked proof roots. No resource limits changed.

The checked `prefix_not_distributive` and `no_distributive_alternative` theorems
are different: they establish a mathematical obstruction. A nonempty prefix
would occur once on one side and twice on the other. Exact carrier recovery
cannot make that extra equation true. This rejects the mixed law, not the valid
operation combination or a weaker relational simulation.
