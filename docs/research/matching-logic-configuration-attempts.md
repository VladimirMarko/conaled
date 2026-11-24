# Configuration-pattern implementation attempts

The accepted #439 client and #503 contracts were retained throughout. The
following failures concern Lean encoding; none motivates weakening a semantic
premise or changing the expected outcome sets.

- The first free-variable occurrence datatype fixed the context as an inductive
  parameter. Its binder constructor needs the extended context, so Lean rejected
  that recursive occurrence. Making the context an index permits the correctly
  typed `there` occurrence under the binder. The bound sort also needed to be
  specified in that constructor.
- Equality between implicitly sort-polymorphic valuation functions initially
  inserted an unresolved sort argument. Explicit `@` applications in the two
  pullback/extension lemmas preserve the entire polymorphic function. Their
  proofs are function extensionality and typed-variable cases. A similar dotted
  `extend` expression on an applied valuation selected `Function.extend`;
  explicit `Valuation.extend` fixed the examples.
- An initial opaque carrier abbreviation prevented numeric typeclass inference
  at the natural sort. A reducible `Carrier` and concrete `model` expose those
  intended types. No carrier, universe or model law changed.
- Generic simplification did not match several semantic equations through the
  concrete model and implicit valuation arguments. Explicit theorem applications
  supplied the model, pattern and valuation before local set simplification.
  The same exact denotation equations were proved without resource overrides.
- A rule constructor called `axiom` parsed in its declaration but collided with
  the reserved command in an induction alternative. It is `specAxiom` in the
  delivered datatype. An example namespace also needed an explicit root-qualified
  open to avoid resolving `MatchingLogic` to `Examples.MatchingLogic`.

The source PDF hash was checked against the accepted report before coding.
The missing local PDF-text command was supplied through a temporary Nix tool;
no repository toolchain change was needed.

The failed unrestricted-substitution proposal is retained as a checked
nonempty two-outcome counterexample, with a separate empty terminal case.
The failed original-trace recovery claim is retained as `no_recovery` and a
public keepB-to-keepA selected-witness example. These mathematical failures
remain part of the public result, rather than being repaired by changing the
observation contract.
