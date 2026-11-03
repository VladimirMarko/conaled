# Review heuristics

Use these Fowler-style smells as prompts for investigation, not automatic
violations or mandatory rewrites. Explain the concrete consequence and a
language-appropriate remedy. Repository standards override these heuristics.

- **Mysterious Name:** a name obscures the mathematical or computational role.
  Prefer established domain vocabulary.
- **Duplicated Code:** repeated logic creates inconsistent maintenance or hides
  a reusable result. Inductive cases and distinct proof obligations can
  legitimately resemble each other; extract only where it improves use.
- **Feature Envy:** an operation depends on another module's representation
  details. Consider an interface or placement change that reduces that coupling.
- **Data Clumps / Primitive Obsession:** values lack a useful shared invariant
  or domain meaning. Bundle them only when the structure earns its caller cost;
  explicit theorem hypotheses and parameters are often the right interface.
- **Repeated Switches:** duplicated case analysis drifts across implementations.
  Consider a shared eliminator or lemma when appropriate. Exhaustive inductive
  proofs are not defects merely because they repeat constructors.
- **Shotgun Surgery / Divergent Change:** changes reveal avoidable coupling or
  unrelated responsibilities. Assess dependency boundaries before moving code;
  updates to public entrypoints and checked applications may be necessary.
- **Speculative Generality:** unused machinery increases obligations or caller
  effort without serving the task or repository architecture. General theorems,
  weak assumptions, and reusable interpretations may be explicit requirements.
- **Message Chains:** callers depend on representation traversal that should be
  hidden by a stable interface. Mathematical composition is not itself a smell.
- **Middle Man:** delegation adds cost without an interface benefit. Theorem
  wrappers can supply useful specializations, stable names, or law transport.
- **Refused Bequest:** inherited obligations do not fit the intended structure.
  Reconsider assumptions or composition where the mismatch is concrete; do not
  prescribe object-oriented inheritance changes for Lean structures by analogy.
