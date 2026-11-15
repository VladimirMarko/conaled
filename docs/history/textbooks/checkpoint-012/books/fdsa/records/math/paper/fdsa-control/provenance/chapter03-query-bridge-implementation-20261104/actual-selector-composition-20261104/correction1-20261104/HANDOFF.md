# Scoped quantified-binder correction: immutable successor

Candidate **8b7531d661366d7843ccab9ebd7eca7d41cdbbef**; tree **8d7f64ffd6ade763a2c0072a2052f656cbacf528**; parent **2d20573cc5d3373a4746a5ebf16314369e7d7e3e**. Worktree clean.

The source patch changes exactly five proposition-local proof-binder labels on
four lines in Applications.Selection.CoordinateSelection. The two quantified
propositions are exists_uniform_competitor_bound and exists_uniform_optimality:
distinct/correct and distinct/total/correct respectively gain an underscore
prefix. Their actual hypotheses, domains, order, dependencies and conclusions
are unchanged. Proof bodies still introduce and use the hypotheses under the
same local names. No linter option, suppression, premise removal or weakening
was introduced.

Both old/new complete headers and the exact patch are retained. All44 other
public headers and the private header are exact, all47 declaration bodies are
exact, all3 computational definitions are exact, and all16 connected cases are
exact. The other18 component source files and every old provenance/failure
record are unchanged. Combined scope stays337 public names/19 authored private
helpers; the new composition scope stays46 public names/one private helper.

The complete actual failed first attempt was read: owned34748 CLOSED1,
terminal edd85c, closure3cb0b2; full11727-byte log SHA
91949a3a89b4084d23292e384e8eb093a8e363e3109da444567cb811d6eb57b5.
The five recorded diagnostics are the sole correction scope. Examples have
not compiled; no success is inferred from the blocked first run.

Statements46-candidate02.lean and Statements337-candidate02.lean are explicitly
bound to this candidate/tree. Their original inspection bodies, ordered names
and all six printer options are byte-identical, with only an additive candidate
binding comment. They have not been executed. Exact bindings, source/header
assessment and exhaustive preservation details are saved in this directory.

Static git diff --cached --check passed. No author Lean/Lake/build/install/
hydrate/cache command ran. Root should inspect candidate.diff and run the next
serial focused attempt for Applications.Selection.CoordinateSelection and
Examples.CoordinateSelection. This successor remains uncompiled; full/types/
audit/independent-review/immediate-verification gates and all83 obligations
remain mandatory. All own source/provenance writes are now held.
