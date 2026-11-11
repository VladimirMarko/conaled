# ADR 0010 — Test composition with independent implementations and audit every declaration

**Status:** Accepted.

## Context

An application collection would be a weak test of the framework if each domain
were an isolated interpretation. Pointwise examples also leave general source
compiler correctness and compatibility between backends untested. Finally,
checking selected theorem axioms would not detect an admitted proof elsewhere.

## Decision

Place universal cross-application theorems in `Examples`, with imports from the
independently implemented libraries. Use one shared scalar primitive signature
for stack evaluation, finite changes, rational enclosure, and real analytic AD.
Prove stack recomputation after an update equals incremental update of the old
result, and transfer interval enclosure to both outputs. Quantify over every
typed source term and every arbitrary preserved stack tail.

Synchronize the matrix and stack squares for the entire shared linear source
fragment. The output representation is a pullback: its two components must
decode to the same value. This is an actual joint implementation, with its
agreement certificate constructed from the two compiler theorems.

Compose the polynomial derivative tower with scan-based polynomial evaluation.
The prepared representation is a dependent package of a scan plan and its
correctly shaped coefficients. Prove the coefficient adapter, correctness for
any sufficiently large plan, and a total adapter that selects enough slots.
Paste its square with analytic differentiation and evaluation, obtaining the
true derivative of every source polynomial expression at every order.

Keep the weighted-convolution-to-regex-to-trie and independent recognizer/parser
agreement theorems in the language library, where they can be reused directly.
Timing maps reuse the finite matrix representation over the interval semiring.

The public entrypoint imports every module. The verification command computes
its local import closure, rejects omitted source files, and checks source policy.
Routine acceptance uses stock Lake incremental compilation and runs the
exhaustive audit on every invocation, even if no modules need recompilation.
This trusts Lake's dependency tracking and the local build artifacts. Validation
must use stable candidate inputs, dependencies, and configuration.

A separate `--fresh` mode rechecks every project module from source, with
bounded concurrent compilation after imports succeed. It uses private temporary
outputs, reuses external dependency caches, and excludes existing project
artifacts. Run this mode weekly and after build-tooling, toolchain, or dependency
configuration changes, or suspected cache errors. Both modes audit only after
all required compilation succeeds.

Issue [#223](https://github.com/VladimirMarko/conaled/issues/223) revises the earlier
fresh-on-every-acceptance policy. Recompiling unchanged modules on every check
increases development cost as the library grows. Lake's ordinary invalidation
is sufficient for routine acceptance; the fresh check independently exercises
source compilation without project cache reuse. A stale result could validate
an older statement or hide an integration failure, so the periodic check remains
useful. Neither mode establishes truth of the intended specification or freezes
concurrently changing inputs. A future conditional guarantee for cache reuse
belongs to [#222](https://github.com/VladimirMarko/conaled/issues/222).

The final audit enumerates every locally defined kernel-safe declaration by
module origin, including private and generated proof declarations, and traverses
all transitive axiom dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. The audit selects imported project modules from Lean's module metadata, includes
their constants and resolvable generated names, and includes current-module
kernel declarations. It deduplicates names and retains the module-origin and
safety checks. This avoids a scan through every dependency declaration without
narrowing the intended root set. The audit calls Lean's public `collectAxioms`
API for every root. Since the Lean 4.35 upgrade, this uses Lean's transitive axiom
summaries for imported declarations, computed when checked modules are exported,
and traverses local declarations directly. It does not skip audit roots.
Lean-generated unsafe
runtime declarations are reported separately. Both source-range metadata and
a lexical source guard reject user-written unsafe definitions; any forbidden
axiom reached from a mathematical root still fails the audit.

## Alternatives

* Compare only numerical examples: useful executable checks, insufficient for
  the universal compatibility claims required here.
* Force every representation into a decoding function: loses interval
  enclosure, signal stability, and higher-order logical relations.
* Audit only named headline theorems: could miss a placeholder in an unused
  implementation or auxiliary proof.
* Import arbitrary cached local `.olean` files without Lake dependency tracking:
  this can miss source changes. Routine acceptance instead asks Lake to rebuild
  changed inputs and their affected dependents before auditing.

## Consequences

Composition requires matching semantic interfaces and explicitly established
local laws. It does not mean every target supports every source operation, or
that equality of semantic functions implies equality of analyses. The initial
dependent-family library remains a shallow model; the dependent coefficient
package tests indexed representations without claiming a new full dependent
language compiler.

The audit establishes absence of extra transitive axioms in this development.
It does not establish that the chosen specification is the desired one; that
is addressed by the independent evaluators, explicit statements, examples,
source review, and scope documentation.

## Checked evidence

`Examples.ArithmeticPipeline.stack_after_update`, `stack_enclosed`,
`incremental_output_enclosed`, `compile_hasFDerivAt`,
`Examples.MatrixStack.jointSquare`, `agree_preserving_tail`,
`Examples.JetScan.prepare_correct`, `shaped_evaluation_correct`,
`source_jet_scan`, `LanguageDerivatives.normalized_product_snapshot`,
`recognizers_agree`, and the exhaustive command in `ProofAudit.lean`.

## Verification tooling follow-ups

Issue [#42](https://github.com/VladimirMarko/conaled/issues/42) adds parallel fresh
compilation and module-directed audit enumeration. Public-command regression
fixtures check scheduling and freshness, and an independent exhaustive scan
compares exact audit root sets. These tests are empirical evidence; formal
refinement proofs and their external-state assumptions are follow-up
[#43](https://github.com/VladimirMarko/conaled/issues/43).

[#7](https://github.com/VladimirMarko/conaled/issues/7) replaces Python source
interpretation with the pinned Lean header parser and native lexical parsers.
Coverage and scheduling use the resulting import graph; no second import grammar
is maintained. Lake resolves dependency paths and owns routine incremental
compilation. The explicit fresh mode retains the bounded scheduler with private
project outputs. Python continues to manage those processes and candidate
receipts. The lexical policy preflight is distinct from full compiler syntax
checking and the exhaustive transitive-axiom audit; none replaces the others.
See [the implementation boundary](../research/native-verification-source.md).
