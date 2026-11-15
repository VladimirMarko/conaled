# FRP umbrella-import contingency investigation

2026-11-02, read-only investigation by root and `environment` against candidate
`cba657b43ed57e15962858713b819058e7d3c3ca`. **All proposed imports below are
uncompiled. The current candidate and advancing validation remain unchanged.**

The only direct integrated `import Mathlib` umbrella imports found by the scoped
source search are `Applications/FRP/Spec.lean` and
`Applications/FRP/Equivalence.lean`. Other direct matches are historical sources
under docs/history and are outside the integrated build. The two integrated
imports bring the full Mathlib closure into the validation graph, explaining
why missing artifacts unrelated to sorting are built during this candidate run.

The inspected FRP documentation describes the FRP interfaces and explicitly
preserves the Raw/Homomorphism facade in docs/frp-integration.md. No promise to
re-export all of Mathlib was found in that bounded inspection. This does not
establish that every indirect or external consumer is independent of ambient
imports, instances, simplification rules, or tactics.

## Conservative uncompiled proposal

For Spec, a possible replacement for the single umbrella import is:

```lean
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Ext
```

Retain its existing SquareKit.FunctionCategory and SquareKit.CartesianMap
imports. At this pin Mathlib.Basic.Real.Basic is canonical;
Mathlib.Data.Real.Basic is a deprecated compatibility module.

For Equivalence, a possible replacement is:

```lean
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
```

Pinned Mathlib.Tactic.Linarith publicly imports Mathlib.Tactic.NormNum.
`exact_mod_cast` is supplied by the pinned Lean core; a proposed
Mathlib.Tactic.NormCast import would name a nonexistent module at this pin.
The lists above intentionally retain some immediate-client dependencies and
have not been established as sufficient or minimal.

## Concrete client obligations found

| Immediate client | Dependencies to preserve or import explicitly |
| --- | --- |
| Applications/FRP/Frontier.lean | List.toFinset, List.coe_toFinset, Finset.finite_toSet in logEvent. |
| Applications/FRP/Finite.lean | Set.finite_Iio, finite images/preimages, Set.Finite.biUnion, List.ofFn, lexicographic products and relevant simplification rules. |
| Examples/FRP.lean | Nat-to-Real cast facts and exists_nat_gt; the latter needs the Real Archimedean instance, beyond Real basics alone. |

Removing an umbrella can change available instances, simp lemmas, and tactic
extensions even if explicitly named declarations remain available. Any actual
change would therefore need its own scoped local ticket, exact unchanged
declaration/proof comparison, focused compilation of both modules and clients,
the full required candidate build/audit, and both independent review axes.
It would create a new candidate; existing source reviews on cba657b would need
their normal correction/evidence round for that candidate.

No memory or timing improvement was measured, no source/staging/cache/process
change was made for this investigation, and no restart is justified solely by
this uncompiled proposal. This is a retained fallback if the whole-Mathlib
imports become a concrete resource blocker, not an accepted implementation or
an alteration of the current chapter gate.
