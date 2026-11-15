# XP01 compatibility continuation at 4b5dbfa0

Recorded 4 November 2026 by `/root/shared_acceptance_sequence`. This preserves
the completed bounded source inspection requested by root after checkpoint 0097.
It is preparation for the existing XP01 exception, with no implementation,
compilation, independent review approval, acceptance or new mathematical preflight.
The original `report.md` and `receipt.json` remain byte-for-byte unchanged.

## Exact comparison and unchanged sequence

The saved draft is `c28ba71863d2a35ee1c3a089caa90464e4cca692`, whose parent is
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`. The inspected current central source
snapshot is `4b5dbfa07288acc73f25c27838d3fb2f78e77d71`. Its Potential,
FIFOContracts, SharedDemand, BinaryCounter, SymmetricCosts, RandomAccess.End,
Workload and Measured blobs match the previously recorded
`8ba7ae11a657e8a4af025f60b4e1a54dddb3c512` snapshot. They still use the old
Potential implementation; current builds therefore provide no XP01 compile credit.

The sequence remains exact foundation F acceptance, combined XM01/XD01/XQ01/XU01
acceptance, XU02 acceptance, XU03 acceptance, and complete Chapter 2 acceptance.
Accepted Chapter 1 remains `07e480f6ec9958d4975bb90151005b84f2907614`; exact F
remains `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`. Chapter 3 stays queued until
Chapter 2 acceptance and its checkpoint. This inspection does not insert XP01
as a prerequisite, assemble a candidate, change a gate, or reopen later chapters.

## Concrete compatibility findings

**No new source compatibility defect was identified within the read boundary.**
This is a source conclusion; actual elaboration of the saved generalized
implementation and its clients remains unverified.

### SharedDemand retains its Nat connection

`SharedDemand.run_work_remaining`, lines 226–235, applies the retained
Nat-specialized `run_potential_exact` and simplifies using `budget_constant`.
Its `step compute` returns `Measured (Cache ι α) Nat`, and `remaining compute`
returns `Nat`. Those types fix both the raw-work and accounting carriers,
including the zero charge. The wrapper retains its original statement and
introduces no new validity premise into this client. The existing remaining-work
and eager-catalogue bounds continue to call this same result.

The relevant current source blob is `449d7fce653a449be11209c4cb8cb23ae1240609`.
The original receipt's comparison of the eight preserved Nat contract statements
is retained; this continuation does not replace that evidence with a printed-type
or compilation claim.

### FIFO already contains the concrete inference repair

Generalized `budget` separates raw-work carrier `C` from accounting carrier `D`.
In `FIFOContracts.abstractBudget`, the Nat-valued profile fixes `D` but does not
fix the raw component of `(step (lists α) c xs, 0)`. Exact XP01 already supplies
the needed `(0 : Nat)` annotation. This is the complete FIFO source delta.

`budget_abstract` still follows the same decoded state trajectory, while
`abstractBudget_append` supplies `e.measured` through an explicitly Nat-valued
`Instrumentation`. No additional FIFO source edit is justified by this inspection.
The draft FIFO blob is `01839707e852b3faff6ef1a49ad88a76fb5e5c18`; the unchanged
central FIFO blob is `51a45acf742f9e984188094bb72d3744e9f6e19b`.

### Other inspected Nat clients determine their carriers

`BinaryCounter.incWithCost`, `SymmetricCosts.chargeStep` and `workStep`, and
`RandomAccess.End.consRARun` provide explicit Nat work types to the retained
Nat wrappers. The inspected natural examples use typed measured transitions or
`Fin.val`; they do not reproduce the unconstrained raw-zero situation.

A bounded immutable search of all tracked `*.lean` files at `4b5dbfa0…` found
no explicit positional application matching
`@(Resources\.)?(budget|budget_append|run_potential_exact|run_constant_charge)\b`.
This rules out that exact textual use in the searched snapshot, not all possible
metaprogrammatic references or downstream clients outside the repository.

### The inspected mapped APIs match the pinned declarations

Mathlib pin: `56a005855ea17e0b0958f73ec801ae140b0a1679`.

| Inspected API | Source evidence | Consequence |
| --- | --- | --- |
| `AddZero` | `Mathlib/Algebra/Group/Monoid.lean`, lines 30–32 | Bundles zero and addition without imposing identity laws, matching the draft's raw structure assumption. |
| `AddMonoidHom` | `Mathlib/Algebra/Group/Hom/Defs.lean`, lines 133–160 | Accepts `[AddZero]` on both carriers and preserves zero and addition. |
| `Nat.castAddMonoidHom` | `Mathlib/Data/Nat/Cast/Basic.lean`, lines 38–43 | Supplies the additive natural-number observation into the target carrier. |
| `Nat.coe_castAddMonoidHom` | The same file, lines 45–47 | Is a `[simp]` function equality to `Nat.cast`, proved by `rfl`, as used in the counter example. |

The read found no concrete missing-name or assumption mismatch in those uses.
It does not establish that all new proofs elaborate, nor assert an exhaustive API
assessment. The completed original mathematical preflight remains the relevant
earlier assessment and is not repeated or promoted here.

## Consequence for future work

Preserve the existing FIFO annotation and accepted SharedDemand source. No
preparatory source repair is indicated by this inspection. When root schedules
XP01, the already recorded compatibility targets must elaborate against the actual
generalized Potential implementation; source equality and old-implementation
builds cannot supply that result. The original full-scope review and validation
requirements remain as recorded, with no new gate added by this continuation.

## Honest read boundary

Complete reads in this continuation were the saved 188-line report; draft
Potential (238 lines), FIFOContracts (168), and MappedPotentialAccounting (165);
current SharedDemand (251), Workload (64), and Examples.PotentialAccounting (126).
The latter current files were read from the earlier immutable snapshot and their
equality to `4b5dbfa0…` was checked. The complete one-line FIFO change was read.

Bounded caller reads were BinaryCounter lines 200–270, SymmetricCosts 213–265,
and RandomAccess.End 125–162. Pinned API excerpt reads were Group.Monoid 21–88,
Group.Hom.Defs 115–166, and Nat.Cast.Basic 25–53. Current Potential, FIFOContracts
and Measured received identity comparisons in this continuation, not new complete
reads of their old versions. Full identities and these boundaries are in the
companion JSON; full-file hashing does not imply full-file assessment.

An initial broad textual search produced truncated output and included unrelated
uses of the word `budget`. It is not treated as an exhaustive caller inventory.
The relevant target-file search and the separate explicit-argument search were
subsequently read completely. Auxiliary textual API-name searches are not
evidence that an unreturned generated declaration is absent.

Only this new Markdown file and its new companion JSON are authorized writes.
No source, ref, existing report, compiler, cache, output or process is changed.
The report is read back in full before the companion record is finalized.
