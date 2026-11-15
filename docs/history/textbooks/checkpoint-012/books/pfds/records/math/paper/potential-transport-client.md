# Local 10023 — connected transport and ordered-charge clients

Implementation subtask of root's existing local10023 loop. No separate workflow,
review, compiler, Git or acceptance action is owned here.

## Governing inputs

- Requirements: `session/requirements/signed-potential.md`, version1,
  SHA256 `bb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81`.
- Starting base, supplied by root:
  `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
- Assigned checkout: `signed-potential`, branch `pfds/signed-potential`.
- Source ownership: only `Examples/PotentialTransport.lean`; this report is
  outside the source diff. Core algebra and the other signed clients belong to
  the other implementers in the same loop.
- Read: repository AGENTS, architecture/domain guidance, glossary, ADR0001,
  implement/review procedure and example-driven development guidance; the
  potential inventory and the existing Measured, Workload, Potential and
  BinaryCounter interfaces supply the local design context.

## Independent expectations, before implementation

### Existing binary counter under an additive observation map

Starting with no bits, four increments visit bit lists `[true]`,
`[false,true]`, `[true,true]`, `[false,false,true]`. The write counts are1,2,1,3,
so total writes are7 and the final number of one bits is1. Initial potential
is0. The exact account therefore reads7+1=8, and the cost-only bound is7≤8.

The client must call the existing `BinaryCounter.incWithCost`; only its second
projection is mapped by `Nat.castAddMonoidHom ℝ`. `reweight_run` must establish
that the final state and measured total are unchanged except for the cast.
The existing per-increment law must be lifted and passed to the generalized
`run_potential_exact`; casting an existing final identity alone does not meet
this obligation.

For arbitrary n and any initial bit list, the intended identity is lifted
cost plus lifted final one-bit count equals lifted initial one-bit count plus
2n. The intended bound uses nonnegativity of the actual final one-bit count.
Its Real constant budget is obtained by the same `budget`, the public
`budget_congr_state` and `budget_map`, and the existing Nat `budget_constant`.

### Ordered exact accounting

State is a remaining list of natural-number tokens. A step removes its first
token and emits that token as a singleton `FreeAddMonoid Nat` word; an empty
state emits the empty word. Potential is the remaining ordered word and new
charge is zero. Two steps from `[1,2,3]` emit `[1,2]` and leave `[3]`.

The exact local identity is prefix concatenated with suffix equals the
previous word. It is satisfied at both empty and nonempty states. Apply the
public exact telescope to obtain emitted word followed by final remaining
word equals `[1,2,3]`. Token order is part of the expectation. Neither
commutativity nor an ordered cost domain is available or needed.

### Independent observation and charge codomains

An ordinary Nat-valued measured step increments a Nat state and records one
unit of observation. Its independent charge emits the pre-step state as a
singleton `FreeAddMonoid Nat` word. Starting at0, two steps emit charge word
`[0,1]`. `budget_append` must connect the two one-step budgets using the state
actually produced by the first run. This checks a use that would not typecheck
if the budget still conflated step observation and charge codomains.

## Initial obligation and evidence status

The existing Nat counter already supplies the algorithm and local identity.
The missing obligations are its connection to the generalized Real telescope
and the two ordered-word uses of generalized budget/exact accounting. The
finite observations themselves can reduce; that alone would not exercise the
new public laws. No artificial failed compilation is being claimed.

No compiler, test, Git, cache or process operation has been performed by this
subagent. Root owns the frozen focused wrapper, candidate capture, full gate,
exhaustive audit and independent review. All acceptance remains pending that
evidence.

## Implemented derivations and statement review

Source namespace: `Examples.PotentialTransport`.

| Declaration or group | Public connection and statement review |
|---|---|
| `Counter.realStep` | Calls the existing `incWithCost` and `reweight` with `Nat.castAddMonoidHom ℝ`. Only the cost observation changes codomain; there is no replacement increment implementation or executor. |
| `Counter.realStep_potential` | Quantifies over every Unit instruction and bit list. Casts the existing exact per-increment law and orients the boundary as cost + final potential = initial potential + charge. There is no canonical-bit assumption or assumed whole-run balance. |
| `Counter.realRun_transport` | Applies `reweight_run` for arbitrary n and initial bits. Its pair conclusion explicitly preserves the original final state and casts the original total measured cost. It includes n=0. |
| `Counter.realBudget` | `budget_congr_state` proves the Real and Nat steps have the same first projection. `budget_map` maps the existing Nat constant budget along this trajectory. `budget_constant` supplies the existing 2n Nat calculation. It does not recreate recursion or independently choose states. |
| `Counter.realRun_potential` | Instantiates generic `run_potential_exact` with the lifted local law. The budget transport then gives 2n. Both initial and final one-bit terms remain in the conclusion for every initial state. |
| `Counter.realRun_bound` and its zero-start example | Uses `run_cost_le_of_nonneg_final`, supplies its local inequality from the exact local law, and proves nonnegativity of the actual terminal one-bit count by `Nat.cast_nonneg`. The conclusion retains initial potential; only the zero-start specialization removes it. |
| `Counter.realRun_four` | The independent observed pair is the original Nat run at four increments. `realRun_transport` gives the Real pair with the same `[false,false,true]` state and cost7. It does not assume the desired Real observation. |
| `Counter.realRun_four_balance` | Specializes `realRun_potential` and computes its right boundary. Together with the previous observed pair and `ones`, it is7+1=8. It is connected to the generic exact telescope, rather than proving detached numeral arithmetic. |
| `OrderedWords.step` and `step_potential` | The empty branch emits zero; the nonempty branch emits precisely its first token. Potential is the remaining word. The local proof covers both branches and keeps emitted prefix before remaining suffix. |
| `OrderedWords.two_steps` | Uses `run_append` and the actual step to obtain emitted `[1,2]` and remaining `[3]`. The expected literal distinguishes token order. |
| `OrderedWords.two_steps_conserve` | Applies `run_potential_exact` with `FreeAddMonoid Nat`, the proved local law and zero charges. Simplification removes the actual two-step zero budget. The conclusion places observed output before final potential; no commutativity or order assumption is available. |
| `IndependentCharge.step`, `charge`, `two_step_budget` | Observation codomain is Nat and charge codomain is `FreeAddMonoid Nat`. `budget_append` supplies the intermediate state from the measured first run; reducing the actual two one-step pieces gives `[0,1]`. Charges observe pre-step states0 and1, not two copies of the initial state. |

No claim in this client is conditional on its own desired whole-run result.
The only local telescope premises are proved for all actual states, including
empty bit/list states. This is a connected application of the shared API, not
a new general potential hierarchy. It introduces no algorithmic complexity,
forcing, persistence or chapter-completion claim.

Imports identify the existing counter, free additive monoid, current Real
provider (`Mathlib.Basic.Real.Basic`), Nat cast homomorphism/order providers
and the small numeral tactic. The deprecated `Mathlib.Data.Real.Basic`
wrapper and broad tactic imports are avoided. No proof-budget setting,
linter suppression, admission or unchecked proof shortcut was introduced.

## Handoff

Initial draft is ready for root's frozen focused wrapper. Only the assigned
source and report were written. Compilation and all acceptance gates are
pending; no success is inferred from source inspection. Root will return
actual diagnostics before any compiler-directed correction. File hashes are
sent with the freeze notification rather than embedded recursively here.
