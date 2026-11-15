# Halving trace: source candidate and bridge interface

Candidate `45d120ce0f5bacbaac76cbceeca13ee3ff494dff`, tree `68427ffb24fd6dad0fcafa0e44e28dedd25eb844`, fixed parent/base
`3f42358dec92315ac847dc7e1f0c58c2ab26cd40`. Branch `work/fdsa-ch03-rounded-recurrence` in
`conaled-ch02-natural-runs` is clean. The local Conventional Commit is
`feat(resources): bound positive halving traces (#174)`; actual commit and
staged whitespace check `dd0671`, exit 0, command-local ChatGPT identity.

Only Applications/Resources/HalvingTrace.lean (6,430 bytes,159 LF lines) and
Examples/HalvingTrace.lean (3,077 bytes,81 LF lines) are added. All ten earlier
rounded/F/group/outside files and every other parent source path remain exact.
The baseline binds 140 prior related provenance payloads; they remain unchanged.

## Intended and implemented arithmetic

`Resources.HalvingTrace.Halves n sizes` is an indexed proposition. Its `stop`
constructor records a positive singleton [n]; its `step` constructor prepends
n to a positive tail beginning at m under 2*m<=n. Head consistency, positivity,
nonemptiness and positive length are derived. `step_of_le_half` gives the
identical condition through natural floor division; `next_halved` recovers
halving for adjacent recorded sizes. Stopping early above1 is intentional.

The public results establish n<=sizes.sum<=2*n, sizes.length<=sizes.sum and
each entry<=sizes.sum. `pow_edges_le` proves 2^(sizes.length-1)<=n using the
positive terminal entry. `edges_le_log` applies the pinned primary
Nat.le_log_of_pow_le; `edges_le_clog` composes Nat.log_le_clog. Recursive edges
are length-1, while entries count active invocations. `singleton_at_one`
proves every trace at initial1 is [1]; zero initial size is impossible.

The aligned tariff interface uses List.Forall₂, so sizes and charges have the
same length and no charged step is silently omitted. For explicit fixed Nat
A,B and charge<=A*size+B at every position, `affine_charges_sum_le` gives
sumcharges<=A*sumsizes+B*length, then `tariff_sum_le` gives
sumcharges<=(2*A+2*B)*n. A separate alignment size<=charge yields
`initial_le_charges`: n<=sumcharges. The lower premise is independent.

This module does not define an execution, select pivots, or attach a tariff to
an extensional selector. C03-080 remains open until the values author proves
the actual selection-policy trace and the actual per-step charge premises,
including pivot construction, with constants uniform over inputs. The values
author confirmed that these constructors, the edge convention and Forall₂ API
fit the anticipated bridge. No outside-pivot, minimum, PMF or run<=F source was
duplicated. The whole Chapter3 scope remains the original83 obligations.

## Cases and statement review

Independently calculated expectations were saved in requirements-and-cases.md
before source edits, after baseline3ae025. The source includes constructed
traces [8,4,2,1] and [7,3,1], sums15 and11, edge counts3 and2, and the distinct
floor/ceiling logarithms2 and3 for7. It includes [1], its exact invocation and
edge counts, universal singleton forcing, early [8], impossibility at0 and
rejection of [3,2]. Public generic theorems are consumed by the bound clients.

The fixed tariff3*size+2 gives [26,14,8,5], sum53, upper bound80, and lower8
from an independently proved size<=charge alignment. These are scalar examples,
not runtime measurements. statement-review.json records domains, quantifier
order, trace semantics, edge convention, premises, constants and connections.

## Inventory and validation boundary

The exhaustive authored inventory has39 public names:36theorems, one inductive
type and its two constructors. There are no authored private declarations,
anonymous examples or instances. Statements-candidate1.lean includes explicit
@ checks for all39, plus the three expected standard generated eliminators
Halves.rec, Halves.recOn and Halves.casesOn, separately counted. The complete
actual generated declaration set remains for compiler/environment inspection
and the exhaustive audit; a source inventory does not establish it.

All240 final source lines were read at9ba169; all39 raw headers at e38bfc;
prepared inspection input, statement review and pre-source cases at476e39.
Input bindings include exact primary Nat.Log APIs and the source's actual p35
text. An unsupported Mathlib.Tactic.Omega spelling was corrected by source
lookup to official Lean.Elab.Tactic.Omega before commit; no compiler failure
or environment change is claimed for that lookup.

Focused targets are Applications.Resources.HalvingTrace and
Examples.HalvingTrace. At this handoff's preparation no root terminal result
has been received for this candidate. No Lean/Lake, hydration, runtime/pin/profile
change or historical-session poll was performed by the author. Only Nix is
waived. Actual-type inspection, full integrated candidate check/audit, independent
Standards and Spec review and immediate verification remain mandatory. There
is no Chapter3 acceptance or C03-080 closure credit from this source package.

Source and additive provenance are held after the final readback receipt for
the next durability checkpoint. Any later actual focused outcome is to be
recorded additively, preserving the original candidate and this boundary.
