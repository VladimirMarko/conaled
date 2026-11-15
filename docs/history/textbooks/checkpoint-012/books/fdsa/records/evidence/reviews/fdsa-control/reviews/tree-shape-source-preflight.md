# Shared tree-shape draft: bounded source assessments

Recorded 2026-11-02. These are bounded source/API/client readings, **not
compilation, either independent final review axis or acceptance**. No compiler,
project checker, project hash helper, enumeration, cache or gate operation ran
for these assessments. Chapter 1's existing old-candidate gate is unchanged.

## Fixed scope and read inputs

Requirements: `tree-shape-requirements.md`, version 1, SHA-256
`50d11472d8380fb3458a3ea71aba3d1104886f676a7b1cec578c0557a6979e91`.
Initial base: `64c6b777d828ecfe83234fc2aed94600a1f24297`.
The three reviewed source files were held stable during the respective reads:

| File | Supplied identity |
| --- | --- |
| `Applications/Trees/Shape.lean` | `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3` |
| `Applications/Trees/ShapeLog.lean` | `35c0555383fc3d03bcac4f368d41b2c8f744a49e18ef72b192c3753b7ef4497b` |
| `Examples/TreeShape.lean`, before SP01 wording correction | `9b0aacf07d1e9fe62f540abba5d24a387f3e962c9711d253fdb8d105001436f7` |
| `Examples/TreeShape.lean`, after the one-line correction | `2bcf2b65fa7a0eccc043c3bc7ba66d1bfdcd469489eab52d9085fdfb3db0b516` |

Root computed ordinary file identities; the independent readers did not run
project hash helpers. The exact original example source is retained at
`tree-shape-preflight-snapshots/Examples-TreeShape-before-SP01.lean` under its
original hash. No formal declaration, proof body or interface changed in that
correction. Public-root integration and reconstruction documentation were
outside these bounded independent reads.

## Architecture/API assessment

The retained `/root/architecture` contributor read the full frozen scope and
natural core, followed by the actual real bridge. It found no concrete
statement, pinned-API or proof-route mismatch in those files.

The natural pass checked the existing-fold definition, recursive rather than
numerically defined completeness, source subtraction equivalence, arbitrary
map transport and independent universes. Nil remains in every universal bound;
only the first tree in `height_optimal` needs almost completeness, and its
size premise remains an inequality.

The lower and upper nonstrict inductions supply actual exponent-monotonicity
facts. The strict upper induction splits child maximum heights; the strict
lower induction splits child minimum heights. In the latter equal-minimum case,
completeness/height equivalence correctly supplies the missing maximum-height
equality. The equality converses use the correct orientations, including
`h.symm` in the minimum-bound contradiction.

The reader inspected the pinned natural power interfaces, including the
positive-base premise of `Nat.pow_le_pow_right`, the base-greater-than-one
premise of `Nat.pow_lt_pow_right`, and `Nat.pow_succ`. It also inspected the
installed Lean configuration: Omega's min/max, disjunction and natural
subtraction splitting are enabled by default. This supports the intended
proof route without establishing that the tactic scripts elaborate.

Both natural log argument orders match the pin. The floor case supplies a
nonstrict lower power bound and strict upper bound. The ceiling case combines
minimum-height strictness with the general ceiling upper bound and almost
completeness, so it needs neither a predecessor nor positive-height premise.
Optimality reduces directly to `clog_le_of_le_pow` after converting nodes to
leaves and using the other tree's power upper bound.

For the real bridge the reader confirmed actual use of the correct four logb
equivalences, base proof first and positive leaf count second. Rewriting
`Real.rpow_natCast` leaves the intended natural-exponent real inequality, and
each `exact_mod_cast` consumes the corresponding discrete theorem. Complete
real equality follows from the sandwich and completeness/height identity.
The exact natural floor and ceiling bridges use the pinned argument order.
No extra inhabited-label, nonempty-tree, order or equality assumption appears.

The earlier focused API follow-up also confirmed that `Real.rpow_natCast`
requires no sign hypothesis, and that the ordinary analytic import supplies
the required mathematics. `omega` and `exact_mod_cast` are implemented through
the pinned Lean tactic modules; no nonexistent `Mathlib.Tactic.NormCast` import
or broad new tactic import was introduced.

## Source-correspondence assessment

The retained `/root/book_inventory` contributor read the full requirements and
three supplied stable files, plus the particular XT01 fixtures needed to
identify sample, chain and corrupt annotation shapes. It found no concrete
source/domain/formula mismatch within the bounded scope.

It confirmed the external-leaf convention, recursive predicates, both sharp
bounds and equality converses, nonstrict universal rounded bounds and exact
almost-complete formulas. The actual real sandwich/strictness/complete equality
and natural floor/ceiling bridges preserve positive leaves and the empty case.
The optimum keeps unrelated payload universes and only the intended first-tree
shape assumption. The concrete examples invoke the intended public results.

Executable checking, arbitrary subtrees, the constructor exercise,
Braun/weight-balance invariants and algorithms, leftist representation and
queue operations, and work models remain separate obligations. A minimum-cache
reader is not a replacement for existing leftist rank/validity proofs. This
source pass did not inspect elaborated types or establish tactic success.

## Independent client assessment and retained finding

The retained `/root/tail_examples_preflight` contributor read the three complete
files and requirements, its independent hand calculations, and targeted cache
and log API sources. It found no concrete mathematical theorem error or obvious
pinned-API mismatch, but reported the following required wording correction.

### XT02-SP01 — Recursive cache validity described as necessary

- Severity: minor documentation/statement-description issue.
- Original location: `min_reader` docstring in `Examples/TreeShape.lean`.
- Original text: “A cached minimum is correct only under the existing all-node
  validity law.”
- Finding: the theorem correctly states that recursive validity is sufficient,
  not necessary for an individual root observation. Necessity is false.
- Independent counterexample: `node ((),1) (node ((),99) nil nil) nil` has root
  reader one and structural minimum one. Its root is even locally consistent,
  because `min 99 0 + 1 = 1`, while the left child's cache is invalid.
- Implemented correction: “Recursive validity makes the cached minimum agree
  with the structural observation.” The theorem and all proof bodies are
  unchanged. Reconstruction prose records the same distinction.
- Status: correction implemented and confirmed by the same independent client
  reader in a narrow current-docstring versus preserved-snapshot recheck. It
  confirms the sufficient-premise wording only. Final review confirmation
  remains pending with the unit's ordinary acceptance loop.

The independent client pass specifically checked that the Boolean optimum
counterexample is an actual four-node witness, its comparison consumes the
Nat-labelled sample's public optimum, and its generalized optimum remains
paired with explicit failure of almost completeness. The local-balance
predicate includes recursive child conditions, so the seven-node example
really has the property at every node, with leaves eight/minimum two/height four.

The minimum cache is produced by the actual saved `annotate`; its reader uses
the generic validity theorem and erasure/shape connection. The corrupted-cache
example uses unconditional erasure laws and keeps invalid size annotations
explicit. It does not claim that those corrupted size fields compute minimum
height. Empty/singleton, complete/right-heavy/skew trees, real strictness versus
rounded equality, the node-plus-one offset and a genuinely noninjective map
all match the independent expectations.

## Remaining acceptance work

The fixed initial base and corrected draft remain unaccepted. After accepted
repaired Chapter 1 and XT01 are incorporated under the retained history rules,
the complete matching candidate still requires focused compilation, applicable
build/guards, exhaustive axiom audit, both independent final review axes and
immediate candidate verification. All findings and scope boundaries survive
that integration. This record supplies neither acceptance credit nor a reason
to repeat an unchanged preflight as though it were new evidence.
