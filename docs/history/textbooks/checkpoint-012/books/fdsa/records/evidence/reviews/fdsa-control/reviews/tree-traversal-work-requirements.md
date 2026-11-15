# FDSA-XT05 — Shared shape-sensitive traversal work

Version 1, frozen 2026-11-02 before implementation. This bounded shared unit
uses the user's cross-cutting exception; it neither activates Chapter 4 nor
changes chapter acceptance order. The complete original request in
`../REQUEST.md`, all chapter/appendix inventories, project standards and
local-ticket/no-GitHub/durable-checkpoint instructions remain in force.

## Baseline, authority and preserved evidence

Original base: `b035f1151ab4f0c7d7380818576cfe97dae434c4`, saved unaccepted
XT04 candidate. Isolated branch `work/fdsa-tree-traversal-work`, checkout
`conaled-tree-traversal-work`. The clean pre-code baseline is recorded in
`tree-traversal-work-start.json`, SHA-256
`e5fb74a86ac40da3c6f93bf7fcc38212955b4ff362a04399eac7937770f01edc`.
Only pinned external dependency packages are linked; project outputs are
isolated. There are no XT05 source edits or compiler results at this freeze.

Root read all three complete bounded preflights and directly read the retained
book traversal/augmentation passages, companion recurrences and C04-017/018
inventory. The readers stopped writing before this freeze. Exact reports:

| Report under `../research/` | SHA-256 | Bytes / lines |
| --- | --- | --- |
| `tree-traversal-work-source-preflight.md` | `85c28138ff1d78f3251ec785c303f03cb6963e8b2b81ebb6af368c85542be750` | 18311 / 308 |
| `tree-traversal-work-api-preflight.md` | `6b8eede3d9cbc161d0f7a3dc137397964c9b6be0992ada8d62da658c2913be4f` | 23149 / 494 |
| `tree-traversal-work-case-preflight.md` | `7286a1e5e38e80229b195f51defbf42c6c98b074dbe0b9b3bbb4bf435c96ea1f` | 16987 / 384 |

The bounded readers did not compute or certify these root-recorded digests.
Their work is preparation, not either final review axis or acceptance.

Accepted repaired Chapter 1, XT01, XT03 and XT04 are prerequisites to integration
or acceptance of this unit. XT02 and XD01 are not dependencies. Preserve every
original base, source history, scope and finding when incorporating accepted
predecessors. In particular, XT03-CP01/DOC01 retain their original correction
evidence and pending compiler/final confirmation as applicable. The minimal
Chapter 2-first integration plan is unchanged; XT05 must not delay it.

## Source and declared execution boundary

The July 27, 2026 book, printed p.48 and Exercise 4.1 on p.49, supplies direct
inorder, its worst-case quadratic claim, and the cons-only accumulator/value/
linear-work obligation. The p.5 append convention fixes literal right
association. `Tree.thy` lines 76–83, 415–416 and 430–431 supplies the retained
recurrences, traversal length and arbitrary-suffix value theorem. The source
inventory and preflight preserve the exact PDF and theory pins and hashes.

The exact formulas below concern the actual saved measured programs: structural
entry `e`, append work `length(left)+1`, and XT01's explicit positive cache
helper tariff. No `T_inorder`/`T_inorder2`, source translator, compiler rewrite,
physical runtime/allocation/sharing or constant-stack result is claimed. The
companion snapshot postdates the manuscript and is not asserted to be its build.

Book p.56/`Tree2.inorder` ignores annotations while traversing an annotated tree.
The actual XT03 whole inorder-list cache construction is a separate application
of generic augmentation, whose full cost is not a printed book timing theorem.
Its returned object is an annotated tree; its root reader observes inorder.
That reader equality does not execute an extra charged read in a theorem.

## XT05-01 — Ordinary shape observation and sharp input families

Use canonical `BinaryTree` and existing ordinary `Trees.fold`. Define public
`Trees.leftSizeSum` as the second projection of a private Nat-pair fold with
empty `(0,0)` and node algebra

```text
(nL,AL), a, (nR,AR)  |->  (nL+nR+1, AL+AR+nL).
```

Prove its first projection is canonical `numNodes` through existing fold
fusion and `fold_numNodes`; do not create a second public size API or new
carrier. The observation is an external mathematical statistic, not an extra
pass silently executed or charged by the algorithms.

Required public facts, writing `A=leftSizeSum` and `n=t.numNodes`:

- `A(nil)=0` and `A(node a l r)=A(l)+A(r)+l.numNodes`.
- Arbitrary label-map invariance, with independent source/target universes,
  no injectivity, equality/order or inhabitant premise.
- `2*A(t)+n <= n^2`, `A(t)+n <= n^2`, and sharp
  `A(t) <= n.choose 2`, all including zero and one node. Use existing Nat.choose;
  no replacement triangular-number definition. A private Pascal-derived
  `2*(n.choose 2)+n=n^2` identity is an appropriate arithmetic bridge.
- Repeated children retain both occurrences: `A(node a t t)=2*A(t)+n(t)`.

Provide generic explicitly supplied-label left/right input chains:
`L(a,0)=R(a,0)=nil`, `L(a,n+1)=node a L(a,n) nil`,
`R(a,n+1)=node a nil R(a,n)`. Prove canonical node count and height are `n`,
both inorder values are `List.replicate n a`, and
`A(L(a,n))=n.choose 2`, `2*A(L(a,n))+n=n^2`, `A(R(a,n))=0`.
These are input constructors, not cost executors. Retain the existing
`TreeCacheExamples.chain` unchanged and prove its equality with the generic
left family at Unit in the connected examples. Supply a label for positive-size
witnesses; never assume such a family exists over Empty.

## XT05-02 — One exact theorem for the actual measured fold

In the resource domain, reuse `Resources.TreeFold.run`; define no new execution
or recursive cost evaluator. Retain independent payload/summary universes.
For fixed natural `entry`, `d`, `c`, empty summary and callback, require

```text
forall finite child trees l,r and label a,
  cost(callback (value(run entry empty callback l)) a
                 (value(run entry empty callback r)))
    = d*l.numNodes+c.
```

The premise is about actual reached child summaries at the same parameters.
It is not an all-summary law or a premise only about one chosen input's
subtrees. Derive for every tree:

```text
cost(run entry empty callback t)
  = entry*(2*n+1)+d*A(t)+c*n.
```

Use actual `run_node_cost`, the reached-child premise, the pure statistic's
constructor law and induction. Retain nil entry, and allow entry/d/c to be
zero. The quantitative algebra is Nat-specific; do not export collected terms
as an arbitrary-Add or noncommutative observation identity. Existing generic
raw grouping, transport and constant-callback theorems remain unchanged.

## XT05-03 — Connected actual append and cache executions

Instantiate the generic theorem through the existing actual value/read/length
bridges; do not replace an execution by a numerical recurrence. Required exact
all-tree formulas, for every natural entry `e`:

| Existing execution | Callback coefficients `d,c` | Actual work |
| --- | --- | --- |
| Single append to cons | 1,1 | `e*(2*n+1)+A+n` |
| Literal right-associated two appends | 1,3 | `e*(2*n+1)+A+3*n` |
| Left-associated comparison | 2,3 | `e*(2*n+1)+2*A+3*n` |
| Full inorder-list cached annotation | 1,4 | `e*(2*n+1)+A+4*n` |

For the first three, use the current step-cost theorem, the value theorem of
the actual child run, and `inorder_length`. For the cache, use the actual
`TreeCache.nodeRun` callback, its append-node cost, and the actual returned
child annotation's `list_read` before `inorder_length`. Preserve the corrected
wrapped/raw-term bridge from XT03-CP01, without weakening it to an assumed
correct arbitrary cache. The coefficient four already includes append's
terminal entry plus the three helper charges; no hidden extra charge.

Retain the independently established inorder values and cache root-reader,
erasure and validity contracts. Full list and full annotated-tree values must
not be identified. Prove the exact natural comparison identities
`Wright=Wsingle+2*n`, `Wleft=Wright+A`, `Wcache=Wsingle+3*n`.
Provide actual literal-right work invariance under arbitrary label maps, using
the pure map/size laws, and a noninjective connected case. This compares given
inputs and does not include a separate map execution.

## XT05-04 — Explicit bounds and actual-family asymptotics

For positive node count, prove universal upper bounds:

| Actual work | Bound |
| --- | --- |
| Single append | `(3*e+1)*n^2` |
| Literal right and left-associated comparison | `(3*e+3)*n^2` each |
| Full inorder-list annotation | `(3*e+4)*n^2` |
| Existing materializeAppend, fixed entry one | `6*n^2` |

For literal right-associated inorder on the left family, prove the exact
chain formula `e*(2*n+1)+n.choose 2+3*n` and the all-n lower bound
`n^2 <= 2*Wright(L(a,n))`. On the right family prove
`Wright(R(a,n))=(2*e+3)*n+e`. The canonical size and inorder theorems must be
connected to these actual executions, so the two families have the same
returned lists for every n.

Use existing `Resources.isBigO_of_nat_bound` and standard
`Asymptotics.IsTheta Filter.atTop` to prove actual literal-right execution
on left chains is Theta of the real cast of `n^2`, and on right chains is
Theta of the real cast of `n`. Parameters `e` and supplied label are fixed
before the eventual index. The upper constants are `3*e+3` with threshold
one; lower constants can be two and one respectively, threshold zero.
These must concern actual run projections, not a new polynomial tally.

At entry one, retain the explicit worst-case witnesses: every positive-size
tree has work at most `6*n^2`, and the supplied left family has size n and
`n^2 <= 2*W`. The right family's `5*n+1` exhibits the all-shapes lower-bound
boundary. Nil still costs e, so include the positive-entry nil countercase
to a pointwise `K*n^2` claim. No blanket quadratic/positive-linear theorem is
claimed for arbitrary d/c: e=d=c=0 has zero observation.

## XT05-05 — Complete existing suffix-program comparison

Reuse the existing actual `TreeAccumulatorExamples.materializeAppend` and
`buildOnce 1 1`. For every tree and arbitrary suffix prove their value equality
through their independent contracts, and separately prove

```text
cost(materializeAppend t suffix) = 4*n+2+A(t)
cost(materializeAppend t suffix) = cost(buildOnce 1 1 t suffix)+A(t).
```

The second program constructs once and invokes its actual returned function;
its cost is `4*n+2`. Construction is included. No cost is inferred from erased
value equality. Derive the right-chain equality of full measured results and
the left-chain exact excess `n.choose 2`, retaining arbitrary suffixes.
Invocation alone still costs `2*n+1` and has a separate boundary. No further
staged program or new closure tariff is required.

## XT05-06 — Independent expectations and statement review

Connect the new public results to the retained independently worked cases:

- Nil and singleton: A=0; entry-one single/right/left/cache counts
  `1/1/1/1` and `4/6/6/7`; invocation `1/3`; the two complete suffix programs
  agree at `2/6`. Reuse earlier cases where they supply the required connection.
- The saved four-node asymmetric sample has A=2. Derive its actual
  single/right/left/cache counts `15/23/25/27` via the new formulas, and the
  full suffix-program comparison `20=18+2`, with invocation-only 9 separate.
- With structural entry zero, the same actual append/cache sample retains
  callback counts `6/14/16/18`; it does not become a zero-work computation.
  A pure zero-cost callback gives an independently useful d=c=0 specialization
  of the new generic theorem, including entry zero.
- A three-node equal-child shape has A=1; general repeated-child law counts
  both occurrences. Noninjective relabeling preserves A and work.
- Generic left/right chains at n=3 have equal canonical size, height and
  inorder but A=3/0 and literal-right work `19/16`. Prove this consequential
  countercase through the chain/value/work results, without label equality.
- Universal facts retain BinaryTree Empty and nil without an inhabitant
  assumption. Positive-size witness claims use a supplied label or Unit.

Per-claim statement review must cover parameter order/universes, actual reached
arguments, fixed coefficients, nil and positivity boundaries, duplicate
occurrences, returned-object distinctions, source association, all-suffix scope,
and construction-versus-invocation. Record source-only proof/API uncertainty
honestly until elaboration. No observed Lean failure is invented.

## Placement, durability and acceptance

Use `Applications/Trees/TraversalWork.lean` for ordinary shape mathematics,
`Applications/Resources/TreeTraversalWork.lean` for the actual generic fold
law, and `Examples/TreeTraversalWork.lean` for the cross-component clients,
inequalities and existing real-cast asymptotics. Extend the public import root,
write `docs/research/fdsa-tree-traversal-work.md`, and append the source map.
Do not import Examples into domain libraries or move/replace old algorithms.

The note must explain original source scope, actual tariffs/connections,
independent expectations, statement assessment, inherited prerequisites and
pending validation. This shared proof device is not book-mandated. The complete
original Chapter 4 work remains: enumeration, weighted paths, levels,
reconstruction, completeness/checker/subtrees, balancing and its actual wrapper
cost, remaining augmented clients, and later chapter algorithms. Exact copied
list sums do not establish physical storage or sharing. No new maximum over
all trees, maximizing-shape classifier, balanced n-log-n family, abstract
history/closure library or general cost translator is required by this scope;
those exclusions do not impose extra future mechanisms on the original task.

Before coding, create and immediately upload checkpoint 0035 containing this
frozen scope, clean branch and all full preflights. Commit every later source
draft before creating its recovery checkpoint; preserve findings and original
bytes if source preflights require correction. No compiler, project checker or
project hash helper runs while old gate 80227 is active. Keep that gate unchanged.

Once accepted prerequisites exist, integrate with ordinary history-preserving
merges/adaptations, retaining the original base and all carried findings. The
complete candidate requires applicable focused development validation, full
candidate build/guards/exhaustive audit, both independent final Standards/Spec
axes on the same immutable candidate and immediate candidate verification.
Preserve exact logs, record and reviews outside active .lake state and create/
upload an acceptance checkpoint. No source-only review, local commit, former
candidate success or this freeze supplies acceptance credit.
