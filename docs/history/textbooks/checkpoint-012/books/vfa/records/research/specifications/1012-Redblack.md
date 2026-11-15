# Local #1012 — VFA Redblack: requirements and reuse plan

**Planning only, 2026-11-02. Implementation is blocked until #1011 Extract is accepted.**
The chapter sequence remains ADT → Extract → Redblack → Trie. This file adds
no algorithm implementation, Lean proof, compiler result, chapter acceptance,
tracker change, candidate change, or new review loop. The current root-owned
Preface/Perm validation remains independent of this preparation. Proposed names
must be reconciled with the actual accepted predecessor APIs before coding.

## 1. Source, scope, and inspected baseline

- Complete inspected chapter: VFA 2.1, release cover `2026-08-24 10:11`,
  [Redblack](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Redblack.html),
  `reference/vfa/vfa/Redblack.v`: **838 lines, 27,066 bytes**, SHA-256
  `f44255ba3d0235f6efa401b72f2fcf9a9551a7ebc065912202d6f33494891ce2`.
  Its footer is `2026-08-24 09:43`.
- `../source/Redblack.inventory.json` contains **45 records, 13 exercises,
  six pedagogical commands, and no module records**. The records comprise
  15 definitions, four deliberately abandoned proofs, eight source-proved
  declarations, 16 source admissions, one Coq tactic stub, and one grading
  marker. Twelve exercises are standard; `redblack_bound` is advanced.
  None is optional. All are in scope, including both definition holes in the
  advanced exercise and the admitted tactic used by a theorem.
- The complete 24-line auxiliary program `reference/vfa/vfa/test_searchtree.ml`
  was inspected. Its workload and timing boundary are part of the chapter's
  execution obligation. The accepted Extract driver will be reused after its
  acceptance; its frozen planning identity is recorded in section 12.
- The official versioned archive is
  <https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz>, SHA-256
  `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
  Follow `../source/SOURCE-RECOVERY.md`, retain MIT attribution, and exclude
  downloaded research copies from deliverables under ADR 0001.
- Inspected checkout: `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`;
  Lean 4.35.0, revision `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`;
  Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`.
  This is an inspected candidate, not an accepted chapter baseline.
- Read AGENTS, architectural/domain guidance, GLOSSARY, ADRs 0001/0010,
  implementation and example-driven-development guidance, review/build/audit
  policy, `../REQUIREMENTS.md`, the complete chapter and driver, predecessor
  plans, and the tree-invariant, computational-assumption, and resource notes.
  Inspected actual pinned provider definitions and theorem types, including
  the complete `RBTree/Depth.lean`. No compiler or import-closure check was run
  for this plan. Exact inspected file identities appear in section 12.

The intended result retains the source's raw colored trees and exact insertion
recurrence, proves its independent ordering and balance contracts, connects
its observations to accepted tables, and supplies explicit structural cost
bounds and an executed comparison with the accepted ordinary-tree program.
Existing map APIs or an unrelated logarithmic-height theorem cannot replace
the source algorithm and its stated hypotheses without proved adapters.

## 2. Architecture, key assumptions, and actual reusable interfaces

Use a small Redblack family beside the accepted `Applications/Tables`
SearchTree/Extract modules. Separate substantial resource instrumentation and
the IO workload driver from the pure table development. Cross-domain clients
belong in `Examples`; source references and coverage belong in the research
documentation. Do not introduce a generic tree hierarchy, new finite-map
framework, new comparator class, or an extraction backend for this chapter.

The first carrier choice is the existing raw `RBTree.RBNode (W × V)` with
`RBTree.RBColor`: `.nil` presents source E and
`.node c l (k,v) r` presents source `T c l k v r`. Small aliases/constructor
adapters retain every raw input, including malformed trees. This reuses a
matching colored-node datatype without making the sealed library map's
operations the source operations. The provider warns that users should
prefer `Std.TreeMap` and that its RBTree implementation will eventually be
deprecated. Record that bounded pinned dependency in the chapter note; do
not replace source recurrences merely to use the recommended map container.
The public chapter remains a source-specific table realization, not a new
general-purpose replacement for Std's containers.

Reuse Extract's ordinary parameters `W`, `decode : W → Int`, and executable
`ltb : W → W → Bool`. Its proved realizations supply
`ltb a b = true ↔ decode a < decode b` and injectivity of `decode`.
Redblack does not use `leb`, addition, a decoder inverse, or surjectivity.
Reuse the accepted signed `Int`/identity, `BitVec w` signed-comparison, and
`Int64` realizations; do not assume new integer axioms. A finite word remains
a bounded carrier. Default BitVec order is unsigned and cannot silently stand
for this signed comparison interface.

Keep the hypotheses at their actual boundaries:

- Storage, colors, traversal, nonemptiness, arbitrary all-node predicates,
  balance shape, and measured structural recurrences need no lawful key
  ordering or decoder injectivity. Shape preservation can split arbitrary
  Boolean comparison outcomes.
- `balance_BST` needs decoded strict separators and valid subtrees; the
  balancing function itself performs no key comparison. `ins_BST` and the
  semantic lookup laws use strict-comparison reflection. Same-key lookup
  and decoded operation commutation do not require decoder injectivity.
- Distinct-original-key lookup preservation and identification of a found
  original key use injectivity. Two different values of W with the same
  decoded integer would otherwise be indistinguishable to search.
- No operation needs an order or equality decision on V. A default is a
  caller argument to lookup, not an inhabitance requirement on all payloads.
  Any equality decision needed by a mathematical `Function.update` client
  stays separate from the executable Boolean tree branches.

Do not let `LinearOrder.lift' decode` silently change execution to decoded
Int comparison. Accepted Extract adapters must retain the supplied Boolean
decisions and their short-circuit order. An order instance used solely in a
proof or in a relation adapter is a different use from an executable branch.

| Inspected provider | Exact reuse and remaining obligation |
| --- | --- |
| `RBTree.RBColor`, `RBNode.nil/node`; Batteries `RBTree/Basic.lean` | Exact raw color and colored-node shape after packaging key/value labels. Preserve arbitrary raw trees and source constructor equations. |
| `RBNode.All`, `All.imp` | `All p nil=True`; at a node it is `p label ∧ All p left ∧ All p right`. Present source `ForallT P` through `p (k,v)=P k v`; use `All.imp` for predicate weakening and separator transitivity. |
| `RBNode.foldr`, `toList`; `foldr_cons`, `toList_node`, `mem_toList`, `All_def` in `RBTree/Lemmas.lean` | Foldr has exactly the source accumulator recurrence. `foldr_cons` states `t.foldr (·::·) acc = t.toList ++ acc` for every raw tree and accumulator. Use it before transferring inorder properties. |
| `setBlack`, `setBlack_idem`, `setBlack_toList`, `Ordered.setBlack`, `Balanced.setBlack` | `setBlack` is exactly source root blackening, including nil. The last theorem produces an existential new black height and a black root. It does not preserve black height in every case. |
| `RBNode.Ordered`, `cmpLT`, `cmpLT_iff`, `ordered_iff`, `Ordered.toList_sorted` | Ordered is a full-subtree separator predicate and is equivalent to Pairwise inorder `cmpLT`. `cmpLT` wraps `∀ [Std.TransCmp cmp]`; establish an actual lawful key comparator and its decoded-order relation before using this equivalence. A vacuous conditional comparator property is not source BST. No payload order or comparator equality of all payloads is required. |
| `Ordered.balance1`, `Ordered.balance2`, `balance1_All`, `balance2_All`, `balance1_toList`, `balance2_toList` | Existing side-specific rotation facts. All/inorder equations have no BST/RB premise; Ordered equations take both valid subtrees and both separator bounds. Apply only through the actual selected source case/observation bridge; priorities differ on overlapping raw cases. |
| `RBNode.find?`, `find?_some_eq_eq`, `find?_some_mem`, `Ordered.memP_iff_find?`, `Ordered.find?_some`, `Ordered.unique` | Optional search uses one Ordering-valued cut. Forward membership is unconditional; converses use Ordered, actual `Std.TransCmp`, and `IsCut` or `IsStrictCut`. A cut derived from the two source Boolean tests needs its own recurrence/semantic adapter. Equal comparator keys do not imply globally equal key/value records; `Ordered.unique` additionally requires both records occur in the same ordered tree. |
| `RBNode.Balanced`, `RedRed`; `Balanced.ins`, `RedRed.balance1/2`, `balance1_eq`, `balance2_eq` | Root-color balance and temporary red-red predicates, with precise meanings in section 4. The ins theorem is about the library algorithm, so it is not a source insertion theorem without an operation bridge. |
| `WF.out`, `WF_iff`; Batteries `RBTree/WF.lean` | `WF cmp t ↔ Ordered cmp t ∧ ∃ c n, Balanced t c n`. Use the proved equivalence, not the closure constructors of WF as an unproved justification of source invariants. The chapter need not introduce a WF wrapper if separate BST/RB facts suffice. |
| `RBNode.size`, `depth`, `Balanced.depth_le`, `Balanced.le_size`, `Balanced.depth_bound`; `RBTree/Depth.lean` | Size counts internal nodes. Depth is zero on nil and max child depth plus one. Root-color-sensitive black-height bounds yield `depth ≤ 2*(size+1).log2`. A proved source RB/shape adapter is required; this does not by itself discharge the minimum-depth exercise or an operation cost claim. |
| `BinaryTree.nil/node`, `map`, `height`, `numNodes`; Mathlib `Data/Tree/Basic.lean` | Existing uncolored carrier used by accepted SearchTree/Extract. Erase colors while retaining every original key/value, and prove lookup/all-node/inorder/shape correspondences. Colored insertion does not commute with ordinary unbalanced insertion as a structural equality. |
| Accepted Maps/ADT table API; staged `TablePreparation.Ops`, separate `Laws`, `observe_set`, `ObservedEq`, `twoWrites_equivalent` | Operations are empty/get/set; validity is a separate predicate. Instantiate source lookup laws with `Valid := BST`, not True and not an unnecessarily stronger balance invariant. A separate efficient-state predicate can combine BST with `∃ n, RB t Red n`. The staged file is evidence only until its accepted integration. |
| Accepted partial-map/default and enumeration APIs; `Function.update` | Preserve actual optional bindings, including a stored default. Source lookup algebra transports through the valid table observation law. Enumeration and binding equality need their own refinement facts; total default-valued equality alone loses presence. |
| `Resources.Measured`, `bind`, `bind_erases`, `reweight`, `erasureSquare` | Instrument the exact source branches and prove value erasure. Measured/bind support separate universes; `erasureSquare` currently packages its types in one universe. Do not constrain every generic payload merely to use the square wrapper. Equal values do not imply equal costs. |
| `Resources.isBigO_of_nat_bound` | Converts an explicit eventual Nat inequality into real-cast `Asymptotics.IsBigO`. Supply the actual size family, logarithmic function, constants, primitive costs, and threshold first. |

The pinned `RBNode` BEq compares inorder streams and ignores shape/colors.
It must not be used as a test for structural equality in the source/library
counterexamples. Use propositional constructor/root observations. A successful
Boolean inorder comparison is not evidence that the two algorithms constructed
the same colored tree.

## 3. Exact operation requirements and case priority

The following are mathematical specifications, not new Lean implementation.
Write `N_c(l,p,r)` for a colored node whose entry is `p=(k,v)`, and E for nil.
Every equation is required on raw trees, not merely on well-formed ones.

| Operation | Exact source recurrence |
| --- | --- |
| `empty_tree` | E, with no default payload. |
| `lookup d q E` | d. |
| `lookup d q N_c(l,(k,v),r)` | If `ltb q k` then recurse left; otherwise if `ltb k q` then recurse right; otherwise v. Color is ignored; the second comparison is short-circuited. |
| `ins k v E` | `N_Red(E,(k,v),E)`. |
| `ins k v N_c(l,(x,w),r)` | Test `ltb k x`, then `ltb x k`. Recurse into the selected child and call the full source balance with color c. Equality returns `N_c(l,(k,v),r)`, replacing the key as well as the value. |
| `make_black` | E stays E; every node becomes `N_Black` with the same children and entry. |
| `insert k v t` | `make_black (ins k v t)` unconditionally, regardless of the input root color. |
| `elements_aux E acc` | acc. |
| `elements_aux N_c(l,(k,v),r) acc` | `elements_aux l ((k,v) :: elements_aux r acc)`. |
| `elements t` | `elements_aux t []`. |
| `ForallT P E` / `ForallT P N_c(l,(k,v),r)` | True / `P k v ∧ ForallT P l ∧ ForallT P r`. |

The balance cases are ordered. A row applies only if every earlier row that
could match has failed. Here x, y, z are entire key/value entries and a, b, c,
d are subtrees; subtree c is unrelated to the root-color parameter.

| Priority | Inputs to balance | Result |
| --- | --- | --- |
| 1: red root | Red, any l, p, r | `N_Red(l,p,r)`, with no child-pattern inspection. |
| 2: left-left | Black, `N_Red(N_Red(a,x,b),y,c)`, z, d | `N_Red(N_Black(a,x,b),y,N_Black(c,z,d))`. |
| 3: left-right | Black, `N_Red(a,x,N_Red(b,y,c))`, z, d | `N_Red(N_Black(a,x,b),y,N_Black(c,z,d))`. |
| 4: right-left | Black, a, x, `N_Red(N_Red(b,y,c),z,d)` | `N_Red(N_Black(a,x,b),y,N_Black(c,z,d))`. |
| 5: right-right | Black, a, x, `N_Red(b,y,N_Red(c,z,d))` | `N_Red(N_Black(a,x,b),y,N_Black(c,z,d))`. |
| 6: fallback | Black with all four red-red patterns absent | `N_Black(l,p,r)`. |

Do not swap the right cases or balance only the recursively changed side.
The source balances the entire node after either recursive branch. On an
arbitrary ordered tree that violates RB, a pre-existing left violation can
take priority even when insertion recursed right. The source's BST-only
theorems explicitly retain such inputs.

The existing library differs in three concrete ways:

1. `balance2` tries right-right before right-left. If a red right child has
   two red children, both patterns match and the roots of the results differ.
2. Library ins uses only balance1 after a black node's left recursive call,
   and only balance2 after its right call. Source ins uses the complete
   left-first function after either call.
3. Library insert blackens only if the input root was red. On E it returns
   a red singleton; source insert returns a black singleton.

`insert_setBlack` proves the library's own post-blackening identity. It does
not prove source-ins equality. A valid-input algorithm adapter is possible
only after proving the needed overlap exclusions and branch correspondence.
`NearlyRB` alone permits both red children at its red root, so that predicate
alone does not justify swapping the right-case priority. Such an adapter is
optional reuse work:
the minimal route is direct source-case proofs with shared All/inorder/shape
facts. No valid-only adapter can replace the source BST-only balancing laws.

## 4. Ordering, balance, and observation proof boundaries

### Ordering and table behavior

Source BST is True on E. At `N_c(l,(k,v),r)` it requires BST of both children,
every decoded left key strictly below `decode k`, and every decoded right
key strictly above it. Child-root comparisons alone are insufficient.

Prove separator propagation with the generic all-node implication law, then
prove balance preserves BST from precisely those four subtree premises.
Prove balanceP independently for arbitrary P, and use it in insP and ins_BST.
Recoloring then yields insert_BST without a second induction. None of these
ordering results assumes RB.

The balance lookup equation must retain its exact quantifiers and comparison
orientation. For arbitrary d and queried q, ordered children and both strict
separator bounds imply

```text
lookup d q (balance color l k v r) =
  if decode q < decode k then lookup d q l
  else if decode k < decode q then lookup d q r
  else v.
```

The displayed conditions denote decidable Int comparisons, corresponding to
source `<?` and `>?`. Prove their agreement with the supplied Boolean ltb;
do not silently exchange the two operands of the second test.
Both same-key and distinct-key lookup-after-ins theorems retain `BST t`.
The insert versions follow by lookup's insensitivity to root recoloring.
The empty lookup theorem is unconditional. Use the resulting accepted table
Laws instance at BST to derive update observations and shared clients.

### Parent color, root color, and black height

The source index in `RB t parent n` is the **parent's** color. Its exact
constructor rules are:

```text
RB E parent 0
RB l Red n  ∧ RB r Red n  → RB (N_Red(l,p,r)) Black n
RB l Black n ∧ RB r Black n → RB (N_Black(l,p,r)) parent (n+1).
```

Every path has the same number n of black internal nodes. E contributes zero;
do not count a conceptual black sentinel as another node. A tree under a
hypothetical red parent must have a black root or be empty. Under a black
parent, its own root may be red. Source `RB_blacken_parent` changes only the
logical parent index and does not modify the represented tree.

The pinned library Balanced index instead records the **root** color.
Under the constructor adapter C, establish the exact bridges

```text
RB t Red n   ↔ Balanced (C t) black n
RB t Black n ↔ ∃ rootColor, Balanced (C t) rootColor n.
```

If the source-facing predicate is defined using the existing predicate,
prove all three source constructor/elimination characterizations explicitly;
an unexamined alias is not a statement review. An independent source-facing
inductive presentation may instead use these proved iff adapters. Avoid two
parallel balance proof libraries when the exact constructor contract can be
presented from the existing one.

NearlyRB requires a nonempty tree. Its red-root case allows both children to
satisfy `RB _ Black n`, so a red-red violation may occur only at the root;
its black-root case has those same children and black height n+1. Establish

```text
NearlyRB t n ↔ C t ≠ nil ∧ RedRed True (C t) n.
```

Nonemptiness cannot be dropped: library RedRed includes nil through its
balanced constructor. Prove ins_not_E independently of all invariants.
Retain both conclusions of the simultaneous source induction:

```text
(RB t Black n → NearlyRB (ins k v t) n) ∧
(RB t Red n → RB (ins k v t) Black n).
```

These are shape claims without BST, comparison reflection, or injectivity.
The accepted proof must replace `prove_RB := admit` with ordinary kernel-
checked case analysis, invariant inversion, constructor proofs, and reusable
lemmas. Lean tactics need not mimic the Ltac syntax. Prove the second
projection as ins_red, then compose it with root blackening:

```text
RB t Black n → ∃ n', RB (make_black t) Red n'
RB t Red n   → ∃ n', RB (insert k v t) Red n'.
```

The existential permits a changed black height. A red singleton has black
height zero; blackening it gives black height one. Empty stays at zero.
Do not state that root blackening preserves n or that ins already has a
black root. Empty plus insert_BST and insert_RB supplies a nonvacuous valid
insertion-history realization with both ordering and shape maintained.

### Color erasure and complete relevant enumeration reuse

Define the ordinary constructor-preserving color erasure to the accepted
Extract tree, retaining original W keys and V payloads. On every raw tree,
prove lookup equality for the same Boolean branches, ForallT correspondence,
BST equivalence, and the all-accumulator traversal equation. Mapping decoded
keys into an Int-labelled ordinary tree is a separate map; comparison
reflection supplies its lookup compatibility. It must not replace the
runtime key representation.

Source elements can use the exact existing foldr/toList recurrence. Establish
`elements_aux t acc = elements t ++ acc` and equality to accepted ordinary
inorder traversal of the erasure, for arbitrary acc and without BST or RB.
The same erasure preserves height and internal-node count. It does not
commute with source insertion and ordinary insertion as raw-tree equality,
because the former rotates and recolors.

The prose at 598–603 invites reuse of the SearchTree elements facts. Transfer
the relevant full contract, preserving its hypotheses rather than copying
proofs or merely claiming that colors are ignored:

| Observation / law | Required bridge and scope |
| --- | --- |
| All-node predicate and relation-to-a-key membership | Through color erasure or `All_def` and exact inorder equality, on every raw tree. |
| Successful search gives an enumerated binding | Through accepted bound/optional-search observations on the erased tree; retain comparison reflection and original-key identification. Default-valued lookup alone is not success. |
| Enumerated binding gives presence and lookup for every default | Requires BST; retains the accepted raw-versus-valid asymmetry and both absence converse scopes. |
| A successful bound has a default-independent value | Preserve `∃ v, ∀ d`, not a witness that may vary with d. Source Redblack need not add a separate runtime bound algorithm when the accepted optional observation supplies it. |
| Strict decoded-key order, source non-strict sortedness, and key nodup | BST is sufficient, with no RB hypothesis and no payload order. Nodup is of projected keys, not only complete pairs. |
| Empty and update enumeration | Empty is []; each source rotation preserves exact inorder sequence on all raw inputs. Prove source `elements (insert k v t) = kvs_insert k v (elements t)` under BST using that recurrence and the accepted replacement-aware list insertion. A structural insertion-erasure equation would be false. |
| Partial-map abstraction, bound/lookup/update correspondence | Reuse accepted head-winning list decoding and the presence/default seam. Prove the source update bridge from actual enumeration/optional bindings; do not infer presence from one-default lookup equations. |
| Direct structural abstraction coherence | Apply accepted Abs/Abs' agreement to the erased BST; the collision-removing structural union still has its original definition and hypotheses. |
| Canonical enumeration | Two BSTs with identical partial-map bindings have equal inorder lists. Total lookup agreement for one default cannot replace equal bindings. |

These bridges connect the new balanced realization to the accepted maps,
ADT observations, and ordinary-tree client. Shape facts remain independent;
ordered but RB-invalid examples must still satisfy all BST-only laws.

## 5. Complete 45-record disposition

Each exact lexical source ID occurs once in this table. Targets are later
Lean obligations, not implementation or acceptance claims. Repeated source
names at abandoned attempts remain distinct records.

| Source record | Intended obligation / adaptation |
| --- | --- |
| `Redblack.key@46` | Reuse accepted Extract carrier W, decoder, executable strict comparison, and proved laws/realizations. No new axiomatized int. |
| `Redblack.color@48` | Existing red/black datatype with exact source constructor presentation. |
| `Redblack.tree@50` | Existing raw colored-node carrier over W×V; exact E/T correspondence without an invariant wrapper. |
| `Redblack.empty_tree@57` | E-valued empty operation, arbitrary payload type. |
| `Redblack.lookup@64` | Exact color-ignoring two-Boolean-test recurrence and color-erasure bridge. |
| `Redblack.balance@83` | Exact six ordered cases in section 3; both right-case priority and left-before-right priority are observable on raw trees. |
| `Redblack.ins@103` | Exact recursive search, complete balance after either recursive branch, and replacement of both key and value in equality branch. |
| `Redblack.make_black@111` | Exact setBlack adapter on E and nodes. |
| `Redblack.insert@117` | Unconditional final blackening of source ins. |
| `Redblack.elements_aux@123` | Exact foldr accumulator traversal; prove arbitrary-accumulator equality and uncolored observation bridge. |
| `Redblack.elements@130` | Accumulator traversal at [], with complete relevant enumeration reuse. |
| `Redblack.ins_not_E@149` | Abandoned manual proof, not a false theorem. Map its statement to the completed theorem; preserve the explanation of progressively automating match cases. |
| `Redblack.ins_not_E@208` | Source ins produces a nonempty node on every raw tree for arbitrary Boolean comparator. Derive insert nonemptiness as the introductory prose also promises. |
| `Redblack.ForallT@237` | All-node predicate independent of order, search reachability, and balance. Reuse actual All constructor equations. |
| `Redblack.BST@243` | Full-subtree strict decoded-key separators and both valid children, with source constructor/elimination interface. |
| `Redblack.empty_tree_BST@252` | Valid empty tree, no RB premise and no payload inhabitance. |
| `Redblack.insert_BST@259` | Abandoned statement preview; map to the final insertion-preserves-BST theorem and its prerequisite proof route. |
| `Redblack.balance_BST@269` | First abandoned proof, same correct four-premise statement. Preserve the case-splitting lesson, not a claim that Lean generates exactly 58 goals. |
| `Redblack.balance_BST@331` | Second abandoned attempt, same statement. Preserve the identified need for transitive all-subtree bound propagation; the reported 41 remaining Coq goals are historical proof-state detail. |
| `Redblack.ForallT_imp@368` | All-node P plus pointwise P→Q implies all-node Q. Reuse All.imp in the exact argument direction. |
| `Redblack.ForallT_greater@378` | All decoded keys >decode k and decode k>decode k0 imply all decoded keys >decode k0. |
| `Redblack.ForallT_less@387` | All decoded keys <decode k and decode k<decode k0 imply all decoded keys <decode k0. |
| `Redblack.balance_BST@398` | Completed ordering-preservation theorem from both separator predicates and both child BST proofs, with no RB premise. |
| `Redblack.balanceP@428` | Balance preserves arbitrary all-node P from P on l, r, and the root entry; no order or balance premise. |
| `Redblack.insP@444` | Source ins preserves arbitrary all-node P from P on the old tree and newly written pair. Use balanceP and structural induction. |
| `Redblack.ins_BST@458` | BST preservation by source ins, using strict-comparison reflection, all-node preservation, and balance_BST. |
| `Redblack.insert_BST@471` | BST preservation by insert via ins_BST and color irrelevance; no new induction or RB assumption. |
| `Redblack.lookup_empty@490` | Every query and caller default on E returns that default. |
| `Redblack.balance_lookup@501` | Exact decoded-Int two-branch lookup equation from BST l/r and both separators. No RB or key inequality premise. |
| `Redblack.lookup_ins_eq@528` | For BST t, lookup at the written key after source ins yields the written value; preserve the required invariant. |
| `Redblack.lookup_ins_neq@541` | For BST t and distinct original written/queried keys, lookup at the queried key is unchanged. Use decoder injectivity in addition to comparison reflection. |
| `Redblack.lookup_insert_eq@556` | Same-key map law for insert through lookup's root-recoloring invariance and the ins law. |
| `Redblack.lookup_insert_neq@563` | Distinct-key map law for insert with the same BST and original-key inequality premises. |
| `Redblack.RB@642` | Exact parent-color/equal-black-height predicate with all three source constructor rules; prove the Balanced bridge and account for E at height zero. |
| `Redblack.RB_blacken_parent@658` | RB t Red n implies RB t Black n, with tree and black height unchanged; this is a predicate implication, not a recoloring operation. |
| `Redblack.NearlyRB@669` | Nonempty temporary root-red-red predicate with exact red and black constructor cases; RedRed True bridge includes nonemptiness. |
| `Redblack.prove_RB@692` | Remove the source admitted tactic's logical gap. Use proved Lean case/inversion/constructor reasoning in the actual ins_RB proof; no new axiom, tactic admission, or Ltac emulation framework. |
| `Redblack.ins_RB@694` | Prove both parent-color-dependent conclusions simultaneously, preserving the same n and no BST/order hypotheses. |
| `Redblack.ins_red@725` | Second projection of ins_RB: RB t Red n implies RB (ins k v t) Black n. |
| `Redblack.RB_blacken_root@738` | RB t Black n implies existence of n' with RB (make_black t) Red n'; retain possible black-height change. |
| `Redblack.insert_RB@751` | Compose ins_red and root blackening: RB t Red n implies existence of n' with RB (insert k v t) Red n'. |
| `Redblack.height@777` | Complete the executable hole with height E=0 and height node=1+max child heights; identify it with existing depth/color-erased height. |
| `Redblack.mindepth@780` | Complete the executable hole with mindepth E=0 and mindepth node=1+min child minimum depths. It is not black height or maximum depth. |
| `Redblack.redblack_balanced@783` | For every parent color and black height, RB implies height≤2*mindepth+1. Prove the auxiliary black-height upper/lower path bounds, including red-root cases. |
| `Redblack.manual_grade_for_redblack_bound@790` | Omit grading data from the library; the definitions, advanced theorem, source proof method, and connected size/cost obligations remain required. |

## 6. All 13 exercises

| Exercise and exact source range | Completion evidence |
| --- | --- |
| `balanceP`, 423–437, standard, 2 stars | Arbitrary-P all-node preservation with actual source case analysis; order-independent checked use. |
| `insP`, 439–451, standard, 2 stars | Inductive preservation using balanceP, including replacement and both recursive branches. |
| `ins_BST`, 453–464, standard, 3 stars | Actual source ins preserves decoded strict BST; no balance hypothesis added. |
| `insert_BST`, 466–476, standard, 2 stars | Source insertion preserves BST via recoloring. |
| `balance_lookup`, 496–516, standard, 4 stars | Exact default/query equation for each rotation and fallback, using only stated ordering hypotheses. |
| `lookup_ins_eq`, 518–534, standard, 3 stars | Same-key lookup under BST; use prior lemmas rather than an unrelated map implementation. |
| `lookup_ins_neq`, 536–549, standard, 3 stars | Distinct-original-key preservation, with injective interpretation accounted for. |
| `lookup_insert`, 554–571, standard, 2 stars | Both same-key and distinct-key insert laws. One theorem does not complete the exercise. |
| `RB_blacken_parent`, 653–663, standard, 1 star | Parent-index weakening with no represented mutation. |
| `ins_RB`, 679–721, standard, 4 stars | Both simultaneous conclusions and a fully proved replacement for the admitted tactic. |
| `RB_blacken_root`, 731–744, standard, 1 star | Black-root result with existential height and a case witnessing its change. |
| `insert_RB`, 746–757, standard, 1 star | Insertion preserves black-root RB existence, using the exact source insert. |
| `redblack_bound`, 759–792, advanced, 4 stars | Both executable definitions, auxiliary path/black-height inequalities, and the exact minimum-depth theorem for either parent color. Grading marker is not mathematical work. |

## 7. Commands, abandoned attempts, and substantive prose

All six inventoried pedagogical commands have a disposition:

| Source command | Lean adaptation |
| --- | --- |
| `Check` at 576 | Check/export valid-empty statement for arbitrary V. |
| `Check` at 580 | Check/export insert_BST with exactly a BST input premise. |
| `Check` at 584 | Check/export unconditional lookup_empty and arbitrary default/query. |
| `Check` at 588 | Check/export same-key insertion lookup law with BST. |
| `Check` at 592 | Check/export distinct-key insertion lookup law with BST and original-key inequality. |
| `Extraction` at 799 | Deliver actual runnable Lean empty/insert/lookup/elements code using the proved realization, through accepted Extract's direct and standalone execution paths. Exporting only theorems or running an unrelated library map does not discharge it. |

The remaining source commands and prose also matter:

| Source span | Required treatment |
| --- | --- |
| 3–31, balanced-tree introduction and references | Explain the specific Okasaki-style algorithm and the source lineage. The papers and left-leaning variants are background references, not additional algorithms or entire-paper coverage requirements. The logarithmic performance claim needs section 8's model and hypotheses. |
| 33–40, warnings/imports/scope; 54–55, Arguments | Adapt imports to accepted Lean providers and use explicit source namespace/constructor arguments. Coq warning names, Z notation scope, and argument commands are not mathematical axioms or Lean APIs. |
| 44–46, abstract int keys | Replace source global assumptions with accepted Extract parameters and proved signed realizations. |
| 60–81, lookup/ins/balance explanation | Connect color erasure and exact recursive search; explain that rebalancing happens on unwind. Keep key replacement in the equality branch. |
| 120–140, traversal and left-leaning discussion | Preserve the accumulator traversal. Treat the alternative algorithm and case-count commentary as context; do not silently replace the source with a left-leaning implementation. |
| 145–223, nonempty warmup and automation | Prove ins nonempty and the stated insert consequence. Preserve the method of splitting only relevant Boolean/color/tree matches and closing constructor contradictions. The first Abort is an abandoned proof of a true claim. |
| 229–250, invariant adaptation | Preserve all-subtree decoded ordering, color irrelevance, and the difference from source Nat keys. |
| 257–421, BST proof development | Retain all three abandoned attempts as explanatory mappings and the completed result. Show why local case splitting needs the all-subtree implication/transitivity lemmas; do not reproduce incidental Coq goal counts as Lean obligations. |
| 480–596, equational specification and summary | Provide the actual three table equations, invariant preservation, and shared observation client. Their premises matter; the Redblack update equations are not all-raw laws. |
| 598–603, enumeration reuse | Prove the erasure/all-accumulator bridges and instantiate the relevant complete accepted enumeration contract in section 4. Avoid a second copied proof library. |
| 610–640, local/global invariants and efficiency | Separate no-red-red adjacency, equal black-height paths, root-color convention, minimum-depth theorem, size/logarithm theorem, and operation costs. Retain the possibility of a red root in RB. Qualify the literal `2 log N` expression at N=0/1. |
| 665–677, temporary invariant | Nonempty and only root-level red-red relaxation; include the exact library-predicate bridge. |
| 681–721, automated simultaneous induction | Keep both theorem components and remove the admitted tactic/proof. Ordinary Lean automation may differ while every resulting proof remains kernel checked. |
| 723–757, blackening and insertion | Distinguish parent-index weakening from represented root recoloring and its possible new black height. |
| 761–787, advanced proof hints | Define max/min depth, retain arbitrary parent color, and prove helpful upper/lower black-height path lemmas before the exact bound. |
| 795–823, extraction and quoted commands/timings | Reuse accepted Extract's runnable paths, keep empty/insert/lookup/elements exported, and perform actual bounded Lean executions. The OCaml `#use`, `ocamlopt`, and executable commands motivate the direct/standalone adaptation; they are not commands to fabricate or require as Lean validation. |
| 825–836, comparative conclusions | Report measured random/consecutive observations with provenance and limits. Do not turn the historical relative speeds or the prediction of a faster execution mode into universal performance theorems. |

## 8. Height, exact structural work, and performance assumptions

### Minimum depth and logarithmic node-count bound

Use the standard observations, counting internal nodes on a root-to-E path:

```text
height E = mindepth E = size E = 0
height (N_c(l,p,r)) = 1 + max (height l) (height r)
mindepth (N_c(l,p,r)) = 1 + min (mindepth l) (mindepth r)
size (N_c(l,p,r)) = size l + size r + 1.
```

Height and size are existing depth/size observations under the constructor
adapter; also prove agreement with BinaryTree height/numNodes after color
erasure. Minimum depth is a small missing source observation, not a new tree
interface. From `RB t parent n`, establish `n ≤ mindepth t` and
`height t ≤ 2*n+1`; for a black root the stronger `height t ≤ 2*n` is available.
The former needs an actual minimum-path induction. The latter can reuse
`Balanced.depth_le` after the parent/root bridge. Together they prove the
exact source `height t ≤ 2*mindepth t+1` for either parent color.

For the separate performance claim, reuse the precise pinned bounds:

```text
depthLB red n = n+1          depthUB red n = 2*n+1
depthLB black n = n          depthUB black n = 2*n
Balanced t root n → 2^(depthLB root n) ≤ size t + 1
Balanced t root n → height t ≤ 2*(size t + 1).log2.
```

The provider's depthLB docstring calls it an upper bound, but its actual
definition and `le_size` theorem provide the quantity used in the lower
size bound. Cite/use the theorem type, not that mistaken label. In particular,
`2^n ≤ size t+1` follows for any source RB tree; the red-root case has the
stronger n+1 exponent. Reuse `Balanced.depth_bound` once the exact adapters
are established. BST is unnecessary for shape bounds; it is needed for the
map interpretation and unique-key meaning of internal-node count.

Use N+1 or explicit small-size cases. The literal source expression `2 log N`
is undefined at zero and cannot bound singleton depth at N=1. The exact
Nat-log inequality above covers both cases. A depth-versus-size result alone
does not replace the source minimum-depth theorem.

### Instrument the source recurrence

Reuse Measured for an explicit vector of counts, retaining comparisons,
visited internal nodes, balance calls, and syntactic node constructions
separately where used. Value erasure must identify the instrumented output
with the actual source operation on every raw input, before any bound is
claimed. A count of constructors is a chosen source model, not a measurement
of backend heap allocation, sharing, or garbage collection.

The following recurrences fix the required counting convention. Other
primitive costs may be added with explicit weights, but may not replace
these branch-sensitive counts silently.

| Count | Exact recurrence / bound to prove |
| --- | --- |
| Lookup internal-node visits L | E gives 0. A nonempty call adds 1; a recursive branch adds the selected child's L; equality adds no recursive visits. Thus `L ≤ height t`. |
| Lookup Boolean comparison calls Q | E gives 0. The left branch adds 1; the right branch adds 2; equality costs 2. Add the recursive selected-child Q where present. Thus `Q ≤ 2*height t`. |
| Ins internal-node visits and comparisons | The same descent recurrences over the original input tree; insertion at E has zero old-node visits/comparisons. Bounds are height and twice height. |
| Balance calls B during ins | E and the equality branch contribute 0; either recursive branch contributes the selected child's B plus 1. Thus `B ≤ height t`. Include balance on red roots, even though it performs no rotation. |
| Local balance pattern attempts | In the explicit ordered-case model, charge one root-color selection and one for each attempted full red-red pattern. The exact costs for red, left-left, left-right, right-left, right-right, and black fallback are respectively 1, 2, 3, 4, 5, 5. Thus at most 5 per balance call. Prove the selected-branch equations in source priority order. |
| Syntactic node constructions A | Source balance constructs 3 nodes in each of the four rotating cases, 1 in the red or black fallback case. Source ins at E or equality constructs 1; on recursion it adds the selected child's A to that selected balance cost. Hence `A(ins) ≤ 3*height t+1`. |
| Final root blackening | Source ins is always nonempty, so insert adds one root-node construction in that syntactic model, plus its constant root inspection. Thus `A(insert) ≤ 3*height t+2`. This is separate from balance calls and Boolean comparisons. |
| Accumulator enumeration | With one charge for each invocation, `C(E)=1`, `C(node)=1+C(l)+C(r)`, so `C(t)=2*size t+1`. With one cons charge per visited node, exactly size t new list cons operations occur. The existing accumulator is not traversed or copied. No ordering/balance premise is needed. |

Full-pattern recognition is a bounded-depth primitive in that first model.
If refining it to datatype observations, each attempted red-red pattern
examines at most two node constructors and two color constructors. Prove
the corresponding bound of at most 17 such observations per balance call,
including the initial root color, for the explicit sequential-attempt model.
A matcher that shares failed subtests has its own observation recurrence;
neither count is automatically the compiler's generated match cost. This
distinction gives a precise fixed bound without hiding balancing work.

Instrument the nested enumeration call consistently with the chosen Lean
evaluation model; it computes the right-side accumulator before passing it
to the left call. Numerical visit counts do not establish constant stack
space. The source term being accumulator-based does not eliminate its nested
recursive call, and no unconditional constant-stack/physical-sharing claim
is part of this plan.

From these recurrences obtain a concrete affine-in-height work bound,
including terminal calls and balance/root work under the stated primitive
weights. Combine it with RB's height bound to get a bound in
`1 + (N+1).log2` for lookup/insert on balanced input. Semantic correctness
additionally uses BST. On an insertion history from empty, preserve both
invariants at each step and apply the per-state bound to the actual current
size; repeated keys replace values and need not increase N.

If a Boolean comparison is charged as one unit, say so. Unbounded Int
comparison is not automatically a constant-time machine operation. With a
workload comparison-cost bound Ccmp, retain that factor; a bit-cost model
needs a key-bit-length parameter as well as N. A fixed finite signed width
also bounds the possible number of distinct keys. An asymptotic family must
state its size domain and uniform primitive assumptions rather than invoke
arbitrarily large finite-word maps without a representation condition.

For a suitable Nat-indexed family with a proved explicit inequality, use
`Resources.isBigO_of_nat_bound` on the real casts and the stated Nat-log
function. A conventional O(log N) wording is then a qualified interpretation
for large N, not a replacement for the formal small-size statement. The
source's remark about the absence of a built-in Coq execution-cost model
does not prohibit proving a separately defined operation-count semantics.
Such a model still does not verify Lean's compiler/runtime or native timings.

## 9. Runnable comparison and benchmark fidelity

Reuse the accepted Extract driver and its source-shaped and controlled
workload variants; extend the realization parameter to this exact balanced
tree implementation. Do not create an independent benchmark algorithm with
similar names. The driver must exercise empty/insert/lookup/elements through
the proved signed-key adapters and both direct and standalone compiled paths
that Extract actually established.

The pinned ML program constructs the tree **before** calling `Sys.time`.
Its timed loop includes n queries and fresh calls to `f`; for random runs
those calls generate new random keys. The printed insertion-and-lookup label
is therefore inaccurate, and the returned hit count is discarded. Consecutive
keys are `0,1,…,n−1` in both phases; this makes the ordinary BST a right chain.
Random query keys are not guaranteed to have been inserted, so the expected
hit count is not generally n. Repeated insertions also reduce distinct size.

Required evidence for the new realization and comparison:

1. Run an actual bounded source-shaped scenario with accurately named
   build/query/whole-run phases. Preserve random generation inside the
   timed query phase when claiming fidelity to that source shape. A supplied
   seed/generator must make the sequence reproducible; equality to the OCaml
   generator's bitstream is not assumed.
2. Reuse identical stored insertion and query lists, carrier/range, values,
   defaults, and validation rules for the controlled ordinary/red-black
   comparison. Record their digests or equivalent reproducibility evidence.
   Pre-generated query-only timing and RNG-in-loop timing are separate
   experiments, with distinct labels and measured regions.
3. Validate query results and the consumed/reportable hit count against an
   independent finite-map/reference model. Validate enumeration and its
   distinct-key count on bounded correctness workloads. A lookup result equal
   to a default is not sufficient evidence of absent binding.
4. Record actual current tree size, height, and the appropriate proved
   invariants in mathematical checks or separately identified executable
   checks, without including validation/setup work in a supposedly query-only
   interval. Connect the observed difference on consecutive keys to the
   verified height distinction; do not infer an exact time ratio from it.
5. Retain exact candidate/command/toolchain/dependency identities, execution
   mode, host information where available, clock/unit, seed, workload sizes,
   repetitions/warmup choices, ranges/conversions, checked results, exit
   status, raw times, and logs. Process CPU time and monotonic elapsed time
   are different observations and must be labeled accordingly.
6. The source scenarios are random 1,000,000, random 20,000, and consecutive
   20,000 keys. Preserve their named configurations, but use bounded smoke
   scenarios and explicit resource limits for routine validation. Record any
   attempted timeout/stack limit or deferred large run honestly; a smaller
   completed run cannot be reported as a larger one. A bounded executed
   Redblack/ordinary-tree comparison is still required.
7. Keep the published OCaml bytecode/native numbers as historical source
   observations. Their claims of similar random performance, faster
   consecutive performance, and similar random/consecutive Redblack times
   are not all-workload guarantees. Report the actual Lean measurements and
   mode distinctions; do not assert that one execution path must be faster.

The driver uses the accepted signed realization and checked conversion
ranges. Positive-only timing workloads do not test signed ordering, so retain
the negative/extreme-key correctness cases from Extract. IO/randomness and
timing remain ordinary execution evidence, not axioms in pure theorem proofs.

## 10. Connected cases and independent statement checks

Cases must use the public operations and their theorems, exercise the exact
adapter boundaries, and have independently stated expected outcomes. They
are obligations for the implementation phase; none has been run here.

| Case | What it must establish |
| --- | --- |
| Empty/default and singleton | Arbitrary caller default on E; ins creates a red singleton; insert creates a black singleton; elements is the one written pair. This detects the library-insert mismatch. |
| Four isolated rotations | Ordered three-key fixtures for left-left, left-right, right-left, and right-right yield the precise middle-root/black-children tree. Check lookup, inorder equality, BST, and the applicable balance state through the actual theorem interfaces. |
| Red branch and black fallback | A red root returns its children unchanged even if they contain a red-red pattern; a black root with no matching pattern is rebuilt black. Verify their different local costs. |
| Right-case overlap on an ordered raw tree | Use root key 0, empty left, and red right child 2 with red singleton children 1 and 3. Source balance promotes 1; library balance2 promotes 2. Both are BST-shaped orderings, but the input violates RB. Prove the root/constructor difference, not a BEq result. |
| Left-case and cross-side priority | A red left child 1 with red children 0 and 2 below root 3 takes left-left first. Also retain a case where both sides offer a rotation: source still selects the left case. The source branch equations, not invariant assumptions, decide these raw results. |
| Why the Redblack same-key law needs a validity premise | With Int keys and distinct payloads, take a black root 2, left red root 5 whose left child is red singleton 4, and empty right. Inserting key 3 recurses right, then the pre-existing left-left pattern promotes 5; lookup 3 then goes left to 4 and misses. Prove the exact default-versus-written-value result and failure of BST, using source equations. |
| Shape/order independence | An ordered overlap fixture violates RB. Conversely a black root 0 with red left singleton 0 and empty right satisfies the shape invariant at black height 1 but violates strict BST. Neither invariant may silently replace the other. |
| Duplicate and distinct writes | Replacement changes the latest value without increasing distinct-key count; a separate write preserves another query under BST. Consume the shared table observation/update theorem and compare the ordinary and balanced realizations. |
| Presence versus default | Inserting a value equal to the caller default still adds a binding. Optional-map/enumeration observations distinguish this from E even when total lookup agrees. |
| Parent/root blackening | RB parent-index weakening leaves the tree/n unchanged. Blackening a red singleton changes black height 0→1; blackening E leaves 0. Exercise the existential theorem rather than a false fixed-height version. |
| Both ins_RB components | A red-root input under black parent exercises the NearlyRB conclusion; a black-root/empty input under red parent exercises the proper RB conclusion. Include nonempty witnesses and a proof that E is not NearlyRB. |
| Height/minimum-depth endpoints | E, red singleton, black singleton, and mixed red/black valid paths meet the exact min/max recurrences and source inequality. Check the N+1 logarithmic bound at N=0/1. |
| Signed keys | Reuse the accepted Int/BitVec signed/Int64 comparisons for negative, zero, positive, and bounded extreme values. Default unsigned BitVec comparison must not satisfy the selected source-facing test accidentally. |
| Traversal with a nonempty accumulator | Exact prefix/inorder plus the untouched suffix on raw and valid trees; count visits/calls/cons separately and preserve the accepted all-accumulator contract. |
| Work branches | A left search performs one comparison at a visited node; right/equality performs two. Rotations charge three syntactic node constructions; fallback charges one; final blackening is charged separately. |
| Executed workloads | Source-shaped and controlled random/consecutive runs consume verified operations, validate expected bindings, retain actual results, and use identical stored workloads for the direct algorithm comparison. |

Statement review must inspect actual elaborated types and their connected
uses: raw versus BST-only scope, order versus shape hypotheses, key inequality
orientation, parent versus root color, changed black height, nonempty
NearlyRB, original-key versus decoded equality, and exact source branch
priority. Success of a large proof script alone is not sufficient evidence.

## 11. Implementation order, remaining gaps, and acceptance gate

Only after #1011 is accepted:

1. Record the accepted baseline and reread the relevant actual predecessor
   public API types. Confirm the chosen raw carrier/import boundary, source
   comparison adapter, and signed realization. Reconcile this plan's proposed
   names without changing the source equations or weakening coverage.
2. Add the exact colored source operations, constructor/erasure observations,
   and meaningful connected cases. Reuse existing All/foldr/setBlack/shape
   observations. Follow the required example-driven design and statement
   review before optimizing proof scripts or runtime code.
3. Establish predicate transport and source ordering/lookup proofs, then the
   two-part shape proof and final blackening theorem. Preserve each theorem's
   weaker hypotheses rather than bundling BST and RB into every lemma.
4. Instantiate the accepted table laws and complete the enumeration/model
   bridges. Connect them to an accepted ordinary-table client and insertion
   history; do not leave the new results as isolated theorem stubs.
5. Complete the advanced minimum-depth proof, exact size/log bridge, and
   actual measured recurrences/qualified cost bounds. Integrate the runnable
   driver extension and retain actual bounded comparative evidence.
6. Map all 45 records, 13 exercises, six inventoried commands, and substantive
   prose obligations to actual declarations/evidence in the local coverage
   state. Aborts, tactics, and grading markers receive their explicit
   dispositions; source admissions must all be discharged.
7. Run the repository's required focused checks and the exact-candidate full
   Nix/direnv guard, audit regression and managed proof audit, both independent
   review axes, and final verification immediately before acceptance. Include
   the real integration roots/examples and meaningful statement/counterexample
   checks. Do not weaken the gate or invoke compilers during this planning task.
8. Root records local acceptance and creates/exposes/uploads the durability
   checkpoint, including source mappings, local tracking, review evidence,
   runnable artifacts, benchmark provenance/results, and exact Git identities.
   Then and only then may Trie implementation start. Planning for later
   chapters can continue without claiming this gate passed.

Known remaining work is substantive: exact source balance/ins definitions and
proofs, parent/root and NearlyRB bridges, original-key observation transport,
minimum-depth lower bound, source-specific resource instrumentation, and
actual executable comparison. Pinned providers supply useful ingredients;
none of these adapters or chapter claims was compiled/proved by this plan.
This preparation does not modify a source inventory, tracker, checkout,
configuration, dependency, cache, GitHub state, or another agent's file.

## 12. Exact inspected identities

Paths are relative to the workspace. Hashes identify the inspected bytes;
they do not assert that every listed provider was compiled or newly accepted.
Future accepted predecessor APIs must be recorded at their actual candidate
identity. The four predecessor specifications and the shared table file here
remain planning/staging evidence at this writing.

| File | SHA-256 |
| --- | --- |
| `reference/vfa/vfa/Redblack.v` | `f44255ba3d0235f6efa401b72f2fcf9a9551a7ebc065912202d6f33494891ce2` |
| `reference/vfa/vfa/Extract.v` | `c132273a13fafe176573469e664b9cbe8dd3366ec00e2f9a3ab8ab1d42a2e15d` |
| `reference/vfa/vfa/test_searchtree.ml` | `109e94b84632608b05e2c00081e98b2050a05dd9c5180241aa70486e7620e279` |
| `work-state/source/Redblack.inventory.json` | `c801f47c6922fca2dd72b29f3a59c1f650461bc5bb834ed70cbd8f9389e58c34` |
| `work-state/source/TREE-INVARIANT-REUSE.md` | `b7078b4a213b2a37035fa25531245749eeed411ff767aa8956a71678efe614db` |
| `work-state/source/COMPUTATIONAL-ASSUMPTIONS.md` | `eb4e8eb1cc4d04f6fe536e87622c4943d6af160b555e7ae4266979484f3eca30` |
| `work-state/source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` | `5d26488e0127a072c61c3db0323deececfd428023d71cf51b4db6b4055e5e03f` |
| `work-state/specs/1008-Maps.md` | `ec2664992b15240b54452ace437d12055ac1b0cc08e9b319b43e6bb211023f99` |
| `work-state/specs/1009-SearchTree.md` | `7bd10a9e771d38364bc806d28b38e6cca8f042a7701e3b852fe331d4cd0819e3` |
| `work-state/specs/1010-ADT.md` | `f53d2e54b8d587e27e486f5a08fb1746cc8e2ee16810d0c28c9e44c8e3bfa3e8` |
| `work-state/specs/1011-Extract.md` | `eccc61e739b5a3ccc0e496ad13828a93b76ec925f3bd80047b799c833a9846ff` |
| `work-state/staging/table-specs/TableObservations.lean` | `0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57` |
| `conaled/.lake/packages/batteries/Batteries/Recycling/RBTree/Basic.lean` | `6305fa5a1780d4eea77e7dfe6d6b961800a9ae4597a3be5d86715261acd6e204` |
| `conaled/.lake/packages/batteries/Batteries/Recycling/RBTree/Lemmas.lean` | `ef2600b1b212c8db551d83e67d8ca1baa70dc9c178cd06750f7a748f0970e9fa` |
| `conaled/.lake/packages/batteries/Batteries/Recycling/RBTree/WF.lean` | `c7aa820c815b3a1101c575ab2bbbcf5df59414c0630dfcf2546d180040468f54` |
| `conaled/.lake/packages/batteries/Batteries/Recycling/RBTree/Depth.lean` | `c91a2e0531038fba0b21adc911786c4daa22ef6334499f81ef5844643d8d8bd2` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Tree/Basic.lean` | `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d` |
| `conaled/.lake/packages/mathlib/Mathlib/Logic/Function/Basic.lean` | `ff4855cf0c959870c20a4ade8c2d0025f24a5088218e4bd715346332597cd64d` |
| `conaled/Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `conaled/Applications/Resources/Growth.lean` | `5e252788c2365d3f9140288a1d51f2ef38270798419af40df8505590a7d20dcc` |
| `conaled/AGENTS.md` | `5d017d009307c72a7616d7afe0bee9fb5a7105fe2f6f4e1da3fdccf070d4b4fe` |
| `work-state/REQUIREMENTS.md` | `85fbb013efa28c2aa1827dfaaab9cca5c3498f1da51b446972aa67dd690a7f84` |

Read-only planning reconciliation confirmed the 45 source IDs exactly once
in the record map, all 13 exercise names/ranges, all six inventoried commands,
and all 22 provider/source digests. That finite check certifies the plan's
bookkeeping, not mathematical or chapter completion.
