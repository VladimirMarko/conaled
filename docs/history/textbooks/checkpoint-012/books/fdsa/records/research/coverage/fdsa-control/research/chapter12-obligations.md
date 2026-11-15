# Chapter 12: Tries — source obligations, representations and reuse

Research date: 2026-11-02. Local ticket: `FDSA-012`.

**State: queued; source preparation only.** This note adds no Lean declaration,
runs no build, changes no ticket/acceptance state, and certifies no theorem.
Chapter 1 remains the active sequential chapter. Every item below needs its
checked implementation or reuse witness, statement review, applicable
validation and the project's independent reviews before chapter acceptance.

## Provenance and coverage boundary

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 12, printed pp. 149–160 (PDF pages 155–166), *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026. Official PDF: <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. The current official URL is not an immutable edition URL. |
| Isabelle revision | <https://github.com/isabelle-prover/mirror-isabelle> at `f86f290225eebcc52c1ae7dba2e098f405f51c21`, the shared inspection pin. It postdates the pinned book; correspondence was checked rather than assumed. |
| Function-valued tries | `src/HOL/Data_Structures/Trie_Fun.thy`; 2,294 bytes; SHA-256 `d616127603a542764837a02f232c422250b17dfc73bb75b5d63926df9165f1e9`. Direct PDF link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Trie_Fun.html>. Full file inspected. |
| Binary and Patricia tries | `src/HOL/Data_Structures/Tries_Binary.thy`; 11,874 bytes; SHA-256 `0456b6f86c039ae123c4670c89d07b6ac2d311c81513b1f891b6253efe0972b4`. Direct PDF link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Tries_Binary.html>. Full file inspected. |
| Ternary tries | `src/HOL/Data_Structures/Trie_Ternary.thy`; 4,460 bytes; SHA-256 `efef3e03eb35b6f604cbd16de87faf683f239ea9f57dc97bc89b9fc1c033e15f`. Direct PDF link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Trie_Ternary.html>. Full file inspected, including the explicitly required lookup-child size lemma. |
| Shared map/set sources | `Set_Specs.thy`, SHA-256 `601f6ff60e58de9d0c608b3b40ddf9105f9eb9fbeb7caabfeb9efc038d0d99d0`; `Tree_Map.thy`, SHA-256 `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43`; Chapter 6 inventory owns their exact interfaces. Both paths are under `src/HOL/Data_Structures/`. |
| Isabelle license | BSD-3-Clause; pinned `ISABELLE-COPYRIGHT` SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Retain relevant attribution/notices for translated code. |
| Reuse baseline | conaled `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Inspected library files carry Apache-2.0 notices. |

Pinned raw source URLs are
<https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/>
plus the source path. Reading copies and the extracted chapter text are under
`book-source/`. This original reconstruction and provenance, not the manuscript,
are the deliverable. A scoped scan found no `sorry`, `oops`, `axiomatization`
or `admit` in the three chapter theories; no Isabelle build or independent proof
audit was run.

Scope includes all four representations, their algorithms and refinement laws,
the binary pruning invariant, Patricia compression invariant, the unnumbered
invariant counterexample on p. 155, Exercises 12.1–12.4, and **all four
exercise families repeated for Patricia tries by §12.3.2**. The latter is a
single sentence, not four separately numbered exercises, but still creates
real obligations. The inspected theories contain none of those complete search
and exercise developments. Extra source `delete0` is a useful contrast but is
not an additional independently required book implementation. Historical names,
pronunciation and citations in the chapter notes are provenance, not new Lean
theorems.

## Conventions and architectural findings

Strings are `List α`; a trie represents a **set of strings**, not a set of
individual symbols and not a set of parse witnesses. Write `S(t)` for that
language, `E`/`N b l r` for binary empty/node, and `EP`/`P ps b l r` for a
Patricia node with stored prefix `ps`. `V` and `VP` denote the respective
pruning invariants. False selects the left child and true the right. An
acceptance flag describes the string ending at that node; at a Patricia node
that means **after consuming its stored prefix**.

`fdsa-control/DECISIONS.md` governs partiality, source correction and cost
separation. These trie membership functions are total Boolean recognizers;
missing transitions return false. They do not require a default alphabet
symbol or a global `Inhabited α`. Generic functional-map updates and generic
symbol comparisons need an explicit equality capability; the function-valued
carrier and lookup do not need an order or finite alphabet. The ternary
realization uses a lawful linear order, as its map implementation does.

| Existing interface | Exact reuse and boundary |
|---|---|
| Mathlib `BinaryTree Bool` | Exact binary-trie carrier, after adjusting constructor order and unpacking the pair of children. Reuse the Chapter 4 tree foundations. The pruning predicate and source operations remain to be connected. |
| Mathlib `BinaryTree (List Bool × Bool)` | Exact Patricia carrier. The label is `(storedPrefix,accepting)`; there is no need for another recursive binary-tree datatype merely to copy the source's constructor name. |
| Mathlib `BinaryTree.get` | With Chapter 11's bit-list/positive-index bridge, binary membership is a lookup returning `some true`. This is a useful observation bridge. Braun `update1` is **not** trie insertion: at an empty leaf it creates only one node, while trie insertion builds the entire remaining key path. |
| `Function.update`, `update_self`, `update_of_ne`, `update_apply` in `Mathlib/Logic/Function/Basic.lean` | Exact functional transition-map updates with `[DecidableEq α]`. No finite-support or ordering assumption is required by the abstract model. |
| Core `List.isPrefixOf?` | Returns the unconsumed suffix if one list prefixes another. It can implement the Patricia prefix test after a value bridge to the source's length/take/equality/drop expression. It is a different traversal, so do not reuse source counts by extensional equality. |
| Batteries `List.takeWhile₂` and `takeWhile₂TR` | Lawful-equality specialization finds two equal common prefixes. It does not return the remaining tails. A source `lcp` bridge must supply those tails and maximality; a separate `drop` implementation changes traversal cost. `takeWhile₂_eq_takeWhile₂TR` certifies only the two library versions' value equality. |
| Batteries `List.all₂`, `List.all₂_eq_true` | Exact length-sensitive wildcard matcher for relation `none↦true`, `some a↦(a=b)`. Unequal lengths return false. Use `DecidableEq` or lawful `BEq` to connect Boolean and propositional equality. |
| Mathlib `List.Forall₂.length_eq`, `.get`, `forall₂_iff_get`, `forall₂_iff_zip` | Declarative wildcard specification and same-length indexed reasoning. The zipped characterization has a length conjunct; dropping it accepts truncated matches incorrectly. |
| Mathlib `hammingDist` in `InformationTheory/Hamming.lean` | Standard distance on finite indexed functions, assumptions `[Fintype ι] [∀ i, DecidableEq (β i)]`. Equal-length lists can be viewed on `Fin n`; connect the exercise's recursion to it. It does not choose a totalization for unequal list lengths. Reusable results include self, symmetry, triangle, zero-iff-equality and the bound by coordinate count. |
| conaled `Applications/Languages/Machines.lean` | `LanguageDerivatives.Machine`, `.run`, `.Correct`, `.run_correct`, finite-depth `Trie`, `.lookup`, `.unfold`, `.lookup_unfold`, and snapshot squares provide a language-observation integration route. The depth-indexed trie has total transitions for every symbol and depth exhaustion returns `none`; it is not the book's unbounded sparse function-valued carrier. |
| conaled `Applications/Languages/WitnessTrie.lean` | Proof-relevant bounded observations carry `Decision (P w)` for type-valued languages. Their union/intersection retain sum/product witnesses. Those are different semantics from this chapter's Boolean set tries, per ADR 0004; reuse composition patterns, not the carrier by name. |
| Core `Lean.Trie` / `Lean.PrefixTreeNode` | Useful implementation references only. `Lean.Trie` uses String/UTF-8 keys and leaf, unary and byte-array branching forms. `PrefixTreeNode` nests `Std.TreeMap.Raw`; its `WellFormed` is generated by construction. Their inspected operations are `partial`, and do not supply these pruning/compression/refinement proofs. `findLongestPrefix?` searches stored keys and is not the two-list `lcp`. |

The reuse assessment was independently inspected by subagent `trie_reuse`,
without code changes or builds. No existing complete wildcard or Hamming trie
enumerator was found in the conaled/Mathlib/Batteries slices inspected here.
This is a scoped finding, not an exhaustive assertion about all external work.

## 12.1 Function-valued tries: pp. 149–151, Figure 12.1

| ID | Source obligation | Assumptions, reuse and remaining work |
|---|---|---|
| C12-001 | Abstract constructor `F b m`, with `b : Bool` and `m : α → Option (FTrie α)`. There is no empty constructor; an empty language is represented by a rejecting node with no transitions. | The recursive occurrence in a function **result** is positive. The carrier is not a coinductive unrestricted machine and is not a depth-indexed observation tree. Exact Lean elaboration still needs validation. |
| C12-002 | `emptyF=F false (fun _ => none)`. | No alphabet inhabitant or equality instance needed. Include the empty alphabet case. |
| C12-003 | `isinF(F b m,[])=b`; for `a::xs`, missing `m a` gives false, present child recurses on `xs`. | Recursion on key length works independently of a global finite height. Map lookup is function application. |
| C12-004 | Insertion of `[]` sets the root flag true and retains the transition function. | Preserve transitions, including empty-language children. |
| C12-005 | Insertion of `a::xs`: choose present child or `emptyF`, insert `xs` there, then function-update key `a` to `some newChild`, retaining the original flag. | Use exact `Function.update`; only the chosen key changes. This operation needs decidable equality for execution, not a linear order. |
| C12-006 | Deletion of `[]` sets the root flag false and retains transitions. | Does not normalize or shrink the node. |
| C12-007 | Deletion of `a::xs`: missing transition leaves `m` unchanged; present transition is updated to `some(deleteF xs child)`, even if its language becomes empty. | Retaining a dead child is deliberate. Replacing it by `none` changes the strong structural refinement used later for ternary tries. |
| C12-008 | Source abstraction `S_F(t)={xs ∣ isinF t xs=true}`, invariant identically true. | Preserve this source view and its independence from finiteness/order. A separate declarative acceptance relation is a useful independent observation, C12-013. |
| C12-009 | `S_F(emptyF)=∅` and membership agrees with `isinF`. | Source `isin_set_trie` and Set interpretation. Membership is definitionally true for the chosen abstraction, while the update laws below are substantive. |
| C12-010 | `S_F(insertF xs t)=S_F t∪{xs}` for every trie. | `Trie_Fun.set_trie_insert`, lines 46–48; proof compares all query strings, not just the inserted key. |
| C12-011 | `S_F(deleteF xs t)=S_F t\{xs}` for every trie. | `set_trie_delete`, lines 50–52; unrelated strings retain membership. |
| C12-012 | All seven Chapter 6 Set laws hold, with three validity laws trivial under `True`. | Source interpretation `S`, lines 54–65. This ADT does not require represented sets to be finite. |
| C12-013 | Independent declarative language: empty word belongs iff the flag is true; `a::xs` belongs iff some child at transition `a` accepts `xs`. | Relate this acceptance relation or prefix-union denotation to the executable recognizer. Reuse the project's proposition-valued `Language α = Set (List α)` layer; do not conflate Boolean recognition with type-valued parse witnesses. |
| C12-014 | Example p. 150: deleting `[a]` from a root with sole accepting child at `a` leaves a root with a sole **rejecting** child, both with no further transitions; language is empty. | Keep an executable equality and semantic empty-language result. It witnesses noncanonical structure and the difference between `some emptyF` and `none`. |
| C12-015 | The function-valued model imposes no finite-support or global Nat-height invariant. | With infinite alphabet it can represent infinite languages and arbitrarily deep children. Preserve this full source domain; see the explicit counterexamples below. Finitely supported maps may be a separate refinement, not a silent replacement. |
| C12-016 | Introductory access bound: membership follows at most one transition per key symbol, under constant-time transition access. | In a one-per-recursive-call model, `T_isin≤length key+1`, with equality when all transitions until the end exist. Actual nested function-update closures need their own cost analysis. The book states the constant-transition assumption; do not omit it. |

## 12.2 Binary tries: pp. 151–153, Figure 12.2

| ID | Source obligation | Assumptions, reuse and remaining work |
|---|---|---|
| C12-017 | Binary carrier `E` or `N b l r`, over alphabet Bool. | Use `BinaryTree Bool`; representation has no alphabet/key values stored at nodes, only an acceptance flag. |
| C12-018 | `sel2 false(l,r)=l`, `sel2 true(l,r)=r`. `mod2 f false(l,r)=(f l,r)`, `mod2 f true(l,r)=(l,f r)`. | Reuse pair projections/updates or prove these two-branch equations. The selected callback is applied exactly once. |
| C12-019 | `empty=E`; `isin E ks=false`; on a node, empty key returns its flag, nonempty key chooses the child by the first bit and recurses on the tail. | Exact finite-path lookup. Relate to `BinaryTree.get` after the bit-path bridge, not to inorder or numeric-rank lookup. |
| C12-020 | Insertion at empty key: on `E`, create accepting singleton; on `N _ l r`, set root flag true and retain children. | Distinguish empty trie from the trie containing only the empty string. |
| C12-021 | Insertion of `k::ks`: on `E`, create rejecting root with recursively inserted suffix in child `k`; on a node retain its flag and insert into selected existing child. | Creates the entire remaining path at an empty tree. The opposite child remains `E` in the first case. |
| C12-022 | Smart constructor `node b l r` returns `E` exactly when `b=false` and both children are `E`; otherwise it returns `N b l r`. | Constant-size constructor-pattern tests suffice; no traversal to test semantic emptiness. |
| C12-023 | `delete ks E=E`; on a node with empty key use `node false l r`; with `k::ks`, delete in child `k` and use `node` with the old flag. | Source shrinks while unwinding. Do not substitute nonshrinking `delete0` or full-tree normalization without a correspondence. |
| C12-024 | `V E=True`; `V(N b l r) ↔ V l ∧ V r ∧ ((l=E ∧ r=E) → b=true)`. | Every terminal node must accept; rejecting unary nodes are allowed in an ordinary binary trie. |
| C12-025 | `isin(insert xs t,ys) = (xs=ys ∨ isin(t,ys))` for arbitrary `t,xs,ys`. | `isin_insert`; invariant is **not** a premise. Boolean equality needs the usual propositional/Bool bridge. |
| C12-026 | `isin(delete xs t,ys) = (xs≠ys ∧ isin(t,ys))`, again without `V t`. | `isin_delete`; pruning changes representation but not other memberships even on invalid raw trees. |
| C12-027 | Equations (12.1)–(12.2): `S(insert xs t)=S t∪{xs}` and `S(delete xs t)=S t\{xs}`; empty and recognizer equations also hold. | `set_trie_insert/delete`, `set_trie_empty/isin`. Use language/set equality, preserving the empty word. |
| C12-028 | `V t → V(insert xs t)`. Source support: insertion never returns `E`, for any raw input. | `invar_insert`, `insert_Lf`. The inserted path's accepting endpoint prevents an invalid new terminal. |
| C12-029 | `V t → V(delete xs t)`. | `invar_delete`. Supporting smart-constructor law: valid children give a valid `node` for either flag. |
| C12-030 | The binary implementation satisfies all seven Set laws with invariant `V`. | Source interpretation `S`, lines 120–124. Do not add `V` to the already stronger semantic update theorems. |
| C12-031 | Pruning expresses the claimed space property: on a valid tree every stored node lies on a prefix of an accepted string; no wholly dead subtree remains. | Prove this finite-tree consequence. It explains canonicality and structural minimality among binary-tree representations of the same set; physical bytes/allocation sharing are separate models. |
| C12-032 | Binary membership and each single-key insert/delete have `O(length key+1)` recursive-call overhead with constant-time child access and smart constructors. | The introductory conditional access claim applies directly here. Lookup/delete may stop early; insertion consumes the entire key and reaches an endpoint. Source contains no generated quantitative time theory, so any exact measured constants remain to be supplied and reviewed. |

## 12.2.2 Exercises: pp. 153–154

These algorithms are not supplied in the inspected `Tries_Binary.thy`. The
recurrences below give concrete, reviewable solution scopes, rather than a
definition whose answer is obtained by filtering an unspecified set oracle.

| ID | Exercise and exact obligation | Concrete solution and required proof |
|---|---|---|
| C12-033 | Exercise 12.1: `V t₁ ∧ V t₂ → (S t₁=S t₂ ↔ t₁=t₂)`. | Prove canonicality on valid trees. Use the valid-empty-language iff `E` fact, root membership of `[]`, and false/true residual languages. Neither equal node counts nor lookup at a finite sample suffices. |
| C12-034 | Exercise 12.2 union: define executable `union`, prove `S(union t₁ t₂)=S t₁∪S t₂` for all inputs and preservation under `V t₁,V t₂`. | Base `E` returns the other tree; two nodes combine flags by OR and recursively union corresponding children. If using `node` instead of raw `N`, state that choice. Exact representation equality/cost is not forced by the exercise, but its semantic and validity laws are. |
| C12-035 | Exercise 12.2 intersection: prove `S(inter t₁ t₂)=S t₁∩S t₂` and **unconditional** `V(inter t₁ t₂)`. | Empty argument gives `E`; two nodes combine flags by AND, recurse on corresponding children, and rebuild using `node`. Unconditional validity follows because every recursive output is normalized. Adding input validity would miss the explicitly stronger exercise. |
| C12-036 | Exercise 12.3 generic `matches : List (Option α) → List α → Bool`: `none` matches any symbol, `some a` matches only `a`; the whole lengths must agree. | Reuse Batteries `List.all₂`. The declarative relation is `List.Forall₂ (fun p a => p=none ∨ p=some a)`. Empty/empty is true; exactly one empty is false. |
| C12-037 | Define binary `isins t ps`: leaf gives `[]`; at a node with empty pattern return `[[]]` iff accepting; `some k::ps` searches only child `k` and prepends `k`; `none::ps` searches both children and prefixes their respective bits. | A concrete order is false-child results followed by true-child results. Use actual recursive searches and map/append; source specifies a set of returned strings, not a particular order. |
| C12-038 | Exercise 12.3 correctness: `xs∈set(isins t ps) ↔ isin t xs ∧ matches ps xs`. | No validity premise. Prove soundness and completeness, including empty pattern and too-short/too-long candidate strings. A duplicate-free result is a useful strengthening but not a substitute for the iff. |
| C12-039 | Exercise 12.4 `Hdist : List α → List α → Nat`, agreeing on equal-length lists with the number of mismatching positions. | Use decidable symbol equality. A concrete totalization may count mismatches of zipped positions and ignore any remaining suffix; state this explicitly because Hamming distance is only specified for equal lengths here. Do not claim a metric on all lists from this totalization. |
| C12-040 | Connect the equal-length distance to Mathlib `hammingDist` on the shared `Fin n` coordinate domain. | Prove zero/cons mismatch recurrences and the `Fin` bridge; existing metric facts then apply on the equal-length domain. This avoids a second unrelated mathematical distance theory. |
| C12-041 | Define `near t xs d`: leaf gives `[]`; at a node and empty key return `[[]]` iff accepting; for `k::xs`, search matching child at budget `d`, and opposite child only when `d>0`, at budget `d-1`; prepend the selected bit. | Natural subtraction alone is unsafe: at `d=0`, `d-1=0` would admit a mismatch unless the branch is guarded. The empty-key case must not return longer accepted strings. |
| C12-042 | Exercise 12.4 correctness: `ys∈set(near t xs d) ↔ length xs=length ys ∧ isin t ys ∧ Hdist xs ys≤d`. | No pruning invariant premise. Preserve the length conjunct even if the chosen distance totalization returns 0 for unequal-length pairs. |
| C12-043 | Exercise boundaries and output behavior. | Include empty trie, stored empty word, empty pattern/key, impossible literal, all wildcards, zero budget, and budget at least key length. Enumerators may visit both subtrees and return many strings; no single-path linear-time claim follows from ordinary trie lookup. |

## 12.3 Patricia values and algorithms: pp. 154–156, Figure 12.3

| ID | Source obligation | Assumptions, reuse and remaining work |
|---|---|---|
| C12-044 | Patricia carrier `EP` or `P ps b l r`; `ps : List Bool` records the compressed path before the acceptance flag and branch bit. `emptyP=EP`. | Reuse `BinaryTree (List Bool × Bool)`. Prefix may be empty; no condition forbids it at a branching/accepting node. |
| C12-045 | `isinP EP ks=false`; at `P ps b l r`, let `m=length ps`. If `ps≠take m ks`, reject; otherwise inspect `drop m ks`: empty returns `b`, nonempty chooses the indicated child and recurses on its tail. | Preserve the stored-prefix boundary. Standard `List.isPrefixOf?` can be an explicitly bridged optimization, not an unannounced recurrence replacement. |
| C12-046 | `lcp [] ys=([],[],ys)`; `lcp xs []=([],xs,[])`; on two heads, mismatch returns `([],xs,ys)`, match recurses on tails and prepends the shared head to the first component. | Generic alphabet operation with equality, source lines 147–152. It returns the **actual residual tails**, not only a length or prefix. Both-empty overlap is consistent. |
| C12-047 | If `lcp xs ys=(ps,xs',ys')`, then `xs=ps++xs'`, `ys=ps++ys'`, and nonempty residuals have different heads. | Source `lcp_if`. In the Boolean divergence case, unequal heads are complementary; this justifies choosing both new children by only one head. |
| C12-048 | The common prefix is maximal: every common prefix of `xs,ys` is a prefix of `ps`; the residual decomposition is unique. | Mathematical meaning of “longest common prefix,” derivable from C12-047. An equal-set-of-symbols fact or arbitrary common prefix is insufficient. |
| C12-049 | `insertP ks EP=P ks true EP EP`. | Store the whole remaining suffix at one accepting Patricia node. This differs from binary insertion's full path construction. |
| C12-050 | Inserting into `P ps b l r`, equal strings case `lcp ks ps=(_,[],[])`: return `P ps true l r`. | Retain old stored prefix and children; set acceptance only. |
| C12-051 | Key proper prefix case `(qs,[],p::ps')`: make old remainder `t=P ps' b l r`; new node `P qs true` has `t` in branch `p` and `EP` in the other. | This creates an accepting unary node, which is allowed by `VP`. The consumed branch bit is removed from `ps'`. |
| C12-052 | Stored prefix proper prefix case `(_,k::ks',[])`: retain `ps,b` and insert `ks'` in child `k`. | The recursive call receives the residual **after** its branch bit. Preserve the other child. |
| C12-053 | Divergence case `(qs,k::ks',p::ps')`: form `old=P ps' b l r`, `new=P ks' true EP EP`; return rejecting `P qs false` with `new` in branch `k`, `old` in the opposite branch. | `k≠p` follows from `lcp_if`; it is not an extra assumed alphabet law. For Bool there are exactly two branches. |
| C12-054 | `nodeP ps true l r=P ps true l r`. For a false flag and two empty children, `nodeP` returns `EP`. | Accepting nodes never merge through their child, because doing so would lose a shorter stored key. |
| C12-055 | False flag with only right child `P qs c ll rr` becomes `P (ps++true::qs) c ll rr`; only left child uses `false`. With two nonempty children retain `P ps false l r`. | All five cases of the source smart constructor. Concatenation order is parent prefix, branch bit, child prefix. Child's flag and children replace the parent's. |
| C12-056 | `deleteP ks EP=EP`; at a node with equal key/prefix, use `nodeP ps false l r`. | Deleting the stored prefix clears acceptance and may remove or merge the resulting node. |
| C12-057 | When `lcp ks ps=(_,_,_::_)`, deletion returns the original Patricia node unchanged. | Covers both an earlier divergence and a query that ends before the stored prefix. No descent or normalization occurs in these cases. |
| C12-058 | When `lcp ks ps=(_,k::ks',[])`, recursively delete in child `k`, then rebuild with `nodeP ps b`. | Keeps the old flag while possibly compressing a now-unary rejecting node. |
| C12-059 | Termination of `insertP`/`deleteP` follows the selected strict subtree on recursive branches; `lcp` recurses on list tails. | The supplied source uses a `mod2_cong` congruence lemma for its function package. Lean may pattern-match the selected child directly; prove exact recurrence correspondence if changing presentation. |
| C12-060 | `VP EP=True`; `VP(P ps b l r) ↔ VP l ∧ VP r ∧ ((l=EP ∨ r=EP) → b=true)`. | The connective is **OR**, unlike ordinary binary invariant's AND. Thus a rejecting Patricia node must have two nonempty children. Prefix contents do not enter this invariant. |
| C12-061 | Example of compression: `P ps false (P qs b l r) EP` and `P (ps++false::qs) b l r` represent the same language. | Prove via the abstraction below or independent prefix denotation. Structural equality is not claimed before applying `nodeP`. |
| C12-062 | Unnumbered p. 155 exercise: exhibit `¬VP t` but `V(absP t)`, disproving equality of the two invariants. | Witness `t=P [] false (P [] true EP EP) EP`. Its expansion is a valid unary binary path accepting `[false]`; its Patricia root is nonaccepting and nonbranching. Retain the actual checked counterexample. |

## 12.3.1 Stepwise refinement: pp. 155, 157

| ID | Source obligation | Exact theorem strength and support |
|---|---|---|
| C12-063 | `prefix [] t=t`; `prefix(k::ks)t` creates a rejecting binary node whose child `k` is `prefix ks t` and other child is `E`. | Source `prefix_trie`. This expansion **does not** normalize dead paths; `prefix [k] E≠E` even though its language is empty. |
| C12-064 | `absP EP=E`; `absP(P ps b l r)=prefix ps (N b (absP l) (absP r))`. | Exact structural abstraction, not just equality of represented languages. |
| C12-065 | `isin(prefix ps t,ks) ↔ ps=take(length ps)ks ∧ isin(t,drop(length ps)ks)`. | `isin_prefix_trie`; all prefixes/trees, no pruning hypothesis. If the query is too short the first equality is false. |
| C12-066 | `isinP t ks=isin(absP t,ks)` for all Patricia trees. | `abs_trieP_isinP`; validity is not needed. Empty abstraction is also exact. |
| C12-067 | `prefix ks (N true E E)=insert ks E`. | `prefix_trie_Lfs`; bridges a Patricia leaf containing a whole suffix to the expanded binary path. |
| C12-068 | `insert ps (prefix ps (N b l r))=prefix ps (N true l r)`. | `insert_prefix_trie_same`; accepting the prefix retains all extensions. |
| C12-069 | `insert (ks++ks') (prefix ks t)=prefix ks (insert ks' t)`. | `insert_append`; no invariant assumption. |
| C12-070 | `prefix(ps++qs)t=prefix ps (prefix qs t)`. | `prefix_trie_append`; crucial for divergent-prefix insertion and compression. |
| C12-071 | Equation (12.3): `absP(insertP ks t)=insert ks (absP t)` for all raw trees. | `abs_trieP_insertP`, lines 243–247. This is **tree equality**, stronger than set correctness; do not weaken it to merely equal languages. |
| C12-072 | `VP t → VP(insertP ks t)`. Support: `insertP ks t≠EP` without any validity premise. | `invarP_insertP`, `insertP_LfP`. Both key-prefix and divergence cases create shapes satisfying the precise OR condition. |
| C12-073 | `prefix xs t=E ↔ xs=[] ∧ t=E`; `absP t=E ↔ t=EP`. | `prefix_trie_Lf`, `abs_trieP_Lf`; these are structural emptiness, not semantic-empty-language equivalences. |
| C12-074 | `delete xs (prefix xs (N b l r)) = if l=E ∧ r=E then E else prefix xs (N false l r)`. | `delete_prefix_trie`; no input validity. Deletion shrinks an entire dead path in the both-empty branch. |
| C12-075 | `delete(xs++ys)(prefix xs t) = if delete ys t=E then E else prefix xs(delete ys t)`. | `delete_append_prefix_trie`. The condition prevents retaining an expanded dead prefix. |
| C12-076 | If at least one Patricia child is nonempty, `absP(nodeP ps b l r)=prefix ps (N b (absP l) (absP r))`. Also `nodeP ps true l r=P ps true l r`, and `nodeP ps false EP EP=EP`. | `abs_trieP_nodeP`, `nodeP_True`, `nodeP_LfP2`. Do not drop the nonempty-child condition in the first equality; it fails for rejecting two-empty-child nodes. |
| C12-077 | Equation (12.4): `absP(deleteP ks t)=delete ks(absP t)` for every raw Patricia tree. | Source `delete_abs_trieP` presents the symmetric equality. Preserve the strong structural result, including invalid raw trees. |
| C12-078 | `VP l ∧ VP r → VP(nodeP ps b l r)`; `VP t → VP(deleteP ks t)`. | `invarP_nodeP`, `invarP_deleteP`; the source factors out the smart-constructor lemma rather than inlining an unstable automation proof. |
| C12-079 | Set abstraction is the composition `S_P=S∘absP`; empty, membership, insert and delete laws follow; `VP` supplies all three validity laws. | Source interpretation `SP`, lines 328–345. Keep all seven Set obligations. Value laws are unconditional and follow from structural refinement, not from adding invariant assumptions. |
| C12-080 | Useful integration support: `VP t → V(absP t)`; the converse is false by C12-062. | Needed if composing refinement squares between validity-subtype carriers. Prove the direction using nonempty expansion and prefix preservation; equality of the two predicates is not available. |

## 12.3.2 Repeated Patricia exercises: p. 158

These are four exercise families, with the same mathematical strength as
Exercises 12.1–12.4. Prefix-sensitive implementations below are proposed concrete
solutions; the book gives no source recurrence or cost theorem for them. Their
details and termination must be checked before adoption. Converting to binary
tries and back could be a separately documented executable solution, but it
would not establish direct compressed-tree execution or its resource claims.

| ID | Repeated exercise obligation | Concrete solution and required proof |
|---|---|---|
| C12-081 | Patricia version of Exercise 12.1: `VP t₁ ∧ VP t₂ → (S_P t₁=S_P t₂ ↔ t₁=t₂)`. | Need uniqueness of the fully compressed representation, or injectivity of `absP` on valid Patricia trees plus binary canonicality. `absP` is not injective on all raw trees. |
| C12-082 | Supporting normalization option: convert a binary tree by recursively converting its children and rebuilding with `nodeP []`. | Prove unconditional Patricia validity and language preservation; on a valid binary tree its expansion is exactly the input. A second round trip on `VP` can establish C12-081. These are explicit auxiliary algorithms/proofs, not assumed inverse laws. |
| C12-083 | Patricia union must have unconditional set-union correctness and preserve `VP` from two valid inputs. | A direct algorithm splits both root prefixes by `lcp`. Equal prefixes OR flags and recursively join matching children; a shorter first prefix recurses into its selected child against the second residual-root node; the longer-first case is symmetric; divergent prefixes make a rejecting binary branch over both residual roots. Empty argument returns the other. |
| C12-084 | Verify all Patricia union cases, including proper-prefix acceptance, residual leading-bit removal and branching orientation. | Preserve old flags and off-path children. A termination measure is the sum of Patricia node counts: recursive branches replace at least one root by its strict child; shortening the other prefix does not increase its node count. Rebuilding with `nodeP` is an explicit normalization choice. |
| C12-085 | Patricia intersection must have unconditional set-intersection correctness and **unconditional** `VP` of the result. | Empty or divergent-prefix cases return `EP`. Equal prefixes AND flags and combine recursive intersections using `nodeP`. In a proper-prefix case, only the selected child can contribute; recursively intersect it with the other residual-root node and prepend the consumed prefix/branch to the normalized result. |
| C12-086 | Supporting prepend for direct intersection: `prependP ps EP=EP`; `prependP ps(P qs b l r)=P(ps++qs)b l r`. | Prove prefix-language behavior and preservation of `VP` from the result argument. Unlike ordinary `prefix`, it discards a prefix of an empty Patricia result. This distinction is necessary for unconditional canonicality. |
| C12-087 | Patricia wildcard search `isinsP : Patricia → List (Option Bool) → List (List Bool)`. | Check the stored prefix against an equal-length initial pattern segment; failure/too-short pattern gives `[]`. After consuming it, empty remaining pattern yields the stored prefix iff accepting; a literal/wildcard branch uses the same one/two-child recursion as binary search, prefixing every result with stored prefix and branch bit. |
| C12-088 | Wildcard correctness: `xs∈set(isinsP t ps) ↔ isinP t xs ∧ matches ps xs`, without `VP`. | Reuse generic `matches`, prove the prefix-consumption split law, and handle empty stored prefixes. Do not enumerate only accepting nodes at compressed boundaries while ignoring the actual matched full word. |
| C12-089 | Patricia Hamming search `nearP : Patricia → List Bool → Nat → List (List Bool)`. | If query is shorter than stored prefix, reject. Compute mismatches against that prefix; reject when they exceed budget; otherwise deduct them and recurse on remaining query exactly as for binary `near`, paying an additional mismatch for the opposite branch only when residual budget is positive. Prefix each returned suffix with the stored path and branch bit. |
| C12-090 | Hamming correctness: `ys∈set(nearP t xs d) ↔ length xs=length ys ∧ isinP t ys ∧ Hdist xs ys≤d`, without `VP`. | Use equal-length distance additivity over a common decomposition, not a metric claim on unequal lists. Preserve guards before Nat subtraction and accept only when the whole query is consumed. |
| C12-091 | Repeated-exercise boundaries include a stored empty key, empty compressed prefix, query ending inside a stored prefix, divergence within a compressed prefix, and an accepting unary node with longer descendants. | These distinguish compressed search from merely reusing ordinary child lookup. Check canonical outputs for invalid inputs in intersection, as required by the unconditional invariant statement. |

## 12.4 Ternary tries: pp. 158–160, Figure 12.4

| ID | Source obligation | Assumptions, reuse and remaining work |
|---|---|---|
| C12-092 | Carrier `T b m`, with `m : BinaryTree (α × TTrie α)` representing a character-to-subtrie map; acceptance flag is stored at the outer trie node. | This is a nested recursive type, not simply `BinaryTree Bool`. Source uses the unbalanced Chapter 6 map. A different map carrier needs an explicit refinement/termination bridge and retains its own operational recurrence. |
| C12-093 | Lookup-child decrease: `Map.lookup m a=some child → size child<size(T b m)`. | `Trie_Ternary.lookup_size`, lines 39–42, is unconditional in map validity. Its measure counts nested child-trie contents as well as map nodes; plain map node count cannot bound an arbitrarily large stored child. Needed for structural abstraction and invariant recursion. |
| C12-094 | `empty3=T false emptyMap`; `isin3(T b m,[])=b`; for `a::xs`, failed map lookup gives false, successful child lookup recurses on `xs`. | Exact source behavior. Key recursion alone establishes termination for this recognizer. Map lookup requires the chosen lawful comparison capability. |
| C12-095 | Insertion of `[]` sets flag true; insertion of `a::xs` gets present child or `empty3`, inserts suffix, and uses Map `update a newChild m`, retaining root flag. | It uses both map lookup and map update at the current node; an efficient fused alternative would need an explicit correspondence and distinct cost model. |
| C12-096 | Deletion of `[]` sets flag false; on `a::xs`, missing map entry leaves `m`, present entry is updated to the recursively deleted child. | **No Map delete/erase operation occurs.** The representation intentionally retains empty subtries, matching the unshrunk function-trie semantics. |
| C12-097 | `V3(T b m) ↔ Map.invar m ∧ ∀a child, lookup m a=some child → V3 child`. | Source `invar3` uses observable lookup children, not an unqualified all-raw-entry predicate. Under a valid map an entry-based formulation can be equivalent, but prove that bridge. |
| C12-098 | `abs3(T b m)=F b (fun a => Option.map abs3 (Map.lookup m a))`. | Exact structural abstraction into the function-valued trie. `Option.map none=none`, `Option.map(some child)=some(abs3 child)` are standard. Use C12-093 or equivalent well-founded support for recursive construction. |
| C12-099 | `abs3(empty3)=emptyF`; `isin3 t xs=isinF(abs3 t,xs)` **without** a `V3` premise. | `isin_abs3`; raw malformed BST lookup may describe a strange language, but both sides use that same lookup. The stronger theorem must not acquire an unnecessary invariant condition. |
| C12-100 | `V3 t → abs3(insert3 xs t)=insertF xs(abs3 t)`. | `abs3_insert3`; relies on valid map update/lookup laws and recursive child validity. This is equality in the function-trie carrier, not merely language equality. |
| C12-101 | `V3 t → abs3(delete3 xs t)=deleteF xs(abs3 t)`. | `abs3_delete3`. Shrinking by erasing semantically empty children would break this exact equality, even when it preserves represented sets. |
| C12-102 | `V3 t → V3(insert3 xs t)` and `V3 t → V3(delete3 xs t)`; `V3 empty3`. | `invar3_insert3`, `invar3_delete3`, empty-map validity. All reachable child maps must remain valid. |
| C12-103 | Composite abstraction `S3=S_F∘abs3` realizes all seven Set laws for keys `List α`. | Source interpretation `S2`, lines 94–111. The printed p. 160 phrase “α set” must be “(α list) set.” |
| C12-104 | The explanatory map-replacement claim: other correct search-tree map implementations can replace the unbalanced map. | Preserve lawful Map semantics and the structural child-decrease/positivity support needed for the nested representation. The source explicitly excludes `lookup_size` from the otherwise nearly verbatim proof transfer. An arbitrary extensional Map interface alone does not provide that termination theorem. |
| C12-105 | Ternary structural nonuniqueness is intentional. | Two valid map BST shapes with the same character-to-child mappings give the same string set but different ternary trees. Do not transfer binary/Patricia canonicality to this representation. Balance/order invariants of a chosen replacement map remain separate from trie pruning, which is absent here. |

## Connected observations, resource scope and recovery checks

| ID | Connected obligation | Required disposition |
|---|---|---|
| C12-106 | Present each Set implementation and the two refinement chains through reusable representation operations. | Use the project's proposition-valued language/set observation and `Squares` composition. Preserve the literal structural equations for `absP` and `abs3`; set equality alone does not prove them. |
| C12-107 | Machine view for the abstract trie, with an explicit rejecting sink for missing transitions. | Existing `Machine` can use state `Option FTrie`, nullable false at sink, and transition by the node's optional map. Prove `Machine.run` equals `isinF`; bounded snapshots then follow through existing theorems for every finite word. This does not assert a finite state space for arbitrary function-valued tries. |
| C12-108 | Exact input capabilities and failure observations. | Function insertion/deletion and generic `lcp`, `matches`, `Hdist` need equality; ternary maps need their lawful order. Binary/Patricia operations use Bool equality. No operation may acquire an arbitrary global alphabet inhabitant, finite alphabet, or total-child assumption merely to ease an implementation. |
| C12-109 | Source cost claims versus value optimizations. | The chapter gives no Patricia/ternary measured recurrences or bulk/search bounds. Attach any concrete count to actual operations and named primitives. `lcp`, `isPrefixOf?`, path expansion, prefix concatenation, map lookup/update and output construction have different work; retain these distinctions. |
| C12-110 | Corrected type and domain qualifications, and actual counterexample obligations. | Preserve the explicit source type correction and the raw/canonical boundary examples below. This original note and exploratory calculations are not Lean proofs or chapter acceptance. |

## Source defects and qualifications

### Wrong set element type on p. 160

The final correctness paragraph says the abstract and ternary tries implement
`α set`. Their keys and recognizers have type `List α`; the intended result is
`Set (List α)`. The three companion Set interpretations instantiate exactly
those string-key operations. This is a type-level editorial correction, not a
license to change the represented objects to individual characters.

### The unrestricted function-valued model is not necessarily finite

The introduction's finite-tree/finite-automaton intuition fits the concrete
binary, Patricia and finite nested-map representations. It must not silently
add a domain restriction to `F b (α → Option FTrie)` with invariant `True`.
Two concrete mathematical examples expose the distinction for alphabet Nat:

1. Let `leafAccept=F true (fun _ => none)` and let the root map **every** Nat
   symbol to `some leafAccept`, with root flag false. Its language is all
   singleton lists `[n]`, an infinite set. Replacing source `Set` by `Finset`
   would exclude a valid source value.
2. For each `n`, let `chain n` accept only the word of `n` zeros. Let a
   rejecting root map symbol `n` to `some(chain n)`. The resulting inductive
   function-valued tree has children with arbitrarily long finite accepting
   paths; there is no single Nat bound on the lengths of its accepted words.
   Its residuals after the first symbol are pairwise distinct singleton
   languages, so the tree's full language cannot be recognized by a finite
   deterministic state set even if an infinite alphabet is permitted.

The source datatype can contain these well-founded, infinitely branching
values; none uses a self-referential cycle. Finite keys still give terminating
lookup/update. Preserve their availability or give an explicit separately
named finite-support refinement. The existing conaled depth-indexed observation
tries remain useful snapshots, but are not an exact replacement.

### Canonicality, emptiness and compression boundaries

- Binary `E` and `N false E E` recognize the same empty language but are
  different trees. The second violates `V`. This is the smallest witness
  showing why Exercise 12.1 needs validity.
- Let `p=P [] false (P [] true EP EP) EP` and
  `q=P [false] true EP EP`. Then `p≠q` but `absP p=absP q`; only `q`
  satisfies `VP`. The expansion of `p` satisfies binary `V`, as requested
  by the unnumbered p. 155 exercise. Thus `VP↔V∘absP` and unrestricted
  injectivity of `absP` are both false; the forward invariant implication
  and valid-carrier injectivity are the appropriate statements.
- `prefix [false] E` is a nonempty binary node recognizing no strings.
  Hence structural-empty iff semantic-empty needs `V`; C12-073's structural
  equivalences are not interchangeable with a language test.
- Taking `ps=[]`, false flag and two empty children refutes an unconditional
  version of `absP(nodeP ps b l r)=prefix ps(N b(absP l)(absP r))`: left
  side is `E`, right side is `N false E E`. The companion supplies the
  nonempty-child premise and separate both-empty/accepting lemmas.
- Shrinking a ternary child after deleting its last accepted word would
  change a transition from `some emptyF` to `none` after `abs3`. Those are
  different function-trie values although they accept the same strings.
  Keep the actual unshrinking delete when proving the source's structural
  refinement; an optimized shrinking variant needs its own named theorem.

These are intended domain distinctions, not errors in the companion's stated
theorems. They should become small checked examples alongside the relevant
proofs rather than disappear into stronger assumptions without explanation.

## Execution and mathematical-scope cautions

1. **Patricia lookup is not automatically linear in query length under
   list-operation cost.** Its displayed code first computes the length of
   the whole stored prefix. For valid `P (replicate m false) true EP EP`
   queried by `[]`, it rejects after computing that length, costing linear
   work in `m` if list length is charged. The introductory lookup claim is
   conditional on constant-time transitions; it cannot be transferred
   unchanged to this multi-symbol transition. A lockstep prefix/suffix
   helper may improve behavior, but must retain a checked value bridge and
   its own execution recurrence.
2. **Unbalanced ternary maps do not have constant-time transitions.** A
   character transition pays the local map-search cost; insertion also pays
   map-update cost. A balanced map can bound these by local map size after
   its separate height/cost proof. Neither behavior follows from set
   semantics alone, and no new universal `O(length key)` claim is attributed
   to this source implementation.
3. **Wildcard and Hamming enumeration can branch and produce many words.**
   The single-path membership bound does not apply. Any future resource
   contract must include visited branching structure and output work.
   The exercise's set-membership equivalences alone impose no ordering or
   duplicate count; a concrete implementation can provide stronger
   duplicate-free/order laws if useful.
4. **Totalizing Hamming distance does not remove its equal-length domain.**
   For example a zipped mismatch count gives distance 0 between `[]` and
   `[false]`; this does not make those strings equal or satisfy the source
   search predicate, whose length conjunct rejects the mismatch. A
   same-length `Fin n` bridge uses the existing mathematical metric with
   all its standard laws.
5. **Structural measures for nested tries matter.** A map with one entry
   can store a child trie with thousands of nodes. `lookup_size` measures
   that nested payload, not only map shape. No partial definition,
   termination override or newly assumed recursion axiom is justified by
   the fact that core implementation tries use `partial` operations.
6. **A correct abstraction is not an executable substitute.** The source's
   equality `absP(insertP ks t)=insert ks(absP t)` does not mean `insertP`
   may be claimed as implemented merely by assigning a set-level answer.
   Preserve all prefix-splitting/compression branches. Likewise the source
   ternary algorithm must actually use the chosen map operations, and its
   stronger carrier-level refinement must be proved.

## Handoff

Use shared tree/list/function primitives and the existing set-language
observation layer. Keep the function-valued abstract carrier's full domain;
then prove binary operations and their independent language laws, pruning and
the four exercises. For Patricia tries retain the four `lcp` cases, every
smart-constructor branch, exact expansion equations and the invariant
counterexample, then complete all four repeated exercise families. Ternary
proofs should use Chapter 6's actual map laws together with the explicit
nested-child termination bridge. Finish connected representation examples,
correct the printed set type, and retain the counterexamples and cost
qualifications above. All 110 rows remain source obligations or identified
integration work; none is marked formally covered by this inventory.
