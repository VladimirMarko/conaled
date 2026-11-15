# Chapter 6 source obligations: Abstract Data Types

Status: **queued; source inventory only**. No Chapter 6 implementation or
acceptance is asserted. This is an original reconstruction checklist for the
pinned book, including both exercises and their operational requirements. Read
with `../DECISIONS.md` and the Chapter 5 source inventory. The abstract interfaces
and refinement mechanisms should be shared by domain, not duplicated merely to
follow chapter numbering.

## Pins and source provenance

- Book: July 27, 2026 version, Chapter 6 by Tobias Nipkow, printed pp. 77–83
  (PDF pp. 83–89); printed p.84 is blank. Official PDF:
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
  SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
  All section/page references below use printed numbering. Page 82 was also
  rendered and visually inspected to check the erroneous split-min reference.
- Isabelle companion at
  <https://github.com/isabelle-prover/mirror-isabelle/commit/f86f290225eebcc52c1ae7dba2e098f405f51c21>.
  The following exact files were read. License: BSD-3-Clause, repository
  `COPYRIGHT` SHA-256
  `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
  This pins the inspected companion, not an unverified PDF-build relationship.
- Source URL prefix:
  `https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`.
- The book's direct hyperlinks are to `Set_Specs`, `Map_Specs`, and `Tree_Map`.
  The imported `AList_Upd_Del` and `Sorted_Less` contain the actual association
  list algorithms and proof laws; inventorying just the three linked pages
  would miss that dependency. No exercise solution for the interval-list
  algorithms was found in the inspected `src/HOL/Data_Structures` directory.
- Reuse inspection: conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`,
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` / release v4.35.0.

| Source path | SHA-256 | Relevant content |
|---|---|---|
| `src/HOL/Data_Structures/Set_Specs.thy` | `601f6ff60e58de9d0c608b3b40ddf9105f9eb9fbeb7caabfeb9efc038d0d99d0` | `Set`, `Set_by_Ordered`, and a larger `Set2` extension |
| `src/HOL/Data_Structures/Map_Specs.thy` | `54e97e50dc6e44d4d5533b92a109b50e781520c99bd0c50637b42470493b3e5d` | `Map`, `Map_by_Ordered`, representation composition |
| `src/HOL/Data_Structures/Tree_Map.thy` | `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43` | Key-ordered tree lookup, update, deletion, and map refinement |
| `src/HOL/Data_Structures/AList_Upd_Del.thy` | `42f603405ff3fec058ba284c76183924139c42711ec66edaf623bd5b0a921f9a` | `sorted1`, `map_of`, ordered update, deletion, semantic and structural laws |
| `src/HOL/Data_Structures/Sorted_Less.thy` | `971199401fc20cd378ad3ca9c22c314bba146e44b5730dcc718a2b0f6f6a52d5` | Strict sortedness, shared with Chapter 5 |
| `src/HOL/Data_Structures/Tree_Set.thy` | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` | The generic `split_min` actually used by `Tree_Map` |
| `src/HOL/Data_Structures/Cmp.thy` | `5539b207634456f4c359dc12cabf720018cbc62c2c67b6d99ad0b7e5ac5993e6` | Lawful key comparator |

## Representation and reuse boundaries

The model-oriented specification has concrete carrier T, abstract model A,
abstraction `decode : T -> A`, and validity `I : T -> Prop`. Invariants and
abstraction maps are specification data; the operational interface is separate.
An invariant may have an executable Boolean checker with a reflection theorem,
but the general interface does not need a global decidability requirement.

Neither injectivity nor surjectivity of decode is part of this chapter's
contract. For example, finite BSTs realize finite maps while their abstract
model `α -> Option β` contains arbitrary partial functions. A valid
implementation need not represent every abstract value. Nor does identical
abstract observation imply identical concrete tree shape or operation history.

Reuse labels: **R** existing directly relevant infrastructure; **P** partial
match requiring a checked adapter; **G** gap; **X** shared chapter dependency.

| Inspected component | Reuse assessment |
|---|---|
| `Squares.lean`: `Squares.Rep`, `Square`, `compose`, `Rep.after`, `vertical`, products | R/P: total abstraction functions and composition already exist. An invariant-conditioned specification can use the subtype of valid concrete values; do not ask the total `commutes` law to hold on invalid raw values. |
| `SquareKit/Relations.lean`: `RelRep`, `RelSquare`, identity/composition/product, graph bridges | R/P: directly express the raw representation relation `I t ∧ decode t=a`, preserving validity and semantics in one relation without requiring decode on invalid values to simulate operations. The book's functional representation is a special case; arbitrary relational data should not be forced into a chosen decoder. |
| `SquareKit/RelationComposition.lean`: `compRel`, `existentialSquare`, `transportRelations` | R/P: compose two representation routes using an explicit intermediate witness and pointwise agreement of the middle operation. Needed when composing tree-to-list and list-to-model correctness; no parallel replacement composition theory is warranted. |
| `Applications/Sequences/AbstractFIFO.lean` | R/P as an established client pattern: operation-only `Ops`; separate proposition `Simulation`; trace execution, `run_preserves`, `client_eq`, `client_empty`, `comp`, and `representation_independent`. These are FIFO-specific declarations, not already a generic Set/Map interface, but show how to build actual representation-independent clients. |
| `Applications/Resources/FIFOContracts.lean` | R/P for separating behavior from instrumentation and accounting, and for a valid-state subtype realization. Costs must not be hidden inside the mathematical Set/Map contract. |
| Mathlib `AList` in `Mathlib/Data/List/AList.lean` | R/P for unique-key lookup/update/erase semantics with arbitrary payloads and decidable keys. It uses dependent `Sigma` entries. `AList.insert` prepends the new pair and erases the old occurrence, so it does **not** implement the source's ordered `upd_list` recurrence or preserve sorted entry order automatically. |
| Mathlib `Finmap` and raw list lookup | Candidate semantic adapters. `Finmap` is finite, while the book's abstract map carrier is the unrestricted function `α -> Option β`; do not replace the model by a finite quotient without an explicit embedding and stated observation. |
| Chapter 4/5 binary tree, strict key lists, set contract | X: share the existing/forthcoming domain foundation and lawful comparator; map values require neither an order nor decidable equality. |
| `Applications/Intervals/Arithmetic.lean`, `Applications/Timing/Intervals.lean` | Not the Exercise 6.1 representation. These are rational enclosure/timing abstractions, not ordered disjoint closed natural intervals representing finite sets. Reuse basic logical methods where helpful, not an incompatible carrier. |

The chapter's informal extension of decode/invariant by identity/True on
unrepresented types is best made **role-specific** in a typed operation
signature. A parameter whose Lean carrier happens to equal T does not thereby
become a represented state. Products of explicit representations or the
existing relational compiler interfaces can express the required argument roles.
No global type-equality case split or universal typeclass should guess those
roles. For higher-order client claims, use a checked client syntax/relational
interpretation or prove the concrete generic client; mere polymorphic notation
does not establish parametricity for arbitrary Lean programs.

## 6.1–6.3 General specification and the Set interface: pp. 77–79

| ID | Obligation / exact source scope | Reuse or gap |
|---|---|---|
| C06-001 | Separate the operational interface from its specification: an ADT is implemented by concrete operations satisfying declared laws, and client correctness can depend on those laws rather than concrete representation (p.77). | R/P: established `Ops`/`Simulation` pattern. Provide a checked reusable client/representation-independence theorem, not only a structure containing the desired conclusion. |
| C06-002 | Model-oriented setup: supply T, A, `decode : T -> A`, and invariant I; only valid concrete values must simulate their abstract meanings (pp.77–78). | R/P: validity relation or valid subtype; neither injectivity, surjectivity, canonical form, nor decidable invariant is required. |
| C06-003 | Uniform operation schema extends the represented-state observation to identity on ordinary parameters and extends validity to True there (p.79). | P: explicit typed roles/products; give the equivalence between this extension and the specialized Set laws. |
| C06-004 | For an n-argument operation, valid represented inputs imply validity of the represented output; ordinary outputs have the trivial True requirement (p.79, `f-inv`). | P/G. Preserve every represented input's hypothesis, including binary operations; do not retain only the first. |
| C06-005 | Under the same input-validity hypotheses, decoding the concrete result equals the corresponding abstract operation on decoded inputs (p.79, `f`). | R/P: commuting-square/relation law. Output identity applies to observations such as Bool or `Option β`. |
| C06-006 | Show that the invariant and simulation clauses together are equivalent to preserving the relation `I t ∧ decode t=a`, using equality relations on ordinary parameters (p.79's uniform schema). | R/P: a reusable bridge to `RelSquare`; no source claim requires a new all-purpose category architecture. |
| C06-007 | Include nullary operations: their input precondition is empty/True, so empty-state correctness and validity are unconditional (pp.78–79). | R/P: terminal/product treatment or direct zero-argument instance. |
| C06-008 | Include observations: for `isin`, the output invariant is trivial but the result must agree with abstract membership on valid states (p.79). | P. Distinguish Bool reflection from equality of propositions in Lean; the abstract model may use `decide` only with an appropriate decision or classical specification. |
| C06-009 | Compose implementation routes: tree-to-ordered-list and ordered-list-to-set give tree-to-set correctness while retaining the intermediate invariant and matching middle operation (p.79 plus Chapter 5, pp.66–67). | R/P/X: `existentialSquare` or valid-subtype `vertical`; combined validity must include the intermediate predicate unless already implied by a proved law. |
| C06-010 | Demonstrate the purpose of the ADT with a checked generic client/trace whose observations agree for any two lawful implementations initialized to corresponding valid states (p.77). | P/G. Instantiate at least two materially distinct representations, e.g. Chapter 5 BST and Exercise 6.1 interval lists for natural sets. Reuse existing generic interpretation machinery where it actually matches the client. |
| C06-011 | Figure 6.1: abstract set of `empty` is empty (p.78, label `empty`; source `Set.set_empty`). | X Chapter 5; state no invariant precondition. |
| C06-012 | Figure 6.1: `I empty` (label `empty-inv`; `invar_empty`). | X. |
| C06-013 | Figure 6.1: `I s -> decode(insert x s)=decode s ∪ {x}` (label `insert`; `set_insert`). | X. |
| C06-014 | Figure 6.1: `I s -> I(insert x s)` (label `insert-inv`; `invar_insert`). | X. |
| C06-015 | Figure 6.1: `I s -> decode(delete x s)=decode s \ {x}` (label `delete`; `set_delete`). | X. |
| C06-016 | Figure 6.1: `I s -> I(delete x s)` (label `delete-inv`; `invar_delete`). | X. |
| C06-017 | Figure 6.1: `I s -> (isin s x=true ↔ x∈decode s)` or an equivalent Bool-valued membership equality (label `isin`; `set_isin`). | X. Generic Set semantics does not require linear-order keys; executable concrete realizations expose only their needed capabilities. |
| C06-018 | A concrete implementation supplies all interface operations, abstraction, invariant, and proofs of every law, including validity (p.79). Connect the Chapter 5 implementations and interval-list exercise through this shared specification. | G/P/X. An uninstantiated interface is not the chapter's implementation content. |
| C06-019 | Keep abstraction/invariant specification functions outside executable interface requirements unless they are explicitly exposed (p.79). The map `lookup` exception later is intentional. | Architecture obligation: executable operations must remain executable; do not require `decode`/I to be runtime data simply because a proof uses them. No runtime-erasure claim is inferred without the corresponding compiler semantics. |

## Exercise 6.1: natural sets as interval lists, pp. 79–80

Carrier: `List (Nat × Nat)`; endpoints are inclusive. A suitable minimal
invariant is that every `(l,h)` satisfies `l<=h` and every earlier interval's
high endpoint is strictly below every later interval's low endpoint. For an
ordered list it suffices to express the adjacent strict separation and prove
the all-pairs consequence. This permits adjacent intervals such as `(0,0)`
followed by `(1,1)`. Maximal/coalesced runs are an optional stronger design,
not part of the printed requirement; if chosen, state and preserve it explicitly.

The binary difference has the unusual but explicit argument order
`del cutters targets`, representing **targets minus cutters**. The source
`Set2.diff` uses the usual first-minus-second order; any adapter must reverse
these arguments. `Set2` additionally requires intersection, which this
exercise does not ask for; do not assert an instance without that extra method.

| ID | Obligation / exact source scope | Reuse or gap |
|---|---|---|
| C06-020 | Define `set_of ivs = {n \| ∃(l,h)∈ivs, l<=n ∧ n<=h}`; derive empty/cons abstraction laws and represent the printed example `[(2,3),(5,5),(7,9)]` as `{2,3,5,7,8,9}` (p.79). | G/P: standard `Set.Icc` on naturals. No point enumeration is needed to define the semantic set. |
| C06-021 | Define and characterize the invariant: nonempty intervals, ascending order, no overlap (pp.79–80). Prove empty valid and the prefix/suffix/order facts needed for early termination. | G. Do not assume all intervals have positive width; singleton intervals are required. |
| C06-022 | Define `isin ivs n` with early termination: before the first current lower endpoint return false; inside a current interval return true; otherwise scan the tail. Prove membership correctness for valid input (p.80). | G. The exercise requests an executable observation, not a noncomputable membership oracle. |
| C06-023 | Define `add1 n ivs`, inserting a point or leaving the represented set unchanged if it is already present, while preserving validity (p.80). | G. With the minimal invariant, an absent point before the current interval can be inserted as a singleton without scanning the suffix; an explicitly chosen coalescing variant must handle adjacent neighbors correctly. |
| C06-024 | Define `del1 n ivs`, removing a point; handle absence, singleton removal, truncation at either endpoint, and splitting an interval when the point is strictly interior (p.80). | G. Natural predecessor is used only when the guards establish the intended nonempty residual; include n=0 and singleton `(0,0)`. |
| C06-025 | Prove **all seven** Set laws for `[]`, `add1`, `del1`, `isin`, `set_of`, I (p.80), not only the sample insertion equation. | G/X C06-011–017. Exercise 6.1 is a second concrete model-oriented implementation. |
| C06-026 | Define `add xs ys` by merging the two interval streams; under validity of both, `set_of(add xs ys)=set_of xs ∪ set_of ys` (p.80). | G. It must handle overlapping intervals from different inputs and retain ordering; repeated point insertion is explicitly disallowed. |
| C06-027 | Define `del xs ys`; under validity of both, `set_of(del xs ys)=set_of ys \ set_of xs` (p.80). | G. Delete intervals/segments using a two-stream procedure; splitting a target interval may produce multiple residual intervals. Do not swap the specified argument order. |
| C06-028 | Both valid inputs imply `I(add xs ys)` (p.80). | G. Abstraction equality alone cannot replace the ordering/non-overlap proof. |
| C06-029 | Both valid inputs imply `I(del xs ys)` (p.80). | G. Preserve bounds on all emitted/residual intervals, including natural-number endpoints. |
| C06-030 | Every exercise function terminates and stops once later intervals cannot affect its result (p.80). Give explicit recursive branches / return-on-ordered-bound identities; prove the chosen cursor/residual measure decreases for binary operations. | G. A fuel argument that merely truncates a scan is insufficient without adequacy. Avoid traversing unaffected suffixes just to rebuild them. |
| C06-031 | `add` takes time linear in `len xs+len ys` (p.80). Instrument its actual two-stream recursion and prove fixed constants C,D with `Tadd xs ys <= C*(len xs+len ys)+D` on valid inputs. | G. The constants are not specified by the book; choose and prove them for the implementation. Complexity is in interval count, independent of interval widths. |
| C06-032 | `del` also has a linear bound in `len xs+len ys`, including residual-target revisits and emitted pieces (p.80). | G. Charge actual control flow; a split is not permission to repeatedly rescan the same prefix. A cursor advancement/accounting argument should cover all recursive cases. |
| C06-033 | Show the binary implementations act on interval endpoints rather than iterating `add1`/`del1` over all represented points, as explicitly required (p.80). Useful supporting targets are output-length bounds `len(add xs ys)<=len xs+len ys` and `len(del xs ys)<=len xs+len ys` for the chosen stream implementation. | G/support. These length bounds should be proved if used in the time/allocation argument; they are not substitutes for the actual runtime recurrence. |

### Exercise 6.1 cost and edge-case discipline

The chapter does not print exact cost recurrences or constants. The faithful
reading is the Chapter 1 abstract call-count model with primitive endpoint
comparisons and arithmetic charged consistently as constant operations. Record
the chosen count and prove a linear bound for it. This does not claim bit-time
linear in the number of intervals for arbitrarily large natural endpoints.

A one-interval value `[(0,N)]` represents N+1 numbers. Enumerating those numbers
would defeat the length-based complexity requirement, even though the final set
semantics could be correct. The difference implementation can retain a shortened
current target while advancing the cutting stream; termination and time proofs
must account for that residual state explicitly. Each emitted piece should be
charged to an input interval boundary, rather than to its cardinality.

Useful future checked boundary cases include empty input on each side,
singleton/zero endpoints, one interval containing many of the other stream's
intervals, disjoint streams ordered either way, equal intervals, touching but
non-overlapping natural intervals, deletion of only an endpoint, and deletion
of a strict interior point. For argument orientation, cutters `[(1,1)]` and
targets `[(1,2)]` must leave `{2}`; the opposite set difference is empty.

## 6.4 Partial maps and the Map interface: pp. 80–81

The model is `α -> Option β`: absence is `none`, and any `some b` is present.
This supports arbitrary value types β, including empty types. Values need no
linear order, default value, or decidable equality. Map operations' abstract
laws use point updates, with ordinary equality of functions proved by
extensionality. Generic semantic laws need no linear order on α; the concrete
ordered representations do. Where a Boolean/executable equality decision is
needed, make it local to that realization or comparator.

| ID | Obligation / exact source scope | Reuse or gap |
|---|---|---|
| C06-034 | Define the source partial-map model as total functions `α -> Option β` and the notation `m[a↦b]` as point update at a to `some b` (p.80). | R/P: standard `Option`/`Function.update`; no need for a fresh partial-function type or default β. |
| C06-035 | Formalize the introductory view of sets as Boolean-valued maps with its Lean assumptions exposed (p.80). | P: a set with decidable membership has a characteristic `α -> Bool`; an arbitrary classical set can have a noncomputable characteristic function. If using the chapter's `Option Bool` Map carrier, choose and prove an embedding, e.g. `some true` for members and `none` otherwise. It is not an equivalence to all `Option Bool` maps without restricting the allowed false/absent encodings. |
| C06-036 | Figure 6.2 operations: `empty : M`, `update : α -> β -> M -> M`, `delete : α -> M -> M`, `lookup : M -> α -> Option β`; invariant I is separate (p.81). | G/P. The abstraction is deliberately `lookup`, which is also an executable public operation. |
| C06-037 | `lookup empty = fun _ => none` (Figure 6.2, `empty`; source `Map.map_empty`). | G/P. Function equality, no validity precondition. |
| C06-038 | `I empty` (Figure 6.2, `empty-inv`). | G/P. |
| C06-039 | `I m -> lookup(update a b m) = Function.update (lookup m) a (some b)` (Figure 6.2, `update`; `map_update`). | G/P. Includes both the updated key and every unaffected key. |
| C06-040 | `I m -> I(update a b m)` (Figure 6.2, `update-inv`). | G/P. |
| C06-041 | `I m -> lookup(delete a m) = Function.update (lookup m) a none` (Figure 6.2, `delete`; `map_delete`). | G/P. Deleting an absent key leaves the **observation** unchanged, not necessarily the concrete representation. |
| C06-042 | `I m -> I(delete a m)` (Figure 6.2, `delete-inv`). | G/P. |
| C06-043 | Account for `lookup`'s own simulation clause: because it is the abstraction, observing lookup is reflexive rather than an additional independent assumption (pp.81,83). | P: formally relate the specialized six-law interface to the generic operation schema, including its trivial output invariant. |

## 6.5 Ordered association lists and tree maps: pp. 81–83

Here node labels `(key,value)` are both **semantic data**. They are not the
`(logical label, cached annotation)` pairs whose second component Chapter 4/5's
augmented-tree inorder erases. Use full pair inorder and compare only keys.
The invariant is `sorted1 ps := S(map fst ps)`, with strict S from Chapter 5.
Sorting full pairs by a product order is neither the same invariant nor an
acceptable replacement for key uniqueness.

| ID | Obligation / exact source scope | Reuse or gap |
|---|---|---|
| C06-044 | Concrete carrier `BinaryTree (α×β)` with full pair inorder; validity is strict sortedness of its key list (pp.81–82). Prove/bridge the corresponding key-BST property as needed. | P/X: Chapter 4 carrier. Only α needs linear order; arbitrary β must remain supported. |
| C06-045 | `lookup E x=none`; at `N(l,(a,b),r)`, compare x with a and search left/right or return `some b` (p.81). | G/P: source `Tree_Map.lookup`; compare keys only. |
| C06-046 | `update x y E=N(E,(x,y),E)`; LT/GT rebuild the chosen child; EQ replaces the **whole pair** by `(x,y)` (p.82). | G. It is an overwrite at an existing key, unlike set insertion which keeps the old logical value. |
| C06-047 | Reuse the generic Chapter 5 `Tree_Set.split_min` on full pair labels, with its nonempty-domain and full-pair inorder-head law (p.82's intended dependency). | P/X. The printed reference to §5.6.4 is erroneous; do not use the interval-cache smart constructor or erase the payload. |
| C06-048 | Tree deletion by key: LT/GT recur; EQ returns left if right empty, else replaces the label with the right subtree's full successor `(key,value)` pair and residual tree (p.82). | G/P. Prove every split-min call nonempty; replacement must retain the successor's value. |
| C06-049 | Define `sorted1 ps=S(map fst ps)` and derive no duplicate keys, prefix/suffix facts, and that the empty list satisfies it (p.82). | P: standard `Pairwise`/map facts; do not impose ordering on values. |
| C06-050 | `upd_list x y []=[(x,y)]`; at `(a,b)::ps`, prepend on `x<a`, replace head on equality, otherwise recurse after the old pair (p.82). | G/P. Existing `AList.insert` is semantically compatible but has a different entry order/recurrence; bridge semantics separately. |
| C06-051 | Association-list `del_list x` removes the first pair whose **key** equals x and otherwise scans the tail (p.82). | P. This is not list erasure of an entire `(key,value)` pair. Definition only needs decidable key equality, even though its ordered-map use has stronger hypotheses. |
| C06-052 | `map_of []=fun _=>none`; `map_of((a,b)::ps)` overrides the tail's mapping at a with `some b` (p.83). Thus the first occurrence wins for duplicate keys. | P: standard list lookup with checked first-match semantics. This is the unrestricted-list observation even on invalid duplicate-key inputs. |
| C06-053 | `map_of(upd_list x y ps) = Function.update (map_of ps) x (some y)` **without** a `sorted1 ps` premise (p.83; `map_of_ins_list`). | G/P. Retain this weaker assumption boundary: the theorem remains true on unsorted and duplicate-key lists. |
| C06-054 | `sorted1 ps -> map_of(del_list x ps) = Function.update (map_of ps) x none` (p.83; `map_of_del_list`). | P/G. Key uniqueness is essential for the stated absence result; first-match deletion alone does not remove later duplicate bindings. |
| C06-055 | `sorted1 ps -> sorted1(upd_list x y ps)` (p.83; `sorted_upd_list`). | G/P. |
| C06-056 | `sorted1 ps -> sorted1(del_list x ps)` (p.83; `sorted_del_list`). | P/G. |
| C06-057 | Association-list lookup correctness is reflexive because the operation and abstraction are both `map_of`; combine C06-052–056 to instantiate the six Map laws for ordered association lists (p.83). | G/P. Include empty correctness and validity, not only the four displayed nonempty-operation laws. |
| C06-058 | Supporting source framework: `map_of(ps++qs) x` is the first non-none result of `map_of ps x` then `map_of qs x` (`map_of_append`). | P. This is left-biased, not right-biased. |
| C06-059 | Supporting absence bounds: `S(x::map fst ps)` or `S(map fst ps++[x])` implies `map_of ps x=none`; under the corresponding endpoint bounds, queries below/at excluded boundaries are absent (`map_of_None`, `map_of_None2`, `map_of_sorted_Cons`, `map_of_sorted_snoc`). | P. Record exact strict/nonstrict premises: `map_of_sorted_Cons` uses query `<a`; `map_of_sorted_snoc` uses `a<=query`. |
| C06-060 | Ordered update distribution: under `sorted1(ps++[(a,b)])`, updating `ps++(a,b)::qs` acts on ps if `x<a`, else on `(a,b)::qs` (`upd_list_sorted` and its two branch corollaries). | P/G. No sortedness hypothesis on qs is needed in this update law. |
| C06-061 | Ordered deletion distribution: under `sorted1(ps++(a,b)::qs)`, deleting x acts on ps when `x<a`, else the suffix; plus absence identity and the repeated-pivot corollaries used by tree proofs (`del_list_idem`, `del_list_sorted1`–`5`). | P/G. Prefer shared parameterized composition laws where they cover the finite source corollaries exactly; avoid mechanically duplicating proof syntax. |
| C06-062 | `sorted1(inorder t) -> inorder(update a b t)=upd_list a b (inorder t)` (p.83; `Tree_Map.inorder_update`). | G/P. Full semantic pair traversal. |
| C06-063 | `sorted1(inorder t) -> inorder(delete x t)=del_list x (inorder t)` (p.83; `Tree_Map.inorder_delete`). | G/P. Use the full-pair split-min law, not augmented-tree erasure. |
| C06-064 | `sorted1(inorder t) -> lookup t x=map_of(inorder t) x` (p.83; `lookup_map_of`). | G/P. The equality is pointwise and can be extended to equality of whole lookup functions. |
| C06-065 | Tree empty is E; full inorder is []; empty lookup is always none; key invariant holds (pp.81–83, the omitted trivial empty implementation). | R/P/X. Explicit law witnesses are still needed in the instantiated contract. |
| C06-066 | Compose tree-to-association-list and association-list-to-model laws to prove all six Map axioms for the concrete tree operations (p.83; interpretation `M` and `Map_by_Ordered` sublocale `Map`). | G/P/X: reuse general refinement composition; preserve both operational map arrows and the intermediate key-sorted invariant. |
| C06-067 | General ordered-map refinement admits an extra representation invariant J: assume empty inorder, lookup/update/delete list refinements under `J t ∧ sorted1(inorder t)`, and preservation of J. Then the Map invariant is their conjunction (`Map_by_Ordered`). | G/P: this is what later balanced map realizations need. Unbalanced `Tree_Map` instantiates J=True. The auxiliary invariant must not be forgotten when applying the composition theorem. |

The imported association-list theory also contains additional endpoint update
and deletion laws specifically documented for splay trees:
`upd_list_Cons`, `upd_list_snoc`, `del_list_notin_Cons`, and
`del_list_sorted_app`. Their declarations are preserved by this source pin;
they can be implemented with the later consuming chapter if not needed here.
They are not extra printed Chapter 6 exercise requirements. This scheduling
distinction does not waive the later consumer's exact assumptions.

## Exercise 6.2: equivalent update interfaces, p. 83

The function argument to modify is arbitrary `Option β -> Option β`: it can
insert at an absent key, overwrite a present value, delete a present value, or
leave the observation unchanged. No restriction such as `f none=none` appears
in the exercise. Empty and lookup remain in the replacement interface.

| ID | Obligation / exact source scope | Reuse or gap |
|---|---|---|
| C06-068 | Define the modified Map interface with `modify : α -> (Option β -> Option β) -> M -> M`. Under I m, require `lookup(modify a f m)=Function.update (lookup m) a (f(lookup m a))` and `I(modify a f m)`; retain the empty laws (p.83). | G/P. This is a semantic interface change, with no ordering or value-equality assumption. |
| C06-069 | From the modify interface define `update a b m := modify a (fun _=>some b) m` and prove its semantic and invariant laws. | G/P. Exact exercise direction; not only a working concrete example. |
| C06-070 | From the modify interface define `delete a m := modify a (fun _=>none) m` and prove its semantic and invariant laws. | G/P. |
| C06-071 | Package C06-069–070 with retained empty/lookup into a lawful original Map implementation, proving all original axioms from the modified specification alone. | G/P. No access to a particular representation's internals. |
| C06-072 | Conversely, from the original Map interface define `modify a f m` by evaluating `f(lookup m a)` once and choosing `delete a m` for none or `update a b m` for some b. | G/P. Preserve the possibility of adding an absent key; no global default for β is needed. |
| C06-073 | Prove both modify laws for C06-072 using only original Map axioms and valid input; instantiate the modified contract (p.83). | G/P. Do the None and Some branches and all unaffected-key equations; preserve validity in both. |
| C06-074 | State the interface equivalence at the level actually established: the translated operations have the same lookup observations and preserve invariants on valid states. If recording round-trip laws, prove observational ones without assuming concrete-state equality. | G/P/support. The book asks for mutual derivability of specifications, not a representation-level isomorphism; generic clients should consume this observational result. |

## Source defects and mathematical boundary cases

1. **Wrong cross-reference on p.82.** The printed sentence directs map
   deletion to `split_min` in §5.6.4, the interval-tree smart-constructor
   implementation. The correct dependency is the generic tree operation of
   §5.2, p.61. `Tree_Map.thy` imports `Tree_Set` and uses its `split_min` and
   `split_minD`; no interval-tree import occurs. The printed map node has
   arbitrary semantic value β, whereas §5.6.4 treats the second component as an
   endpoint cache and recomputes it. This is not a cosmetic type alias. Keep
   the exact corrected link and a full-payload successor regression witness.
2. **Strict key sortedness, not full-pair sortedness.** For example, pairs
   `(1,10)` and `(1,20)` can be increasing under a lexicographic full-pair order
   while repeating the same key. With `map_of [(1,10),(1,20)]`, deleting the
   first binding leaves lookup 1 equal to `some 20`, whereas functional update
   to none gives none. This is a useful checked counterexample against dropping
   the source's key-uniqueness premise.
3. **Correctly unconditional update law.** The first equation on p.83 has no
   sortedness premise, and the pinned `map_of_ins_list` likewise proves it for
   every list. Do not add a premise by copying the neighboring deletion law.
4. **Difference order is intentional.** Exercise 6.1 prints `set_of(del xs ys)
   = set_of ys \ set_of xs`. Preserve that order or provide an explicit adapter
   to a conventional first-minus-second API; do not record it as a source typo.
5. **Adjacency is not overlap for inclusive natural intervals.** `(0,0)` and
   `(1,1)` have disjoint sets even though their endpoints are consecutive.
   Requiring a gap of at least one missing natural is a stronger normalized
   representation choice, not the minimal exercise invariant. It may be useful
   but must be justified and visible rather than inserted silently into clients.
6. **Sets versus partial Boolean maps.** HOL's Boolean/set identification does
   not automatically give an executable Lean membership decision for arbitrary
   `Set α`. Also, `none` and `some false` are different in `Option Bool`; a
   claimed equivalence with all partial Boolean maps would need a normalization
   invariant or a different semantics. Use the explicit characteristic-map
   adapter in C06-035.
7. **Mutation laws do not imply concrete equalities.** A lawful implementation
   can retain irrelevant balancing choices or a history counter while exposing
   the same lookup. For instance, extend any correct map by a natural counter,
   ignore it in lookup, and increment it on every update/delete. Deleting an
   absent key changes the counter while satisfying the same six Map laws.
   This is a suitable checked negative witness if a round-trip or identity
   theorem is proposed for Exercise 6.2 at the wrong representation level.
8. **Do not conflate finite realization with a finite abstract carrier.**
   Starting from empty and using finitely many updates yields finite support,
   but Figure 6.2 models maps by all `α -> Option β`. No surjectivity from finite
   lists/trees onto that model is required or generally true for infinite α.
9. **No logarithmic map complexity is proved here.** The tree realization is
   unbalanced. Its functional correctness and the interval-list exercise's
   separate linear-time requirement must not be merged into a global
   performance promise for the Map ADT.

The source defects above are recorded as corrections or explicit hypothesis
boundaries; none licenses an axiom. Meaningful false-statement examples chosen
for the eventual source-error ledger must have Lean witnesses. Source inspection
and illustrative arithmetic in this note are not those witnesses.

## Coverage map and handoff

There are no numbered equations or named theorems in this chapter. Coverage is
organized by the two figures, the uniform schema, concrete representations,
and both exercises:

| Source component | Rows |
|---|---|
| §§6.1–6.3 model-oriented schema and implementation discipline | C06-001–010, C06-018–019 |
| Figure 6.1, seven Set obligations | C06-011–017 |
| Exercise 6.1, all single-point operations and Set laws | C06-020–025 |
| Exercise 6.1, binary operations, validity, early exits, linearity | C06-026–033 |
| §6.4 model and Figure 6.2, six Map obligations | C06-034–043 |
| §6.5 tree operations, ordered lists, source framework, composed correctness | C06-044–067 |
| Exercise 6.2, both translations and derived specifications | C06-068–074 |

Completion requires actual law witnesses for both concrete new representations,
corrected source correspondence, an interface-only consumer demonstrating reuse,
and an instrumented linear bound for both interval-list binary operations.
Semantic correctness of a point-enumerating implementation would leave the
exercise's main operational requirement unresolved. Keep every row queued until
the corresponding Lean declarations and acceptance evidence exist.
