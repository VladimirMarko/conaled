# Local #1011 — VFA Extract: requirements and reuse plan

**Planning only, 2026-11-02. Implementation is blocked until #1010 ADT is accepted.**
The sequence remains SearchTree → ADT → Extract → Redblack. This document
does not implement a chapter, prove or compile a declaration, accept a gate,
or modify the candidate, tracker, source inventory, dependencies, or caches.
Proposed names and interfaces must be reconciled with the actual accepted
Sort, Maps, SearchTree, and ADT APIs before implementation. Root owns the
ongoing isolated validation and checkpoint integration.

## 1. Source, scope, and inspected baseline

- Complete inspected chapter: VFA 2.1, release cover `2026-08-24 10:11`,
  [Extract](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Extract.html),
  `reference/vfa/vfa/Extract.v`: **393 lines, 13,003 bytes**, SHA-256
  `c132273a13fafe176573469e664b9cbe8dd3366ec00e2f9a3ab8ab1d42a2e15d`.
  The chapter footer is `2026-08-24 09:43`.
- `../source/Extract.inventory.json`: **34 records**, **four exercises**
  (one optional, none advanced), and **13 extraction commands**. The records
  comprise 14 definitions, seven source assumptions, eight source-proved
  declarations, two Coq tactics, and three admissions to discharge. There is
  no aborted proof in this chapter. `int_elements` has no named declaration;
  lexical inventory coverage alone would miss its mathematical work.
- Complete inspected auxiliary program: `reference/vfa/vfa/test_searchtree.ml`,
  **24 lines, 935 bytes**, SHA-256
  `109e94b84632608b05e2c00081e98b2050a05dd9c5180241aa70486e7620e279`.
  It is part of the execution obligations, not an optional source anecdote.
- The official versioned archive and recovery instructions are in
  `../source/SOURCE-RECOVERY.md`. Archive SHA-256:
  `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
  Retain MIT attribution. Under ADR 0001, preserve references and identities
  rather than including the downloaded research archive in the deliverable.
- Inspected local candidate: `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`;
  Lean 4.35.0, revision `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its Preface/Perm gate
  remains pending. Record the actual accepted ADT baseline later.
- Read AGENTS, architectural/domain guidance, GLOSSARY, the shared language
  direction, ADRs 0001/0010, the implementation workflow, README development
  and audit rules, `../REQUIREMENTS.md`, the full chapter and auxiliary program,
  predecessor plans, `COMPUTATIONAL-ASSUMPTIONS.md`, and the resource/execution
  and tree-reuse notes. Planning starts no new implementation/review loop.

The intended outcome is a faithful Lean adaptation of the chapter's program
execution method: retain its sorting and tree recurrences through existing
generic algorithms, replace all abstract-integer assumptions with explicit
parameters and proved concrete realizations, connect representation changes
through proved equations, and deliver runnable programs with honest observed
results. Neither changing the implementation language nor obtaining a small
benchmark result discharges the mathematical obligations.

## 2. Architecture and minimum interface

Start with ordinary section parameters. A new machine-arithmetic hierarchy,
comparator class, sorting implementation, tree carrier, extraction framework,
or compiler correctness claim is unnecessary. Separate executable operation
data from mathematical laws, and separate those laws from measurements.

The chapter requires precisely this comparison interface:

| Component | Lean obligation |
| --- | --- |
| Carrier `W` | An ordinary type parameter, universe-polymorphic where the underlying generic APIs allow it. |
| `decode : W → Int` | A mathematical interpretation. It need not be surjective. |
| `ltb`, `leb : W → W → Bool` | Actual executable comparison operations. |
| Injectivity | A parameter `Function.Injective decode`, proved for every concrete realization used. |
| Strict reflection | `∀ a b, ltb a b = true ↔ decode a < decode b`. |
| Non-strict reflection | `∀ a b, leb a b = true ↔ decode a ≤ decode b`. |

These are four pieces of operation/interpretation data and three laws, matching
the seven source assumptions. No project `axiom`, opaque mathematical promise,
`sorry`, or assumed external integer behavior may replace any law. A conditional
generic theorem is useful only alongside the required concrete checked clients.
Do not add addition, a decoder inverse, unbounded encodability, or a claim that
all integers fit in a word to this interface.

Keep the weaker hypotheses visible:

- Arbitrary-comparator insertion-sort permutation requires no order law or
  decoder injectivity. Sortedness and decoding compatibility require the
  relevant comparison reflection. Stability by decoded key does not require
  injective decoding or equality/order on payloads.
- Empty lookup is definitional. Same-key lookup after insertion needs the
  irreflexivity supplied by strict reflection, not decoder injectivity.
  The source distinct-**original-key** lookup law uses injectivity to turn
  distinct keys into distinct decoded integers. If two different keys decode
  to the same integer, a comparator-correct search may identify them.
- Storage, tree mapping, inorder traversal, and the accumulator equation need
  no comparison law. Lookup and insert decoding equations follow matching
  comparison branches; injectivity is not needed merely to map those branches.
  The raw-key table contract and its distinct-key observations retain it.
- No generic operation needs a payload default until lookup is called. Keep
  caller-supplied defaults and arbitrary payloads; avoid unnecessary
  `Inhabited V`, `DecidableEq V`, or an ordering on values.

Use the accepted generic SourceInsertion and SearchTree implementations with
small specializations or proved adapters. If they take `DecidableRel`,
`decidable_of_bool` can supply decisions from the actual Boolean comparator
and its reflection law. If they take a lawful ordered key interface, prove
compatibility with that interface while retaining the chosen executable
decisions. `LinearOrder.lift' decode hinj` is a real pinned Mathlib API for
the mathematical order, but its default decision fields compare decoded
integers. Using it blindly can change the runtime operation being demonstrated.
Explicitly review both the law instance and the branch implementation.

The exact placement follows the accepted predecessor modules. A small shared
signed-comparison realization module is justified by the sorting, tree, and
forthcoming Redblack consumers; it should contain only the adapters and their
laws. Sorting and table specializations belong beside those accepted families.
Cross-domain compositions and connected examples belong in `Examples`.
Keep the IO workload driver and reproducibility harness separate from pure
mathematical modules, following the repository's existing script pattern.
Add a source/reuse/coverage research note through the chapter workflow.

## 3. Concrete realizations and actual pinned providers

### Required realizations

1. **Unbounded mathematical integers.** Use `Int`, identity decoding, and
   `decide (a < b)` / `decide (a ≤ b)`. Identity injectivity and ordinary
   `decide` equivalences discharge the laws. This also realizes `insZ` and
   `sortZ`; their correctness is required by chapter prose even though no
   theorem stub is provided. This realization does not model a finite OCaml
   integer or promise constant-cost arbitrary-precision comparison.
2. **Finite signed words.** Use `BitVec w`, `BitVec.toInt`, `BitVec.slt`, and
   `BitVec.sle`. The pinned core provides all required laws. Prove the generic
   realization for every width; use `0 < w` for the usual representable-range
   and conversion-to-self statements. Retain `w = 63` as the explicitly
   bounded model corresponding to the chapter's 63-bit discussion. Its range
   is `-2^62 ≤ decode x < 2^62`, not all `Int`. At width zero the carrier and
   comparisons still make sense; do not claim the usual positive-width range
   characterization there.
3. **A concrete Lean runtime signed integer.** Use `Int64`, its `toInt`, and
   Boolean decisions of its existing `<`/`≤`. The inspected core definitions
   and lemmas establish signed comparison and injectivity; no native behavior
   is taken on faith as a logical assumption. Its range is
   `-2^63 ≤ decode x < 2^63`. It is a 64-bit Lean realization, distinct from
   the 63-bit source model. Use this proved realization for the native-integer
   executable demonstration, retaining the compiler/runtime trust boundary.

For `BitVec`, **ordinary `<`, `≤`, `ult`, and `ule` are unsigned**. Do not use
those to discharge the source signed comparison laws. Use `slt`/`sle`, or an
explicit local order by `toInt`, without globally replacing the ordinary
unsigned instance. For `Int64`, the native decision procedures have runtime
overrides. Their logical definitions remain connected to signed `BitVec`
comparison; those definitions and theorems support the proof, while the
runtime override remains part of the ordinary execution trust boundary.

| Inspected provider API | Exact use and remaining obligation |
| --- | --- |
| `BitVec.slt`, `BitVec.sle`; core `Init/Data/BitVec/Basic.lean` | Their definitions compare `toInt`, supplying the correct signed operations. |
| `BitVec.toInt_inj`, `BitVec.eq_of_toInt_eq`; core `BitVec/Lemmas.lean` | Equality of decoded values implies equality of the original words. |
| `BitVec.slt_eq_decide`, `sle_eq_decide`, `slt_iff_toInt_lt`, `sle_iff_toInt_le` | Exact reflection bridges; the Boolean-to-Prop coercion in the latter statements means equality to `true`. |
| `BitVec.le_toInt`, `toInt_lt`, `toInt_le` | Actual signed bounds; use them to expose finite representability rather than posit an inverse decoder. |
| `BitVec.toInt_ofInt`, `toInt_ofInt_eq_self` | Conversion decodes as balanced remainder modulo `2^w`; equality to the input requires positive width and both signed-range bounds. |
| `BitVec.toInt_add`, `toInt_add_of_not_saddOverflow` | Modular addition semantics and the proved no-signed-overflow specialization. These do not justify unconditional mathematical addition. |
| `Int64.toInt.inj`, `Int64.toInt_inj`; core `SInt/Lemmas.lean` | Proved injectivity of the runtime carrier's mathematical interpretation. |
| `Int64.lt_iff_toInt_lt`, `Int64.le_iff_toInt_le`; `Int64.decLt`, `decLe` | Proved signed-order bridges and existing executable decisions; use `decide` reflection to obtain the source Boolean laws. |
| `Int64.le_toInt`, `toInt_lt`, `toInt_ofInt`, `toInt_ofInt_of_le`, `ofInt_toInt` | Exact range and conversion laws. Unrestricted `ofInt` wraps; range-guarded conversion is identity after decoding. |
| `LinearOrder.lift'`; Mathlib `Order/Basic.lean` | Transports a linear order along an injection and supplies min/max/compare. Review its generated decisions before using it in an executable adapter. |
| `Examples.ComparisonPermutations` reflection declarations and `reflectedLt` | Existing `decide`-iff/`decidable_of_bool` adaptation of Coq reflection and checked proof-carrying branches. Reuse the method, not a new reflection datatype or tactic framework. |
| `Applications.Sorting.insertionOn`, `insertionOn_spec`, `KeySorted`, `Stable`, `StableSort` | Existing standard insertion sort and independent sortedness/permutation/stability observations. First establish the exact source adapter; respect that `StableSort.perm` is output-to-input. |
| `sortOn_eq_insertionOn`, `sortOn_map`, `StableSort.map`, `StableSort.unique` | Independent stable merge/insertion agreement and compatible-map transport. These supply value observations, not equality of execution costs. |
| Accepted SearchTree generic operations over `BinaryTree (K × V)` | Reuse the existing carrier, comparison branch order, raw lookup laws, invariant, slow/fast traversal correspondence, and enumeration/model theorems. Do not copy the algorithms for each integer carrier. |
| Accepted Maps/ADT table operations, separate laws, `withDefault`/presence seam | Preserve optional binding information and reuse history/update clients. Source raw lookup laws use unconditional validity, while enumeration keeps BST. |
| `Squares.Rep`, `Square`, `compose`, `Rep.after`, `vertical` | Package proved decoding equations and compose only matching contracts. They do not establish host compiler correctness or erase arbitrary semantic data in `Type`. |
| `SquareKit.ListFusion.foldl_reachable`, `foldr_reachable` | Reuse when an insertion-history or sorting fold has the required step law and invariant. Prove the step and initial conditions; do not infer fusion from output examples. |
| `Resources.Measured`, `bind_erases`, `erasureSquare` | Reuse accepted measured source algorithms if resource observations are transported. Erasure gives the same value, not native allocation or timing equality. |
| Staged `unaryLERun_spec`, `equal_inputs_steps`, `no_difference_only_bound` | Existing exact lockstep unary comparison and the counterexample to difference-only cost. Reuse after integration; the draft is not an accepted chapter or native-runtime model. |

### Overflow and finite-range boundary

The commented-out source addition axiom is deliberately false for wrapping
words. Give a checked small counterexample, such as 4-bit signed `7 + 1`
decoding to `-8` instead of `8`. Preserve the source's larger-overflow lesson
without treating the commented code as a valid interface requirement.
Expose the correct existing replacement:

```text
decode (x + y) = (decode x + decode y).bmod (2^w)
¬ BitVec.saddOverflow x y → decode (x + y) = decode x + decode y
```

The first equation is `BitVec.toInt_add`; the second is the inspected guarded
lemma. The original all-`c` equivalence can be recovered under no overflow and
injectivity when useful, but cannot be asserted unconditionally. Sorting and
tree comparisons need no addition law. For conversion examples and benchmark
inputs, check the signed range before converting; native counters and input
generation must not silently widen the verified comparison contract.

## 4. Sorting and representation compatibility

The three source variants all use left insertion on ties and tail-first
sorting. Instantiate the accepted source recurrence once per carrier; expose
its equations and comparison correspondence without creating three recursive
copies. For an arbitrary supplied Boolean comparison:

```text
ins a []        = [a]
ins a (b :: xs) = if leb a b then a :: b :: xs else b :: ins a xs
sort []         = []
sort (a :: xs)  = ins a (sort xs)
```

The Nat version specializes accepted Sort with the original natural-number
test. The Int version uses mathematical integer comparison. The abstract-word
version uses the supplied Boolean `leb`, justified by its law. A proposition-
valued `if` is an acceptable Lean adaptation only with the proved exact branch
correspondence; it must still execute the intended chosen decision procedure.

Adapt source `sorted` through the accepted adjacent-chain specification:
`List.IsChain (fun x y => decode x ≤ decode y)`. Retain empty, singleton, and
adjacent-cons constructor/elimination rules. Use transitivity of `Int` order
to connect it with `KeySorted decode`; do not silently substitute all-pairs
sortedness without that bridge. Discharge the exact source contract:

```text
xs.Perm (sort xs) ∧ sourceSorted decode (sort xs)
```

The permutation is on the **original words**, not just their decoded images.
Use the arbitrary-comparator source permutation proof and symmetry of an
existing output-to-input library result as needed. Also recover the conaled
stable-key contract, with distinguishable equal-key payloads in a generic
client, using `insertionOn_spec` and the accepted source bridge.

Prove insertion and whole-sort decoding equations, for every input and with
only comparator compatibility:

```text
map decode (insWord a xs) = insInt (decode a) (map decode xs)
map decode (sortWord xs)  = sortInt (map decode xs)
```

These equations do not need injectivity or surjectivity. They may follow the
accepted mapping theorem or a short recurrence bridge; do not reprove sorting
correctness independently for each carrier. Retain exact program identity
with the accepted insertion recurrence, even when stable merge sort provides
an independent output agreement theorem.

Package concrete list-decoding squares and a connected client that reuses
the accepted sorting observation or an independent ordering checker. A second
client should combine a finite insertion history, tree decoding, and lookup/
enumeration observations; use actual step laws and the existing fold-fusion
tools if helpful. These are ordinary representation-specific compatibility
proofs, not claims of transport to arbitrary mathematical settings.
`Squares.Rep` currently puts both carriers in one universe. Keep generic
operation theorems at their useful universes, and package compatible concrete
instances (or an explicit standard universe lift) rather than silently
restricting every payload to `Type 0`.

## 5. Tree reuse and the complete optional enumeration obligation

Specialize the accepted generic tree to key `W`, ordered strictly by decoded
integer. Its source constructor presentation is `E` / `T l k v r` over the
existing `BinaryTree (W × V)` carrier. Preserve the exact two tests in lookup
and insertion: first `ltb x k`, then `ltb k x`. The equality insertion branch
stores the newly supplied key and value. Do not replace the source with a
balanced container or use an arbitrary payload to access an unrelated
whole-label ordering API.

Extract's `elements_aux` is SearchTree's **fast accumulator traversal**, and
Extract's `elements` is that traversal at `[]`. They are not the earlier slow
append definition by naming convention. Prove/use the all-raw-tree equation

```text
elements_aux t acc = inorderElements t ++ acc
```

before transferring properties. Mapping `(k,v)` to `(decode k,v)` commutes
with this traversal for every raw tree and accumulator, without any ordering
or injectivity premise. Lookup and insertion commute with the corresponding
Int-keyed operations through the supplied strict-comparison law. Preserve
their branch order and equality replacement in the bridge.

The `lookup_empty`, `lookup_insert_eq`, and `lookup_insert_neq` exercises range
over **all raw trees**. Introducing a BST premise would weaken their source
statements. The last theorem's premise is distinct original keys; it cannot
be weakened to an unproved assumption about finite native identities.

`int_elements` is fully in scope. Instantiate the entire accepted enumeration
contract, retaining its exact scopes and the fast/slow adapter, including:

| Required transferred property | Premises and boundary |
| --- | --- |
| `ForallT`, full-subtree `BST`, valid empty, and insertion preservation | All left/right subtree keys satisfy decoded strict separators. Immediate-child checks alone do not define BST. |
| Bound/search laws and `bound_default` | Empty, same-key, and distinct-key bound laws are unconditional; false bound implies default lookup. Lookup equal to the default does not imply absence. |
| Enumeration completeness | `bound k t = true` together with lookup value implies pair membership, on every raw tree. |
| Enumeration soundness | BST plus pair membership gives bound and lookup value for every caller default. |
| `ForallT`/relation transport through enumeration | Preserve the generic all-node predicate and relation-to-a-key forms without adding BST. |
| Both absence converses and bound-value witness | Inverse completeness keeps BST; inverse correctness remains valid on raw trees. Retain `∃ v, ∀ d` in the default-independent bound-value witness. |
| Sorted projected keys and key uniqueness | Establish strict decoded-key order, recover the source non-strict sortedness, and obtain `Nodup` of original projected keys. Do not merely show nodup of whole pairs or compare payloads. |
| Accumulator identity and fast/slow equivalence | All raw trees, arbitrary accumulators; transfer the soundness result with its original BST premise. |
| Empty enumeration and enumeration after insert | Retain the accepted `kvs_insert` replacement recurrence and its separator split lemma; `elements (insert k v t) = kvs_insert k v (elements t)` uses BST. |
| Partial-map abstraction and element/lookup/bound/update correspondence | Reuse head-winning list decoding, the actual optional-map presence/default seam, and the accepted BST-guarded refinement results. |
| Direct structural abstraction coherence and canonical enumeration | Reuse accepted `Abs`/`Abs'` agreement and `elements_relate'` under BST. Valid trees with identical partial-map bindings have equal canonical inorder lists; equality of one default-valued lookup is insufficient. |

These are specializations or proved transports of accepted SearchTree results,
not a second proof library. Where the source exercise has no starter name,
the eventual coverage ledger must still identify the Lean declarations and
their exact theorem types. A checked malformed-tree example and a stored-
default binding example must show why the invariant and presence premises
are retained. Keep structural tree equality distinct from observational map
equality and do not infer physical sharing from either.

## 6. Complete 34-record disposition

Every row is a later implementation obligation, not a claim that a declaration
already exists or is checked. Identifiers retain the exact inventory spelling.

| Source record | Required disposition |
| --- | --- |
| `Extract.ins@26` | Nat specialization of accepted source insertion with exact Boolean ≤/branch bridge. |
| `Extract.sort@32` | Nat specialization of accepted tail-first source insertion sort; reuse correctness. |
| `Extract.insZ@74` | Int specialization with the same recurrence and mathematical signed comparison. |
| `Extract.sortZ@80` | Int specialization plus the prose-required full sorting correctness theorem. |
| `Extract.int@113` | Carrier parameter `W`, with proved Int, signed-word, and runtime realizations. |
| `Extract.Abs@120` | Decoder parameter to Int, instantiated concretely; no surjectivity assumption. |
| `Extract.Abs_inj@121` | Explicit hypothesis and proofs for every supplied realization, never a new axiom. |
| `Extract.ltb@126` | Supplied executable Boolean strict comparison. |
| `Extract.ltb_lt@128` | Exact strict reflection hypothesis and concrete proof. |
| `Extract.leb@130` | Supplied executable Boolean non-strict comparison. |
| `Extract.leb_le@132` | Exact non-strict reflection hypothesis and concrete proof. |
| `Extract.int_ltb_reflect@162` | Boolean/proposition or Decidable reflection of decoded strict order, using its supplied law. |
| `Extract.int_leb_reflect@168` | Corresponding decoded non-strict reflection. |
| `Extract.Z_eqb_reflect@174` | Int equality `decide` reflection with both true and false branch uses. |
| `Extract.Z_ltb_reflect@180` | Int strict comparison reflection. |
| `Extract.Z_leb_reflect@186` | Int non-strict comparison reflection. |
| `Extract.Z_gtb_reflect@192` | Int greater-than as reversed strict comparison; retain operand orientation. |
| `Extract.Z_geb_reflect@198` | Int greater-or-equal as reversed non-strict comparison. |
| `Extract.bdestruct_guard@211` | Document/use ordinary Lean `by_cases`, `simp`, comparison reflection and `omega`; no custom tactic hierarchy required. |
| `Extract.bdall@225` | Checked repeated-branch proof idiom using that same adaptation. |
| `Extract.ins_int@233` | Specialize the accepted generic source insertion to the actual supplied `leb`. |
| `Extract.sort_int@239` | Specialize the accepted source sort, preserving tail-first recursion. |
| `Extract.sorted@253` | Adjacent decoded-order specification with source constructor laws and the accepted Pairwise bridge. |
| `Extract.sort_int_correct@270` | Original-word input-to-output permutation and decoded sortedness for every list; discharge the source admission. |
| `Extract.key@282` | Key alias for the same carrier W, with no extra arithmetic structure. |
| `Extract.tree@284` | Existing BinaryTree key/value carrier with exact E/T presentation. |
| `Extract.empty_tree@291` | Empty tree, independent of a payload default. |
| `Extract.lookup@293` | Accepted raw lookup with caller default and exact two Boolean tests. |
| `Extract.insert@301` | Accepted raw persistent insertion, including the source equality-key replacement branch. |
| `Extract.elements_aux@309` | Accepted fast accumulator traversal with its all-raw-tree arbitrary-accumulator equation. |
| `Extract.elements@316` | Accumulator traversal at [], linked to accepted inorder enumeration. |
| `Extract.lookup_empty@319` | Exact default lookup result for every carrier/payload/default/key. |
| `Extract.lookup_insert_eq@324` | Same-key lookup-after-write for every raw tree; no BST premise. |
| `Extract.lookup_insert_neq@332` | Distinct-original-key lookup unaffected for every raw tree, using the injectivity/comparison laws. |

## 7. All four exercises

| Exercise and source extent | Required acceptance evidence |
| --- | --- |
| `sort_int_correct`, lines 263–275, three stars | The exact permutation-and-decoded-sortedness theorem, concrete Int/word/runtime clients, and the faithful generic-algorithm bridge. |
| `lookup_insert_eq`, lines 323–329, one star | Universal raw-tree theorem with arbitrary payload/default, connected same-key replacement example, and concrete realization use. |
| `lookup_insert_neq`, lines 331–337, two stars | Universal raw-tree theorem with the original key inequality; explicit dependency on decoder injectivity and connected distinct-key example. |
| `int_elements`, lines 339–345, four stars, optional | Every enumeration/invariant obligation in section 5, including the fast/slow traversal identity, presence/default boundary, sorted/nodup keys, insertion/model compatibility, and a complete target list despite the absence of starter declarations. |

## 8. All 13 extraction commands and remaining prose

Lean compiles/evaluates Lean definitions directly. A Lean adaptation does not
need to implement Coq's extraction command or add an OCaml toolchain. It must
still expose inspectable definitions, ordinary native Lean data interoperability,
the relevant dependency closure, and runnable programs. Record the exact
supported execution commands and their results at implementation time; the
following are obligations, not statements that commands have been run.

| Source line | Source command | Lean adaptation |
| --- | --- | --- |
| 40 | `Extraction sort` | Inspect the Nat sort specialization/recurrence and run a connected example of the actual implementation. |
| 47 | `Recursive Extraction sort` | Build the specialization with its real dependency closure and explain the direct Lean execution path. |
| 58 | Native `bool` extraction directive | Use Lean's ordinary Bool in callable operations; prove any Boolean decision bridge. |
| 59 | Native `list` extraction directive | Use ordinary List, retaining the exact recursion and interoperability without a duplicate list type. |
| 60 | `Recursive Extraction sort` after directives | Demonstrate the same source sort using those ordinary datatypes and the established closure. |
| 86 | `Recursive Extraction sortZ` | Build/run the Int specialization with the prose-required correctness theorem. |
| 114 | Inline `int` as target integer | Supply the concrete proved realization; distinguish BitVec63, Int64, and unbounded Int. No unproved native reinterpretation. |
| 127 | Inline `ltb` as `<` | Use the chosen carrier's actual signed executable comparison and its proved decoding law. |
| 131 | Inline `leb` as `≤` | Corresponding non-strict native decision with its law; retain tie behavior. |
| 245 | `Recursive Extraction sort_int` | Build/run the finite runtime specialization and expose its generic proof and decoder compatibility. |
| 349 | Native `prod` extraction directive | Use ordinary Prod/pair lists, including payload preservation in enumeration. |
| 350 | `Recursive Extraction empty_tree insert lookup elements` | Build/run the complete table operation set and connected calls from a Lean client. |
| 358 | `Extraction "searchtree.ml" ...` | Provide a checked standalone Lean entry point and reproducible build/run instructions for the BST workload, with retained evidence. |

The `Set Extraction Output Directory`, import commands, hints, notation scope,
and IDE output instructions are language mechanics. Explain their Lean
equivalents where relevant; they are not additional mathematical axioms or
permission to hide dependencies. Nat and Int syntax/decision differences
must be explicit in the source adapters.

The prose claim that the mathematical decoder and law proofs need no runtime
counterpart has two parts. Lean erases proof terms in `Prop`; executable code
should use the supplied comparisons and should not depend on proof-only
decoding. A function named `Abs`, or a specification function stored in `Type`,
is not automatically erased by naming or by packing it in `Squares.Square`.
Review the actual dependency path of the delivered runtime specialization.
The existing `Compiler.lean` proves a different modeled compiler, not the
correctness of Lean's compiler, its native overrides, or Coq-to-OCaml extraction.

Retain the chapter's unsound-extraction warning as a precise representability
and overflow boundary. Do not describe a finite native integer as a faithful
unbounded Nat realization. Explain that the 63-bit statement describes a
particular source representation/platform convention; the explicit formal
width and the actual runtime carrier are the authoritative parameters here.

## 9. Runnable program and source-faithful workload evidence

### What the supplied ML program actually does

`build` iterates from `j=n` down to `1`, inserting value `1` at `f j`, then
finishes **before** `Sys.time()` is read. The timed `g` loop performs n queries
with default `0` and increments a hit count when the result equals `1`.
Its calls to `f` occur inside that timed loop. `print_test` discards the answer
and incorrectly labels the observation as insertion-and-lookup time.

For random runs, `f` calls `Random.int n` separately during building and
querying. Thus queries are fresh draws and are not guaranteed to have been
inserted; duplicate inserts may replace earlier bindings. The answer must not
be assumed to equal n. For consecutive runs `f j=n-j`, so both actual sequences
are `0,1,…,n-1`, and the unbalanced tree grows into a right chain. The published
sizes are random 1,000,000, random 20,000, and consecutive 20,000. The program
sets no explicit seed, reports no repetitions, and records no correctness
check on the returned hit count.

The source's bytecode and native timings are historical observations. Preserve
their provenance when discussing them, but do not use those numbers as current
Lean evidence, prove a speedup from them, or claim the faster order will hold
on every machine. `Sys.time` measures process CPU time; the inspected Lean
`IO.monoNanosNow` is a monotonic elapsed-time observation. Label the clock,
unit, timed scope, and execution mode instead of silently equating them.

### Required delivered driver and protocol

1. Deliver an ordinary Lean client for Nat/Int/finite-word sorting and for the
   source empty/insert/lookup/elements API. Have a standalone `main`, documented
   input/options, nonzero failure on incorrect results, and a retained output
   summary. All calls must use the proved adapters, not a separate benchmark
   implementation with a similar name.
2. Implement a source-shaped workload with separate build/query phases, the
   same key generation order, values/defaults 1/0, and a visible checked hit
   count. Label its measured query phase accurately; if generation is inside
   that phase, state it. A separately labelled total or build timing may be
   added, but cannot replace or relabel the source observation silently.
3. Also expose explicit insertion and query key lists for a controlled reusable
   workload. Preserve the exact generated lists or their reproducible seed,
   generator identity, size, range, and digest. Reuse **identical** lists and
   carrier semantics in the later Redblack comparison. A pre-generated lookup-
   only run and an RNG-in-loop run are distinct experiments and need distinct
   labels. Any allocation/validation/input-generation inclusion must be stated.
4. Existing pinned APIs include `mkStdGen`, `randNat`, `IO.setRandSeed`, and
   `IO.rand` in `Init/Data/Random.lean`. Their bounds are inclusive, unlike
   `Random.int n`: for positive n, use range `[0,n-1]`. Handle the zero-size
   empty workload without requesting a random number from an empty range.
   Thread explicit generator state or serialize seeded IO so that another
   consumer cannot perturb the stream. This is reproducibility evidence, not
   a formal uniform-distribution proof or equality to OCaml's PRNG sequence.
5. Validate results against an independent finite map/first-binding list model
   or a small finite set of inserted keys. For every generated query, expected
   success means an actual inserted binding; random hit counts need not be n.
   Check canonical enumeration, distinct-key count, and stored default-valued
   cases on bounded correctness workloads. Consume/report a result checksum
   or count so the experiment actually observes the computed results.
6. Convert generated keys only under checked signed-range bounds. State the
   chosen carrier, including whether the run is Int64 or a BitVec63 model.
   Signed negative/minimum/maximum examples supplement the positive random
   workload; positive-only timings alone cannot test signed-order fidelity.
7. Use bounded smoke sizes for automated validation and explicit configured
   resource limits for larger observations. Keep the original published sizes
   as named reproducible scenarios, but do not require an unbounded run or
   extrapolate a smaller completed run into a larger successful result. Record
   any attempted timeout, stack/resource limit, and skipped optional large
   scenario honestly. A bounded executed workload is still required.
8. The repository already uses `lake env lean --run scripts/...` and a bounded
   measurement harness in `scripts/benchmark-order-certificate.py`. Reuse that
   execution/evidence pattern through Nix/direnv. Provide and actually verify
   the direct runner path and a standalone compiled executable path, adapting
   the source's interactive/standalone stages to the pinned Lean toolchain.
   A small executable target or script may be added through the ordinary
   chapter workflow if needed; no toolchain-version change, foreign compiler,
   new extraction backend, or altered proof gate is mandated. Inspect the
   actual paths before calling one interpreted or native. A mode that has not
   been executed has no success or performance evidence.
9. For each measured run, retain exact candidate/source identity, command,
   Lean and dependency versions, backend/mode, host description where available,
   seed/workload identity, n, repetitions, timer/unit, measured region, exit
   status, complete result checks, raw timings, and logs. Warmup and repetitions
   are recorded choices, not hidden adjustments. Report observations separately
   from kernel-checked semantics and abstract operation counts.

Pure theorem coverage must not import an IO/randomness/timing premise as a
mathematical axiom. The functional workload correctness statement quantifies
over finite input sequences; executable generation and measurement exercise
that verified client under the stated runtime trust boundary.

## 10. Resource claims and corrections to chapter prose

The source sentence making unary `leb` time proportional to the *difference*
of operand values is inaccurate for the lockstep recurrence under discussion.
The inspected staged model has exact terminal-call-inclusive count
`min n m + 1`. Equal inputs have zero difference and arbitrarily many charged
calls; `no_difference_only_bound` states that obstruction for every proposed
difference-only bound. Retain the correction with the source location and
reuse that result after its integration. Do not identify this explicit model
with Lean's native Nat, with every Rocq numeric comparator, or with CPU time.

Binary/arbitrary-precision comparison requires a representation-size cost
model before claiming logarithmic complexity. Fixed-width comparisons may be
charged as primitives in a stated machine-word model; the reflection laws
alone prove no constant-time or constant-allocation theorem. Do not create an
unnecessary bit-cost development to justify an unqualified runtime slogan.
Use the accepted source comparison-count results and state precisely which
numeric representation assumptions connect them to a resource conclusion.

For trees, reuse the accepted height/path and measured comparison contracts.
Increasing distinct keys produce the source unbalanced chain: per-lookup
worst-case path length is linear in its node count, and a whole n-query scan
can take quadratic aggregate work. A bounded observed random workload does
not prove an expected logarithmic bound, and a BST invariant alone does not
bound height logarithmically. If formalizing the consecutive family for words,
keep a bound ensuring all generated keys are distinct and representable;
do not quantify an arbitrarily long strictly increasing fixed-width sequence.
The forthcoming Redblack chapter supplies balancing; this plan does not start
its implementation or replace the current source tree with a balanced one.

Value-preserving decoder squares and fast/slow enumeration equalities do not
imply equal costs, stack use, pointer sharing, or timings. Keep measured
recurrences, retained semantic values, and host observations separate and
compose only the stated resource contract.

## 11. Connected cases, statement review, and completion gates

Implement meaningful cases alongside the universal claims, using kernel-safe
proofs and the accepted public APIs. Reuse predecessor cases when they already
show the needed boundary rather than reproducing every small example.

- Empty, singleton, repeated-value, negative/zero/positive, and signed endpoint
  sorting cases; an equal-key labelled-record case connects stability to the
  shared generic sort. Check permutation of original values and decoder
  commutation, not only one expected output list.
- A signed/unsigned disagreement, for example 4-bit `-1` and `0`, shows why
  unsigned BitVec comparison cannot implement the source law. Check ordinary
  finite signed comparison at both endpoints and range-guarded conversion.
- The 4-bit overflow counterexample and the no-overflow specialization show
  both failure and the valid replacement for the commented addition axiom.
- An explicitly noninjective decoder with distinct colliding keys demonstrates
  why the distinct-key table law needs injectivity, while sorting can still
  preserve original elements and sort their decoded keys.
- Empty and repeated-key table writes, distinct-key lookup preservation,
  missing and stored-default bindings, negative keys, a valid ordered tree,
  and a malformed tree connect the raw laws and the guarded enumeration laws.
- A finite build/query history and a decoding/enumeration composition connect
  the general contracts to the actual runnable client. Validate the workload's
  hit count against an independent observation, including a random-style list
  containing duplicates and a query that was never inserted.
- Source-shaped and controlled benchmark labels/clock ranges, deterministic
  seeded replay, zero-size behavior, invalid ranges, and result-consumption
  behavior need bounded runtime regression evidence when their driver is added.

Statement review must check source quantifiers, original versus decoded key
inequality, the direction of permutation, comparator argument order, exact
recurrences, no-BST raw laws, source-sortedness equivalence, all enumeration
premises, universe scope, finite-range bounds, and the proof/runtime separation.
Review the actual declarations and executable dependency path; an intended
comment or a similarly named library function does not establish these facts.

Before implementation, record the accepted predecessor candidate and clean
starting state, and use the enclosing local implementation/review workflow.
After implementation, the coverage ledger must map all 34 records, four
exercises, 13 commands, unnamed prose obligations, the ML program adaptation,
and every corrected or qualified source claim to exact declarations/docs/
evidence. No optional mathematical exercise is waived.

Acceptance still requires applicable integrated build and exhaustive proof
audit in the isolated clean stable candidate through Nix/direnv,
`./check.sh --candidate HEAD`, necessary executable regressions, both independent
Standards and Spec reviews on that same candidate, and
`./check.sh --verify-candidate HEAD` immediately before acceptance. New axioms,
admissions, user-written unsafe definitions, and native-decide proof shortcuts
remain prohibited. Runtime results cannot substitute for those gates.
Only then may root close local #1011, checkpoint complete source/history/local
tracking/coverage/review/evidence and recovery instructions, upload and expose
the checkpoint, and proceed to Redblack. This planning file accepts none of
those stages and makes no GitHub write.

## 12. Exact identities of inspected providers

Hashes below pin the inspection, not future acceptance. Source/notes are
workspace-relative; project paths are relative to `conaled/`; Mathlib paths
are relative to its pinned checkout. Core paths are relative to the source
root of the pinned Lean 4.35.0 toolchain. Recheck any changed provider and
record the accepted versions when the chapter begins.

| Source or work-state input | SHA-256 |
| --- | --- |
| `reference/vfa/vfa/Extract.v` | `c132273a13fafe176573469e664b9cbe8dd3366ec00e2f9a3ab8ab1d42a2e15d` |
| `reference/vfa/vfa/test_searchtree.ml` | `109e94b84632608b05e2c00081e98b2050a05dd9c5180241aa70486e7620e279` |
| `work-state/source/Extract.inventory.json` | `79583ef29684f9b16e6b4adb86e91f35738186cc7841e17ad9c2a7193a42c755` |
| `work-state/source/COMPUTATIONAL-ASSUMPTIONS.md` | `eb4e8eb1cc4d04f6fe536e87622c4943d6af160b555e7ae4266979484f3eca30` |
| `work-state/source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` | `5d26488e0127a072c61c3db0323deececfd428023d71cf51b4db6b4055e5e03f` |
| `work-state/source/TREE-INVARIANT-REUSE.md` | `b7078b4a213b2a37035fa25531245749eeed411ff767aa8956a71678efe614db` |
| `work-state/specs/1003-Sort.md` | `fcc06acf05245de79637600479006e3d4a98f8bdf85c2537f5e7451cf3042955` |
| `work-state/specs/1009-SearchTree.md` | `7bd10a9e771d38364bc806d28b38e6cca8f042a7701e3b852fe331d4cd0819e3` |
| `work-state/specs/1010-ADT.md` | `f53d2e54b8d587e27e486f5a08fb1746cc8e2ee16810d0c28c9e44c8e3bfa3e8` |
| `work-state/staging/unary-costs/UnaryComparisonCosts.lean` | `997aa73ce69fe65712ba97a1217909a6f7af8c2d00e7e2978a4ca03a18c01c13` |

| Project / dependency provider | SHA-256 |
| --- | --- |
| `Applications/Sorting/Sort.lean` | `5acd7728aaaefdec121df797efafd7dae13476c820d4f85f4ada19868fa71218` |
| `Applications/Sorting/Stable.lean` | `288552150aa002c60ed06c74e69510112cf9b4e2f0045da3d98ca5c39264d881` |
| `Examples/ComparisonPermutations.lean` | `325df7f29e321436e8bd09fa5eada9af614847825c06028af3933b3f447f393d` |
| `Squares.lean` | `2556c4c895a747bc0092239b5dc5b220e8a6d4d6cf8a6f9fe66ab96fa2462dc7` |
| `SquareKit/ListFusion.lean` | `5ade8a9736d46b558e548aa7b1e8c60c6110f674c22deecb0038dc302b7b0164` |
| `Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `scripts/benchmark-order-certificate.py` | `faa59dc2d2e0c0e64ad44322c40ae9754577507fbf6d3c6e6b64aa5aefa8690f` |
| `lakefile.toml` | `76966dfb4ea744d75d4bbe20ed3a6c576a17145d23f36ba44c4422673c51b04f` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lake-manifest.json` | `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b` |
| Mathlib `Mathlib/Order/Basic.lean` | `65700f7c4ab3a15fc4671eade9689f54a8f6bd9e2750bd315736230ef799ae52` |
| Mathlib `Mathlib/Data/Tree/Basic.lean` | `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d` |
| Lean core `Init/Data/BitVec/Basic.lean` | `99cd942131d0fa51deb2ad9320c2fca4176a21b4250eda313b8642b6548f5197` |
| Lean core `Init/Data/BitVec/Lemmas.lean` | `6c9ccb1b115982ac30bcd314b897cc64515e068f57b2b492d3a02b2369067e1f` |
| Lean core `Init/Data/SInt/Basic.lean` | `4868b10bbef3740a4ddcaa5c8b7ccf18fd099bef301ddbc5ac8b1b8ce4e7b225` |
| Lean core `Init/Data/SInt/Lemmas.lean` | `7cd270efa21719a56cb69845ad59dacb1ebfa31be7b48dbfe01d25d22859cdac` |
| Lean core `Init/Data/Random.lean` | `10bc81cac764ae9d426e141954af5a3ba21f89acd9130b437db39e01059a6ec2` |
| Lean core `Init/System/IO.lean` | `409886ee25dd6ee5455dbb83269edbef98012dd22c5b6c45198b47514aeaca25` |

No Lean compiler, benchmark, executable test, or formal acceptance command was
run for this plan. Inspection of pinned declarations supplies an actionable
reuse map; the later chapter must provide its own checked proof and runtime
evidence on its stable candidate.
