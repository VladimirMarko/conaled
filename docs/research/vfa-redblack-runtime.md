# VFA Redblack: the shared executable client and runtime evidence

Historical observation scope: measurements, generated-code inspections and
receipt identifiers below describe the original CTB-93 donor increment at the
source/artifact hashes stated. They are not observations of the current receiving
tree. Old external filenames identify historical records; their current availability
is not inferred from a path or a hash. The retained source/test owners provide
reproducible behavior; [CTB](../textbooks/CTB.json) records CTB-93 attribution
and CTB-78 receiving status. Any new receiving result must bind its actual inputs.

The [shared Extract driver](../../scripts/ExtractSearchTree.lean) now selects the actual source Redblack implementation alongside the ordinary search tree. Both realizations use the same workload generation, chronological writes, signed key adapters, query loop, result checks and output protocol. This note connects that executable extension to the source chapter and records the bounded observations actually obtained during checkpoint 041 development. The [Extract runtime note](vfa-extract-runtime.md) retains its historical checkpoint 039 source, generated-code and execution assessments.

## Assessment status and exact inputs

The driver assessed for checkpoint041 had **681 lines and 38,199 bytes**, SHA-256 **`ab87c0c836c0ad25ce19096248da5cbcc155269c41daf9fe2a10ec664ce4f997`**. It contains 26 private functions, one private configuration record and one public `main`: 28 authored named declarations, with no authored theorem, axiom, unsafe definition or replacement tree implementation. The corresponding historical [public harness](../../scripts/test-extract-searchtree.py) had **1,283 lines and 79,598 bytes**, SHA-256 **`92c219f015299805914386a864ed2609182efbd7fa0c203853a1246ed9e25a86`**. It retains all 26 earlier test methods and adds ten methods exercising the extension through public commands. Its schema-1 compatibility does not change the attribution of any historical execution.

The primary source is VFA 2.1 [Redblack](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Redblack.html), locally inspected as the complete 838-line `Redblack.v`, 27,066 bytes, SHA-256 `f44255ba3d0235f6efa401b72f2fcf9a9551a7ebc065912202d6f33494891ce2`. Its performance section extracts `empty_tree`, `insert`, `lookup` and `elements`, then reuses the 24-line `test_searchtree.ml`, 935 bytes, SHA-256 `109e94b84632608b05e2c00081e98b2050a05dd9c5180241aa70486e7620e279`. The [complete canonical specification](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1012-Redblack.md), particularly section 9, supplies the source/runtime correspondence obligations. Current SESSION instructions govern the established native environment and prohibit task-imposed resource caps.

The selected toolchain remains `leanprover/lean4:v4.35.0`; Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`, and Batteries to `66e469188fe07963e5cf666c7d4433f45b8131c5`. The historical 722-byte `lakefile.toml`, SHA-256 `4a02b9bfe546ecee0a4cb5070f75939bac510c1b412315490a4ff854fb57db81`, already supplies the `extract-searchtree` executable target. No second executable target or replacement extraction backend was introduced.

This document records the checkpoint041 source and elaborated-type assessment, inspection of computational paths generated for that increment, its identified native ELF, and bounded observations in both direct and compiled modes. Final acceptance in both launch modes belongs to the external exact-candidate checkpoint receipts; a document inside the candidate does not assert its own eventual commit or acceptance. Runtime evidence does not add axioms to the pure results or establish compiler correctness.

## 1. Actual source operations

The driver imports [RedBlack.Models](../../Applications/Search/RedBlack/Models.lean) and [RedBlack.Depth](../../Applications/Search/RedBlack/Depth.lean), in addition to the existing Extract dependencies. The key type and tree type are parameters of the shared sample and table routines. Selection occurs once per sample through the existing `Search.OrderedMap.Ops` interface.

| Operation | Ordinary realization | Redblack realization |
| --- | --- | --- |
| Empty state | `DecodedKeys.ops ltb`.empty, the existing empty `BinaryTree` | `Search.RedBlack.ops ltb`.empty = `Search.RedBlack.empty` = the existing colored carrier's nil |
| Chronological writes | `OrderedMap.bindAll (DecodedKeys.ops ltb)` | The same `OrderedMap.bindAll (Search.RedBlack.ops ltb)` |
| One write | Existing `DecodedKeys.insert ltb` | Actual `Search.RedBlack.insert ltb`: `makeBlack (ins ltb key value tree)` |
| Optional search | Existing `DecodedKeys.lookup? ltb` | Actual `Search.RedBlack.lookup? ltb`, using the colored carrier's `find?` with the source's two short-circuit Boolean tests |
| Default search | Actual optional result followed by `Option.getD default` | The same adapter, definitionally the body of `Search.RedBlack.lookup` |
| Full enumeration | `Examples.ExtractedTrees.elements` | `Search.RedBlack.elements`, the actual carrier's `toList` |
| Enumeration with suffix | `Examples.ExtractedTrees.elementsAux` | `Search.RedBlack.elementsAux`, the actual carrier's right fold with `List.cons` |
| Size and maximum height | Actual `BinaryTree.numNodes` and `BinaryTree.height` | Actual colored-tree `size` and `Search.RedBlack.height`, the carrier's `depth` |

[RedBlack.Basic](../../Applications/Search/RedBlack/Basic.lean) owns the source insertion algorithm. Recursive `ins` calls its full `balance` after either descent. Its matcher prioritizes left-left, left-right, right-left and right-right, after the red-root bypass, and then falls back to the unchanged arrangement. Public insertion blackens the resulting root. The driver does not call the provider's separate insertion algorithm or a Python reconstruction of red-black insertion. The provider supplies the existing datatype, search, fold, root blackening and structural observations.

Both realizations receive exactly `Workload.sourceWrites` of the encoded insertion list, with payload 1. The existing `bindAll` passes each returned state to the next chronological write; repeated keys can replace a binding without increasing distinct size. Neither write count nor the generator's universe is substituted for actual node count. The fixed table example additionally uses arbitrary payloads and a stored zero.

The accepted mathematical invariant and model results remain separate from the executable validation described below. The runtime routines themselves do not take theorem hypotheses, reflection proofs or a valid-tree subtype. Their actual finite inputs are range checked, and their reported results are independently checked before a success record is printed.

## 2. Commands, signed carriers and record versions

Run from the repository root within the established environment:

```sh
lake env lean --run scripts/ExtractSearchTree.lean examples
lake env lean --run scripts/ExtractSearchTree.lean redblack-examples
lake env lean --run scripts/ExtractSearchTree.lean workload --realization redblack
```

The direct launcher elaborates the script and invokes Lean's direct runner. The standalone recipe uses the existing target and the same `main`:

```sh
lake build extract-searchtree
.lake/build/bin/extract-searchtree redblack-examples
.lake/build/bin/extract-searchtree workload --realization redblack
```

A recipe is not an execution record. Successful standalone execution requires a fresh identified binary and retained invocations of that binary. Launch mode is established by external command provenance, not by a self-reported JSON field.

`--realization ordinary|redblack` selects the implementation; its default is `ordinary`. Unknown or duplicate selections fail. All existing options and cross-option restrictions remain:

| Option | Values/default | Contract |
| --- | --- | --- |
| `--carrier` | `int`, `word63`, `int64`; default `int64` | Same actual signed adapters in both realizations |
| `--pattern` | `consecutive`, `random`, `replay`; default `consecutive` | Ascending keys, explicit-state random generation, or retained input lists |
| `--timing` | `controlled`, `source`; default `controlled` | The two measured regions in section 4 |
| `--size`, `--queries`, `--universe` | Nat; each defaults to 32 | Insertion/query counts; random keys are drawn in `[0,U-1]` |
| `--seed` | Nat; default 1729 | Fresh `mkStdGen` initial state for each sample |
| `--warmups`, `--repetitions` | Nat; defaults 0 and 1 | Every sample is retained; repetitions must be positive |
| `--inserted-file`, `--queries-file` | Paths; absent by default | Both required for replay, one signed decimal key per line |

Replay is controlled-only, derives counts from its two files, and rejects supplied size/query/seed/universe options. Other patterns reject file options. Source timing requires equal build and query counts. A random workload with any requested draw requires positive U; an entirely empty random workload can use U = 0. The files are read once before samples; each sample rebuilds from the same immutable lists. Errors do not yield successful JSON. As before, invalid top-level commands return 2; handled option, file, conversion and validation failures return 1; success returns 0 and prints one compressed JSON object.

| Carrier | Actual type | Exact permitted input range and comparator |
| --- | --- | --- |
| `int` | `Int` | Unbounded integers; `SignedComparison.intLtb` |
| `word63` | `BitVec 63` | `−2^62 ≤ k < 2^62`; `SignedComparison.wordLtb` uses signed interpretation |
| `int64` | `Int64` | `−2^63 ≤ k < 2^63`; `SignedComparison.int64Ltb` selects the signed native comparison |

The actual definitions are in [SignedComparison.lean](../../Applications/Representations/SignedComparison.lean). Finite positive prefix counts and random universes are checked before schedule allocation; each original input also passes the exact signed range check before encoding, then the decoded round-trip check. These guards prevent modular conversion from silently changing the input. Adjacent unrepresentable endpoints are rejected for Redblack as well as the retained ordinary cases. `BitVec 63` is not silently identified with `Int64`, and unbounded Int comparisons are not assumed constant time.

`examples` preserves its complete schema-1 JSON and all earlier sorting, comparison, table, overflow and width-zero observations. `workload` now emits **schema 2**, adding `config.realization` and `sample.tree` to the earlier fields. `redblack-examples` is a separate schema-2 kind containing the same three independently expected table histories together with actual tree observations and four raw invariant counterexamples. The observer accepts historical schema-1 workloads using their exact old field set; it does not invent absent shape or realization data. Its own acceptance envelope still has schema 1, independently of the observed document's schema version.

Keys are canonical decimal strings in JSON, preserving exact signed magnitudes. Payloads, counters, heights, generator states and elapsed nanoseconds are integers, not floating-point approximations. Optional lookup results remain a payload or null. Bool, Nat, null and decimal string distinctions are checked strictly by the public observer, including rejection of Bool values masquerading as integers.

## 3. Independent finite-map and structural checks

### Full map meaning and the stored-default case

After the query clock, the Lean driver builds a separate `Std.HashMap Int Nat` from the original integer insertion keys. It checks every actual optional lookup against the independent optional result, verifies the consumed timed hit count, and verifies complete enumeration: strictly increasing decoded keys, exactly the reference map's distinct size, and each returned binding present with its expected value. Together those checks establish equality with the finite reference map for the recorded run, rather than checking only an aggregate checksum.

The Python public observer independently rebuilds a normal integer dictionary, compares its complete sorted entries and every optional query, checks all hit and distinct counts, and validates generator states, schedules, input ranges, phase/index ordering and deterministic sample fields. It does not use the tested Lean comparator or finite encoding to construct its reference map.

The fixed chronological writes are `(-3,7), (4,8), (-3,9), (0,0)` and queries are `[-3,4,0,-1]`. For each of Int, BitVec 63 and Int64, both implementations must produce optional results `[9,8,0,null]`, default-0 results `[9,8,0,0]`, and default-99 results `[9,8,0,99]`. Thus stored zero and absence remain observably different. Enumeration is exactly `[(-3,9),(0,0),(4,8)]`; suffix enumeration retains `(99,123)` after those bindings. The actual Redblack history has black root 0 with black children −3 and 4, size 3, height 2 and black height 2. The source ordinary history has height 3. Empty-state enumeration and optional/default lookup are checked in the same public example.

### Independent observations of actual shape

Each workload sample reports `tree.nodes`, `tree.height`, `tree.bst`, `tree.redblack` and a flat `tree.preorder` stream. Nil is null. A node is `[color, decimal-key, Nat-payload]`; ordinary color is null and colored nodes use `red` or `black`. Every nil child is included, making the complete actual shape observable. The stream contains `2*N+1` tokens for N nodes. The driver reports its actual library size/height; these are checked again from the independent stream.

The Lean ordering checker carries both strict ancestor bounds through every descendant of the color-erased tree. The color checker separately inspects the public black-root convention, every red parent's children, and equality of left/right black height at every node. Nil black height is 0; each black internal node contributes 1 and each red node 0. Inconsistent child heights return `none`. The driver also evaluates `height ≤ 2 * (nodes+1).log2`, including empty and singleton inputs. These are **executable Boolean checks**, not kernel certificates or new formal preservation theorems.

The Python observer traverses the reversed preorder with an explicit stack, reconstructs node counts, height, subtree minima/maxima, all-descendant ordering, root color, red adjacency and common black height, then separately reconstructs inorder entries. Every reported field must match these independent calculations, and the reconstructed entries must match the full finite-map listing. Successful workloads must satisfy the required invariants even if a forged record accurately reports their failure. An explicit stack avoids adding a Python recursion-depth limit to ordinary chains. No new insertion algorithm is present in this observer.

Four raw fixtures separate the checks. They are observed with validation disabled only to expose their actual false properties; the same public-tree validator is then called with validation required and must reject each one:

| Fixture | Size / height | Ordering | Black root | No red-red | Common black height | Why rejected |
| --- | --- | --- | --- | --- | --- | --- |
| Deep key outside bound | 4 / 3 | False | True | True | 2 | Key 1 lies in the left subtree of root 0 although immediate parent comparisons are locally ordered |
| Red-red chain | 3 / 3 | True | True | False | 1 | Red parent −2 has red child −3 |
| Unequal black height | 2 / 2 | True | True | True | Absent | Black left leaf under black root, with empty right branch |
| Red singleton root | 1 / 1 | True | False | True | 0 | Violates the public history's black-root convention |

The general source `RB` predicate under a black hypothetical parent allows a red root. The last fixture therefore does not refute that general predicate; it checks the stronger convention of states built by public `insert`. Every fixture independently satisfies the reported numeric logarithmic bound, so its rejection is attributable to the indicated separate property. The Python observer also checks the raw preorder of each fixture against literal independently stated expected entries and flags.

## 4. What the clocks measure

The source ML `test` function builds the tree before reading `Sys.time`, generates fresh `f j` inside the query loop, applies default 0, and counts lookup results equal to 1. Its printed insertion-and-lookup label does not describe its actual query-only timer. The source printer discards the returned count; this client retains and verifies it.

| Phase | Controlled mode | Source mode |
| --- | --- | --- |
| Before clock | Generate/read both input lists, check range/conversion, build the selected tree | Generate insertion list, check its range/conversion, build the selected tree |
| Timed region | Traverse the prepared encoded query list, actual selected optional lookup, default 0, hit count | Create/traverse descending query schedule; generate each fresh query; check range and conversion; actual selected lookup, default 0, hit count |
| After clock | Independent optional/map/enumeration checks, size/height/invariant observation, JSON | Replay the same generator state to retain exact query keys and check final state, then the same independent checks and observations |

The `IO.lazyPure` wrappers delimit actual pure computations within the IO sequence. The build wrapper completes before the first `IO.monoNanosNow`; the query wrapper lies between the two clock calls; source replay and both validation wrappers follow the second clock. Source mode's timed loop keeps only generator state and the hit count, so capturing the report's full query list does not add list accumulation to the measured loop. The later replay must reproduce both generator components. Controlled mode excludes input-file parsing, key conversion and query generation from the timer.

Each sample resets `mkStdGen seed` or reuses its retained replay inputs and rebuilds independently. Warmups are reported before measured samples, with their own zero-based indices. No sample is silently dropped. There is no build-time claim and no timing-based pass/fail threshold. Both regions return the measured hit count into later checking, making the consumed result observable.

Lean's `IO.monoNanosNow` reports monotonic elapsed wall-clock nanoseconds. The source's `Sys.time` reports process CPU seconds. Host scheduling, representations, allocation, compiler transformations and the differing measurement regions can affect the observations. The pinned Lean `StdGen/mkStdGen/randNat` sequence is recorded and checked against an independent pinned observer; equal seeds do not imply equality with OCaml `Random.int` streams. Source mode preserves fresh-query placement, not cross-language generator bitstream identity.

## 5. Every authored declaration and its role

All definitions except global `main` are private. For this table only, `Cfg` means the private `WorkloadConfig`, `Json` means `Lean.Json`, `B W` means `BinaryTree (W × Nat)`, `R W` means `Search.RedBlack.Tree W Nat`, and `Ops W T` means `Search.OrderedMap.Ops W Nat T`. These are explanatory abbreviations. Generic key and state binders in this executable are universe-zero `Type`; the accepted library operations retain their own generic universes.

| Declaration | Actual elaborated type, with the stated abbreviations | Body assessment |
| --- | --- | --- |
| `WorkloadConfig` | `Type` | Four String settings, six Nat settings and two optional paths; ordinary/consecutive/controlled defaults retained |
| `parseWorkloadOptions` | `List String → Cfg → List String → Except String Cfg` | Pairwise parser, seen-option tracking, supported realization selection and all earlier cross-option guards |
| `readKeyFile` | `String → IO (List Int)` | Reads once, parses each signed decimal line with an indexed error; no tested map operation |
| `generatedKey` | `Cfg → Nat → Nat → StdGen → Except String (Int × StdGen)` | Actual pinned random draw with range check, or count-minus-descending-index consecutive key |
| `generatedKeys` | `Cfg → Nat → StdGen → Except String (List Int × StdGen)` | Existing source index fold; explicit state threading and chronological list recovery |
| `orderedWithin` | `{W : Type} → (W → Int) → Option Int → Option Int → B W → Bool` | Both ancestor bounds, independently recursive through all descendants |
| `ordinaryPreorder` | `{W : Type} → (W → Int) → B W → List Json → List Json` | Actual node/null preorder with preserved suffix; no state mutation or insertion |
| `redblackPreorder` | `{W : Type} → (W → Int) → R W → List Json → List Json` | Same raw observation, preserving actual root colors |
| `rootBlack` | `{W : Type} → R W → Bool` | Nil/black true, red false |
| `noRedRed` | `{W : Type} → R W → Bool` | Red nodes require both child roots black/nil; recursively checks both subtrees |
| `blackHeight?` | `{W : Type} → R W → Option Nat` | Nil 0; recursively equal child heights; increments only black nodes |
| `ordinaryTreeObservation` | `{W : Type} → (W → Int) → B W → Except String Json` | Rejects false all-descendant ordering; reports actual size/height and complete shape |
| `redblackTreeObservation` | `{W : Type} → Bool → (W → Int) → R W → Except String Json` | Separates ordering, public root, local color, common black height and logarithmic check; required-valid mode rejects any failure |
| `sourceQueries` | `{W T : Type} → Cfg → (Int → Bool) → (Int → W) → (W → Int) → Ops W T → T → StdGen → Except String (StdGen × Nat)` | Fresh query generation, checked representation, selected actual optional lookup/default/hit count within the source region |
| `workloadSampleFor` | `{W T : Type} → Cfg → Option (List Int × List Int) → String → Nat → (Int → Bool) → (Int → W) → (W → Int) → Ops W T → (T → List (W × Nat)) → (T → Except String Json) → IO Json` | Shared build/clock/query/clock pipeline, then source replay, independent HashMap check, structural observer and report |
| `workloadFor` | `{W : Type} → Cfg → (Int → Bool) → (Int → W) → (W → Int) → (W → W → Bool) → IO Json` | Reads replay inputs once; selects actual Ops and observers; sequential warmups and repetitions; schema-2 configuration |
| `workload` | `Cfg → IO Json` | Unchanged actual Int/BitVec63/Int64 specialization and early finite-capacity guards |
| `wordAdditionCase` | `Int → Int → Int → Bool → IO Json` | Unchanged checked four-bit addition and signed overflow observation |
| `wordBoundaries` | `IO Json` | Unchanged overflowing/safe addition and explicit width-zero collapse examples |
| `tableCase` | `{W T : Type} → String → (Int → Bool) → (Int → W) → (W → Int) → Ops W T → (T → List (W × Nat)) → (T → List (W × Nat) → List (W × Nat)) → (T → Except String Json) → IO (Json × Json)` | Same independently expected arbitrary-payload writes, optional/default distinction, suffix and empty behavior; pairs original table record with actual tree observation |
| `comparisonCases` | `{W : Type} → String → Int → Int → (Int → Bool) → (Int → W) → (W → Int) → (W → W → Bool) → (W → W → Bool) → IO Json` | Unchanged signed less/equal/greater and finite endpoint observations |
| `stableSortCase` | `{W : Type} → String → (Int → Bool) → (Int → W) → (W → Int) → (W → W → Bool) → IO Json` | Unchanged labelled tie preservation through the actual generic source sort |
| `finiteSortCase` | `{W : Type} → String → Nat → Int → Int → (Int → W) → (W → Int) → (W → W → Bool) → IO Json` | Unchanged signed finite range/round trip and actual sorted extreme-key output |
| `natSortCase` | `List Nat → List Nat → IO Json` | Unchanged actual Nat sort checked against independent finite expectations |
| `examples` | `IO Json` | Retains complete schema-1 ordinary examples; discards only the new private table pair's shape component |
| `redblackInvariantCases` | `IO (List Json)` | Four raw literal fixtures; observes their separate failures and checks actual required-valid rejection |
| `redblackExamples` | `IO Json` | Actual Redblack Ops and traversal for all three carriers, plus the four raw counterexamples |
| `main` | `List String → IO UInt32` | Exact three-command dispatch, checked compressed JSON and established stderr/exit protocol |

Nine unchanged declaration chunks (`readKeyFile`, `generatedKey`, `workload`, `wordAdditionCase`, `wordBoundaries`, `comparisonCases`, `stableSortCase`, `finiteSortCase`, `natSortCase`) were also byte-compared against the preceding driver. The complete current source, including the shared generic sample/table bodies and new private observers, was read as current code. Record constructors, projections, pattern matchers and compiler closures are generated declarations; they are not extra authored algorithms. A retained no-output probe imported the freshly built `ExtractSearchTree.olean` and used `Lean.getConstInfo` for every authored row, plus the configuration constructor and twelve projections. Record `18b-current-types/result.json` completed with exit 0 in 3.621 seconds and unchanged watched inputs. Every authored declaration has an empty universe-parameter list, matching the universe-zero executable binders above. The private-name prefix is `_private.ExtractSearchTree.0.ExtractSearchTree.`. The earlier probe `18-current-types` returned exit 1 because its optional `pp.width` display setting is unsupported; its actual output is retained. Removing only that probe setting resolved the failure without changing the driver or imported module.

## 6. Development tests and retained failures

Tests invoke the actual public driver and the public `--check-receipt FILE` observer. No source operation is mocked, and no test calls private Lean definitions. The first small case's expectation was stated before implementation: after keys 0 through 6, the source rotations produce black root 3, black children 1/5 and black grandchildren 0/2/4/6; key 7 becomes the red right child of 6. Therefore N = 8, height = 4, black height = 3 and every query hits. The Python expectation is literal, without a copied insertion algorithm.

The original checkpoint041 runtime records bound actual commands, source/configuration identities, streams, exits and durations. The following names are historical external record identifiers, not repository files or a claim that old raw paths remain accessible. Their substantive semantic/regression observations are retained here and in the maintained driver/test owners; [CTB-93](../textbooks/CTB.json) owns their original qualification. In particular:

| Record | Actual purpose and result |
| --- | --- |
| `01-red/command.json` | Public eight-key Redblack command failed on the unchanged driver: unknown `--realization`; exit 1 |
| `02-elaborate-first/result.json`, `03-green/command.json` | Retained no-output elaboration succeeded; the same public first test passed after implementation |
| `04-observer-red/command.json`, `05-observer-green/command.json` | Actual schema-2 workload initially rejected by the old schema-1-only observer, then accepted together with ordinary defaults |
| `06-signed-red/command.json`, `07-elaborate-signed/result.json`, `08-signed-green/command.json` | New Redblack example command initially absent; actual elaboration and signed/default/suffix behavior then passed, with the complete ordinary example observer |
| `09-invariants-red/command.json`, `10-invariants-green/command.json` | Public counterexample field initially missing; the four literal observations and required-valid rejections then passed |
| `11-shared-replay/command.json` | Eight actual direct driver runs and their public observers passed for four identical-file comparison pairs |
| `12-source-comparison/command.json` | Four actual direct driver runs and their public observers passed for random/consecutive source-mode pairs |
| `13-observer-corruption/command.json` | Twenty-seven malformed or false tree variants rejected, including coherently reported red-root and unequal-black-height failures; schema-1 format compatibility passed |
| `14-redblack-parser-range/command.json` | Unsupported/duplicate realization, extra example argument and both carriers' adjacent out-of-range file inputs rejected |
| `15-redblack-endpoints/command.json` | Actual empty Int, singleton word63 with one miss, and singleton Int64 cases and their independent observers passed |

The early failed commands are retained as failures of their actual earlier source snapshots. The signed counterexample test's later public-observer routing replaced an initially unreachable direct observer call after its real missing-field failure; its independent expectations did not change. Tests that already passed for the generalized implementation are regression evidence, without manufactured RED failures.

The final ten added methods cover the eight-key shape, workload observer acceptance, signed/default/suffix example, invariant counterexamples, controlled same-file pairs, fresh-query source pairs, empty/singleton/miss cases, parser/range rejection, schema-1 compatibility and structural tampering. The unchanged test names retain all earlier sort, comparison, overflow, replay, generator, repetition and malformed-observation coverage. Full 36-test executions in both modes are an external final-candidate obligation and are not inferred from these selected development tests.

## 7. Bounded direct observations

The direct comparison batches used the current driver hash above. Their harness was the 71,584-byte development snapshot, SHA-256 `c1bd1dd6b44c356208405075096c71ef39a2c55e0a0a24f81a3a119656d38ce6`; subsequent additions supplied further observer/parser/endpoint regression coverage. The final harness identity is stated separately at the beginning of this note. Source/configuration snapshots are retained with each actual batch. Neither a later harness hash nor historical checkpoint 039 executable identity is substituted for the artifact that ran.

Every row below has one recorded warmup followed by two measured repetitions; all samples rebuild the selected tree. Times are the raw query intervals in **nanoseconds**, ordered **warmup, measured 0, measured 1**. Counts, optional results, entries and shape invariants agreed with their independent observers for every sample. The whole direct batch process durations were 45.259 seconds for controlled replay and 20.010 seconds for source comparisons; those include repeated script launches/elaboration and are not query times.

### Controlled identical-file comparisons

| Inputs | Realization | Distinct nodes | Height | Hits | Raw elapsed ns |
| --- | --- | --- | --- | --- | --- |
| Int64 ascending 0..127; 131 queries | Ordinary | 128 | 128 | 129 | 6,676,203; 6,596,825; 6,526,310 |
| Same files | Redblack | 128 | 8 | 129 | 3,620,372; 602,257; 592,833 |
| Int pinned random-derived replay; 8 writes / 8 queries | Ordinary | 4 | 3 | 2 | 36,594; 37,425; 15,573 |
| Same files | Redblack | 4 | 3 | 2 | 43,534; 13,139; 11,637 |
| Word63 signed endpoints; 6 writes / 6 queries | Ordinary | 5 | 4 | 5 | 55,421; 30,064; 24,706 |
| Same files | Redblack | 5 | 3 | 5 | 54,420; 28,883; 23,044 |
| Int64 signed endpoints; 6 writes / 6 queries | Ordinary | 5 | 4 | 5 | 37,045; 11,587; 10,675 |
| Same files | Redblack | 5 | 3 | 5 | 41,341; 17,456; 9,844 |

The 131 queries are `0..127, -1, 128, 64`: 129 hits and two misses. The random-derived lists are inserted `[10,0,10,11,6,10,0,0]`, queried `[9,7,4,11,1,8,11,8]`. They are a stored replay from the pinned Lean stream, not freshly generated timed random queries. The endpoint files insert `[min,3,-3,max,0,-3]` and query `[min,max,0,-1,-3,3]`, with the appropriate exact signed minimum/maximum. Every stored value is 1 and every query default is 0.

Each pair uses the same two file paths and bytes, carrier, values, defaults, sample counts and validation. The harness checks the bytes after each realization, while invocation records retain their actual copies and hashes. File parsing and encoding are outside both query timers. SHA-256 identities of those exact newline-terminated input files are:

| Pair | Insertion file bytes / SHA-256 | Query file bytes / SHA-256 |
| --- | --- | --- |
| Int64 consecutive | 402 / `1abb39224f6060360f5496650d517647668639c968d65a54baa4fefe032fb6e9` | 412 / `9ad1a2e5671ff196b59bd5238c0ff5922aa9203cd4ad72c0271fc30e4e306944` |
| Int random-derived | 20 / `3b63074c5cb53f104667cde68221ebd2846b11f3a8dcf56951fa5bd921fd51f3` | 18 / `c8c5871f6bf487a248dc225522f8a913888b5f69a59fe634259bc2332e0f0bd0` |
| Word63 endpoints | 51 / `42c6508b0bff78db4f307114939cdfe643d7bc449a4a233e18a8ae18d98a2de6` | 51 / `44bc08e2f96c7009d5ec009fe7ad89ea383b9613338cb471fde1402a709c135f` |
| Int64 endpoints | 51 / `7f22537f1ca6401b755f57bcf28c9cfadafab8aa26d226d2f19162abe2307ae7` | 51 / `d0204d3eeacb3944901d70b33a11838a92cd178ac30d5ba956d4269eb558904a` |

### Source-shaped fresh-query comparisons

All four commands used Int64, N = Q = U = 32, seed 1729, one warmup and two measured repetitions. Both realizations produced identical inserted/query lists and generator states for the corresponding pattern. Random queries were generated inside the measured loop; their full lists were captured by validated replay afterward.

| Pattern | Realization | Distinct nodes | Height | Hits | Raw elapsed ns |
| --- | --- | --- | --- | --- | --- |
| Random | Ordinary | 17 | 7 | 17 | 152,995; 113,597; 111,184 |
| Random | Redblack | 17 | 6 | 17 | 204,541; 115,170; 106,517 |
| Consecutive | Ordinary | 32 | 32 | 32 | 659,391; 408,422; 407,089 |
| Consecutive | Redblack | 32 | 6 | 32 | 197,941; 172,724; 157,331 |

These actual finite shape differences do not imply an exact timing ratio. The small raw values vary across samples, and no claim that either Lean path is uniformly faster follows from them. The two timing modes are distinct experiments and must not be pooled as measurements of one region.

A read-only host observation after the direct endpoint batch recorded Linux 6.18.57 on x86_64, Python 3.12.14, and the exposed AMD EPYC 9V74 80-Core Processor model. The established profile selected native mode and verified exact tool binaries; its Lean executable identity is `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`. The profile/host observation is retained with an explicit timestamp and its limited after-the-batch attribution. The final execution receipts must provide their own host and artifact binding. No CPU, memory, thread, affinity or elapsed-time caps were introduced for these tests.

## 8. Historical standalone build, generated paths and compiled observations

The historical parent-owned development command `lake --no-cache --rehash build extract-searchtree` completed with exit 0 in 11.272 seconds through the exact-pin native profile. Its record `16-standalone-build/command.json` binds 51 unchanged watched inputs and a recursively derived 47-file project import closure **including the driver**. Configuration and external dependency pins are recorded separately from that source count. A future collector that counts imported owners while excluding the driver must report its own honestly derived count.

| Historical development artifact | Bytes | SHA-256 |
| --- | --- | --- |
| Generated `ExtractSearchTree.c` | 1,112,198 | `d436da981b668ca139dbfa3773eecad0206e24fa7d7a955ba902eeb0d4d927ec` |
| Imported `ExtractSearchTree.olean` | 2,545,536 | `9884d72086bee8241fa7261e2ac346a7fd07cda895cba985d332a8e7df742abc` |
| Standalone `extract-searchtree` | 135,571,968 | `533d1e925eb87c4bef548e90a05c732bf9d9c6f3a05b0ec1a01b32d919a7bcf4` |
| Generated `Search/RedBlack/Basic.c` | 53,672 | `88048946c45e1dceb2a6082281aa44171ee9cd7f4341da05e23e6f95e952af29` |
| Generated `Search/RedBlack/Models.c` | 18,078 | `6dc760631e004816fbf59519fa21535f20630960c125766f7c7f634e677b116e` |
| Generated `Representations/SignedComparison.c` | 29,856 | `b6b2894ac473f25461295a726e8fa1e4c59b3c4e14d20532f6329a08fc27b70a` |

Read-only `file` and `readelf -h` inspection identifies the actual binary as a dynamically linked x86-64 ELF64 position-independent executable, with debug information and interpreter `/lib64/ld-linux-x86-64.so.2`. The complete selected C copies, command stdout/stderr and before/after artifact hashes are retained under `19-generated-inspection/`. All five file/header/disassembly commands returned 0 and their observed inputs remained unchanged. These hashes are new development artifacts; the older Extract note's generated C and ELF are not relabeled as this build.

### Selected generated computational closure

The generated `workloadFor` sample loops select actual `Search_RedBlack_ops` when the realization string is `redblack`, supply the actual provider `toList` closure, and supply `redblackTreeObservation` with required-valid true. The alternate branch supplies `DecodedKeys_ops`, the existing ordinary traversal and its ordinary observer. Both call the same generated `workloadSampleFor` function.

`RedBlack.Models.c` constructs the Ops record with nil, a closure over `Search_RedBlack_insert`, and a closure over `Search_RedBlack_lookup?`. In `RedBlack.Basic.c`, the compiled optional search tests query/pivot first, pivot/query only after failure, then returns the stored binding or descends into the selected child. The inspected `ins` branches recursively obtain the actual child result and pass it to the full source `balance`; equality replaces the original key and payload. `insert` calls that `ins` and then the provider's `setBlack`. The complete generated `balance` body retains the red bypass and LL/LR/RL/RR/fallback priority. Its compiler factoring is not a statement that source-level pattern-attempt counts equal machine instructions or physical allocations.

The current driver C's `workloadSampleFor___redArg` has the following concrete control flow. These join/closure names belong only to the generated file identified above:

| Generated path | Observed computation |
| --- | --- |
| `lam__3`, passed through `v___jp_2119_` to `v___jp_2030_` | Actual `Workload.sourceWrites`, then `OrderedMap.bindAll` from the selected empty state |
| `v___jp_2030_` | Forces that build through `l_IO_lazyPure___redArg` before the first clock; allocates query/shape closures without evaluating shape |
| `v___x_2049_`, query `lam__5`, then `v_resetjp_2052_` / `v___x_2055_` | First monotonic clock, forced selected query loop, second monotonic clock |
| Query `lam__5` controlled branch | Prepared-query fold, Ops lookup field 2, optional default 0 and consumed hit count |
| Query `lam__5` source branch | Actual `sourceQueries`; schedule construction and `generatedKey` occur inside its fold, followed by range/round-trip checks and the same Ops lookup field |
| Source branch after `v___x_2055_` | Forces the query-list replay, compares both state fields, checks replay range/round trip, then joins `v___jp_1956_` |
| `v___jp_1956_`, model `lam__6` | Actual separate HashMap construction, full optional lookup/enumeration checks and consumed-hit validation, after the second clock |
| Shape `lam__4`, called after successful model checking | Calls the selected actual observer; Redblack observer calls eraseColors, the bound checker, separate color/black-height checks, and provider size/depth |
| Final JSON join | Packages verified fields and subtracts the recorded clocks; does not supply an invented elapsed time |

This establishes the selected generated-C calls and their control-flow order. It is not a proof of the downstream compiler, its optimizations or general runtime scheduling. The fixed Int64 comparison closure in this exact ELF contains signed `setl`/`setle` comparisons in its retained boxed wrappers. The BitVec signed comparison instead calls `l_BitVec_toInt` on both operands, with the ordinary Int comparison path afterward. These observations confirm the intended signed computational paths while retaining their different representation costs.

### Actually executed compiled counterparts

The historical record `17-compiled-comparison/command.json` describes a command that selected the freshly identified absolute executable through `EXTRACT_TEST_COMMAND_JSON` and invoked the same public controlled-pair, source-pair and signed/default/suffix test methods. It passed all three methods, exit 0, with unittest duration 1.936 seconds and wrapper duration 2.091 seconds. All watched sources, configuration and the binary remained unchanged. This batch used the final 79,598-byte harness hash stated at the beginning of this note.

The batch contains thirteen successful driver invocations and thirteen successful public observer invocations: eight controlled runs, four source runs, and the complete three-carrier Redblack example. Each workload again has one warmup and two measured repetitions, with raw query nanoseconds ordered warmup, measured 0, measured 1. The exact twelve compiled workload records were compared with the twelve direct records: **every sample field except `elapsedNs` matched**, including the full preorder stream, and every replay-file byte count/hash matched. The compiled example also passed the independent literal stored-zero/miss, replacement, suffix, empty and invariant-counterexample expectations.

| Controlled inputs | Realization | Height / nodes / hits | Raw compiled elapsed ns |
| --- | --- | --- | --- |
| Int64 consecutive, 128 writes / 131 queries | Ordinary | 128 / 128 / 129 | 98,836; 199,343; 96,953 |
| Same stored files | Redblack | 8 / 128 / 129 | 13,379; 12,058; 11,357 |
| Int random-derived replay, 8 / 8 | Ordinary | 3 / 4 / 2 | 1,802; 550; 440 |
| Same stored files | Redblack | 3 / 4 / 2 | 1,542; 511; 501 |
| Word63 signed endpoints, 6 / 6 | Ordinary | 4 / 5 / 5 | 16,855; 17,556; 13,891 |
| Same stored files | Redblack | 3 / 5 / 5 | 11,497; 10,336; 10,355 |
| Int64 signed endpoints, 6 / 6 | Ordinary | 4 / 5 / 5 | 1,903; 601; 481 |
| Same stored files | Redblack | 3 / 5 / 5 | 1,662; 621; 731 |

| Source pattern, Int64 N = Q = U = 32, seed 1729 | Realization | Height / nodes / hits | Raw compiled elapsed ns |
| --- | --- | --- | --- |
| Fresh random | Ordinary | 7 / 17 / 17 | 8,813; 6,740; 5,809 |
| Fresh random | Redblack | 6 / 17 / 17 | 8,212; 5,878; 5,908 |
| Consecutive | Ordinary | 32 / 32 / 32 | 10,326; 47,650; 8,312 |
| Consecutive | Redblack | 6 / 32 / 32 | 6,380; 4,316; 4,516 |

The raw variation is retained, including the larger second ordinary consecutive source interval. No outlier deletion, performance threshold, ratio theorem, claim of uniform native advantage, or extrapolation to the large named recipes is made. The direct and compiled suites exercise the same semantics, but their launch and evaluation costs are different; the full candidate-bound dual-mode suite remains a separate acceptance gate.

## 9. Source configurations and historical observations

The named source configurations remain reproducible recipes: random 1,000,000, random 20,000 and consecutive 20,000. None of those larger Redblack comparison recipes was executed in the bounded development observations above. They are not replaced by the tested 8-, 32- or 128-key cases. For each selected realization, for example:

```sh
.lake/build/bin/extract-searchtree workload --realization redblack --carrier int64 --pattern random --timing source --size 1000000 --queries 1000000 --universe 1000000 --seed 1729
.lake/build/bin/extract-searchtree workload --realization redblack --carrier int64 --pattern random --timing source --size 20000 --queries 20000 --universe 20000 --seed 1729
.lake/build/bin/extract-searchtree workload --realization redblack --carrier int64 --pattern consecutive --timing source --size 20000 --queries 20000 --universe 20000 --seed 1729
```

Use `--realization ordinary` for the corresponding ordinary commands. The direct launcher accepts the same arguments. These recipes use the source-shaped query region and actual Lean generator; controlled comparisons instead require retaining one identical insertion/query pair and passing both files to both realizations. No maximum workload or artificial resource cap is inferred from the bounded selection.

The source reports the following Redblack observations on a 2.9 GHz Intel Core i9, in seconds:

| Source workload | OCaml bytecode reported seconds | OCaml native reported seconds |
| --- | --- | --- |
| Random 1,000,000 | 0.860663 | 0.475669 |
| Random 20,000 | 0.007908 | 0.00312 |
| Consecutive 20,000 | 0.004668 | 0.001183 |

Those are historical measurements printed in `Redblack.v`, not executions performed here, Lean predictions, asymptotic theorems, or reproducible cross-language seed matches. The source's qualitative random/consecutive conclusions are attributed to those observations. The accepted structural height theorems explain why a balanced search path admits logarithmic bounds under their stated invariants; actual wall-clock behavior additionally depends on representation, comparison cost and runtime implementation.

## 10. Acceptance boundary

Current receiving receipts must bind the actual integrated candidate, compiler/pins/configuration and relevant execution inputs. Required public behavior and independent observation checks must run on the selected executable; failures and unknown outcomes remain distinct from passes. Preserve concise current result/input identities in [CTB-78](../textbooks/CTB.json). Detailed working evidence may remain external while needed for review, without perpetually embedding older type exports, logs or envelopes. The historical checkpoint039 source/C/ELF and checkpoint040 proofs remain attributed to their actual bytes and do not certify the receiving candidate.

This runtime correspondence is one part of the complete Redblack chapter obligations. It does not by itself qualify the source chapter, establish the measured resource recurrences, verify Lean's compiler, prove constant-space behavior or guarantee a native performance ordering. Separate pure and measured-resource statements must satisfy their own full statement review and exact-candidate proof-audit gates.
