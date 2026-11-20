# VFA Extract: executable programs and runtime evidence

Historical observation scope: measurements, generated-code inspections and
receipt identifiers below describe the original CTB-91 donor increment at the
source/artifact hashes stated. They are not observations of the current receiving
tree. Old external filenames identify historical records; their current availability
is not inferred from a path or a hash. The retained source/test owners provide
reproducible behavior; [CTB](../textbooks/CTB.json) records CTB-91 attribution
and CTB-78 receiving status. Any new receiving result must bind its actual inputs.

**Historical checkpoint 039 assessment.** The source, generated C, ELF and development observations identified below belong to their explicitly hashed checkpoint 039 artifacts. The current shared driver adds the Redblack realization and schema-2 workload observations, documented in [VFA Redblack runtime evidence](vfa-redblack-runtime.md). The historical identities and observations below are preserved; they are not claims about execution of the current driver.

This note connects the thirteen extraction commands in VFA 2.1 `Extract.v` to the actual Lean programs in [ExtractSearchTree.lean](../../scripts/ExtractSearchTree.lean), their executable dependencies, and the public runtime observations. The client reuses the proved sorting and ordinary binary-search-tree adapters. It supplies argument handling, reproducible workloads, independent result checks, timing, and JSON output.

## Assessment status and source identity

The complete 536-line driver was independently read at SHA-256 **`50b329f2155ce378b5e71b2be2396b57b2cbf8f71014ba1a8cffd133581e5795`**, 30,113 bytes. Its sixteen private function bodies, private configuration record, and public `main` are assessed below. No concrete source defect was found in the supplied comparison paths, range checks, model checks, source/controlled timing boundaries, or repetition behavior.

**This version records complete driver-source assessment, inspection of the selected generated computational closure, an identified native ELF, and retained bounded compiled smoke results.** Section 8 identifies those observed development artifacts. The final full suites in both launch modes and exact-candidate acceptance remain obligations of the external checkpoint receipts. Those receipts must bind the accepted source/configuration, generated files, executable, commands, and results; no candidate commit is asserted inside this document. Recipes and expected examples below are not additional execution claims. Inspection and bounded execution do not establish compiler correctness, general native scheduling correctness, or an asymptotic performance theorem.

Source references are the versioned [VFA 2.1 Extract chapter](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Extract.html), its `Extract.v` (393 lines, SHA-256 `c132273a13fafe176573469e664b9cbe8dd3366ec00e2f9a3ab8ab1d42a2e15d`), and its 24-line `test_searchtree.ml` (SHA-256 `109e94b84632608b05e2c00081e98b2050a05dd9c5180241aa70486e7620e279`). The [canonical local Extract requirements](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1011-Extract.md) preserve the source inventory and the mathematical/runtime boundaries. Session instructions govern current environment and acceptance procedures where older planning instructions differ.

The selected toolchain is `leanprover/lean4:v4.35.0`; the inspected manifest pins Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`. Final execution evidence must bind these to the actual compiler, source, configuration, generated files, and binary used.

## 1. The two launch paths

Run from the repository root in its established environment. The direct route is:

```sh
lake env lean --run scripts/ExtractSearchTree.lean examples
lake env lean --run scripts/ExtractSearchTree.lean workload
```

This route elaborates the script and invokes Lean's direct runner. The pinned `Lean.Shell.runMain` declaration describes interpreter execution. It is not evidence that the separate standalone executable has been built or run. Imported runtime primitives retain their normal implementation and trust boundary.

The selected ordinary Lake executable configuration is:

```toml
[[lean_exe]]
name = "extract-searchtree"
root = "ExtractSearchTree"
srcDir = "scripts"
```

This entry is present in the inspected 722-byte `lakefile.toml`, SHA-256 `4a02b9bfe546ecee0a4cb5070f75939bac510c1b412315490a4ff854fb57db81`. The retained target test first failed with `unknown target`, then the actual target build passed after the entry was added, with the driver unchanged. Section 8 records the development build and executable identities. Ordinary build/run recipes are:

```sh
lake build extract-searchtree
.lake/build/bin/extract-searchtree examples
.lake/build/bin/extract-searchtree workload
```

The target uses the same `main` and local dependency closure. It does not need `supportInterpreter = true`: that Lake option exposes symbols for programs that themselves interpret Lean files, and its pinned default is false. A successful compiled-mode claim requires the actual binary, identified as a native ELF and hashed, followed by successful invocations of that file. A compiler invocation or the existence of generated C alone is insufficient.

The [public Python harness](../../scripts/test-extract-searchtree.py) uses the actual launch argv. Its default prefix is the direct route; `EXTRACT_TEST_COMMAND_JSON` selects the compiled binary for the same public semantic suite. The final completed harness can be invoked as:

```sh
python3 -B scripts/test-extract-searchtree.py
EXTRACT_TEST_COMMAND_JSON='[".lake/build/bin/extract-searchtree"]' python3 -B scripts/test-extract-searchtree.py
```

The harness's whole-process monotonic duration is distinct from each driver's query interval. Launch mode belongs to the external invocation record, not a self-asserted field in driver JSON. The established host profile is native; any final host/backend evidence must describe the environment actually used.

## 2. Public command and record contract

`main (args : List String) : IO UInt32` accepts `examples` with no further arguments, or `workload` followed by option/value pairs. Success prints exactly one compressed JSON object on stdout and returns 0. A malformed top-level command prints usage on stderr and returns 2; handled parser, file, range, replay, or result-check errors print an error on stderr and return 1. No successful JSON receipt is emitted after a failed check.

### Workload options

| Option | Accepted value / default | Meaning |
| --- | --- | --- |
| `--carrier` | `int`, `word63`, `int64`; default `int64` | Selects the actual key representation and supplied signed comparison. |
| `--pattern` | `consecutive`, `random`, `replay`; default `consecutive` | Selects generated ascending prefixes, explicit-state random keys, or input files. |
| `--timing` | `controlled`, `source`; default `controlled` | Selects the measured query region described in section 5. |
| `--size` | Nat; default 32 | Number of generated insertion keys. |
| `--queries` | Nat; default 32 | Number of generated queries; source timing requires this to equal size. |
| `--universe` | Nat; default 32 | Random keys use `[0,U-1]`. It does not constrain consecutive keys. Internally named `rangeSize`. |
| `--seed` | Nat; default 1729 | Argument to `mkStdGen`, reset for every sample. |
| `--warmups` | Nat; default 0 | Number of recorded warmup samples before measured samples. |
| `--repetitions` | Positive Nat; default 1 | Number of recorded measured samples. |
| `--inserted-file` | Path; absent by default | Replay insertion keys, one signed decimal Int per line. |
| `--queries-file` | Path; absent by default | Replay query keys in their supplied order. |

Unknown, repeated, missing-value, unsupported, or invalid numeric options fail. Replay requires both files, uses controlled timing, derives counts from the files, and rejects explicitly supplied `--size`, `--queries`, `--seed`, or `--universe`. File options are rejected for other patterns. A positive random draw count requires `U > 0`; an entirely empty random workload with `U = 0` makes no draw. `--repetitions 0` fails. No duration, memory, thread, or performance threshold is imposed by the driver.

Replay files are read once before sampling. Each line is parsed with `String.toInt?`; a malformed line reports its file and one-based line number. Samples rebuild from the same retained immutable lists. Each generated sample starts from `mkStdGen seed` and generates its own reproducible insertion/query sequence. Repetitions do not advance one shared generator between samples.

### Successful JSON

The schema version is 1. `examples` returns kind `examples` with `sortZ`, `sortZBoundary`, `natSort`, `finiteSort`, `stableSort`, `comparisons`, `fourBitComparison`, `tables`, and `wordBoundaries` observations. These fields contain actual returned values checked before printing.

`workload` returns kind `workload`, `config`, `clock`, `unit`, `timedRegion`, and `samples`. Configuration records every selected setting; replay's seed and universe are null, its file paths are retained, and its counts are the actual parsed list lengths. Each sample contains:

- Phase `warmup` or `measured` and a zero-based index within that phase.
- Exact original insertion and query key lists; actual canonical entries and optional query results.
- The timed return `hits`, independently calculated `expectedHits`, and reference-map distinct size.
- The observed nonnegative `elapsedNs`, with clock `IO.monoNanosNow` and unit `ns`.
- Generator name `StdGen/mkStdGen/randNat`, initial/post-build/post-query two-Nat states, and logical build/query key-draw counts; replay uses null.

Signed keys are decimal strings in JSON so a consumer need not round large keys through a floating-point number. Payloads, counters, and generator states are natural numbers. An optional payload is a Nat or null. All warmup records precede all measured records. The record claims no build duration. The recorded draw counts count calls requesting keys through `randNat`, not its potentially multiple internal `stdNext` steps.

## 3. Every driver declaration and its executable dependencies

All declarations below except global `main` are private in namespace `ExtractSearchTree`. There are sixteen private functions and one private record; no additional user-authored theorem, axiom, unsafe definition, or replacement tree/sort algorithm is introduced by this script. Record constructors, projections, and compiler-generated closures arise from these declarations and are not separate source algorithms.

`WorkloadConfig : Type` has String fields `carrier`, `pattern`, `timing`; Nat fields `size`, `queries`, `rangeSize`, `seed`, `warmups`, `repetitions`; and `Option String` fields `insertedFile`, `queriesFile`. Their defaults are listed above. For the signature table only, `Cfg` denotes this exact record, `Json` denotes `Lean.Json`, and `Tree W` denotes `BinaryTree (W × Nat)`. These are explanatory abbreviations, not new code.

| Source declaration | Actual type, with the stated abbreviations | Executable body assessment |
| --- | --- | --- |
| `parseWorkloadOptions` | `List String → Cfg → List String → Except String Cfg` | Recurses over option/value pairs; tracks seen flags; uses `String.toNat?`; performs all cross-option conditions at the end. The public caller supplies defaults and an empty seen list. |
| `readKeyFile` | `String → IO (List Int)` | `IO.FS.readFile`, line iteration with indices, `String.toInt?`, and explicit failure. It neither converts to finite keys nor invokes a tested algorithm. |
| `generatedKey` | `Cfg → Nat → Nat → StdGen → Except String (Int × StdGen)` | For random, checks positive U, calls pinned `randNat state 0 (U-1)`, checks `< U`, and returns the new state. Otherwise returns `count-index` as Int and preserves state. The public path calls the nonrandom branch only for generated consecutive workloads. |
| `generatedKeys` | `Cfg → Nat → StdGen → Except String (List Int × StdGen)` | Folds `Workload.sourceIndices count`, threads `generatedKey`, accumulates in reverse, then reverses once. The returned list is chronological. |
| `sourceQueries` | `∀ {W : Type}, Cfg → (Int → Bool) → (Int → W) → (W → Int) → (W → W → Bool) → Tree W → StdGen → Except String (StdGen × Nat)` | Creates/traverses the descending query schedule, generates each key from the post-build state, checks range before encoding and checks round trip, calls actual `DecodedKeys.lookup`, and retains only state and hits. |
| `workloadSampleFor` | `∀ {W : Type}, Cfg → Option (List Int × List Int) → String → Nat → (Int → Bool) → (Int → W) → (W → Int) → (W → W → Bool) → IO Json` | One fresh sample: inputs, conversion, shared chronological tree build, clock/query/clock, optional source replay, independent HashMap/enumeration/query validation, then JSON. |
| `workloadFor` | `∀ {W : Type}, Cfg → (Int → Bool) → (Int → W) → (W → Int) → (W → W → Bool) → IO Json` | Reads replay inputs once; runs indexed warmups and measured repetitions sequentially; packages configuration, region, and all sample records. |
| `workload` | `Cfg → IO Json` | Selects Int/BitVec63/Int64 and their actual signed comparators. Checks finite consecutive count capacities and random-universe capacities before schedule generation. |
| `wordAdditionCase` | `Int → Int → Int → Bool → IO Json` | Parameters are left/right/expected sum/expected overflow. Checks both four-bit input ranges before `BitVec.ofInt 4`, executes addition and `saddOverflow`, and checks both actual observations. |
| `wordBoundaries` | `IO Json` | Executes overflowing 7+1 and safe 2+1; deliberately demonstrates width-zero collapse/replacement through actual comparisons, tree operations, and traversal. |
| `tableCase` | `∀ {W : Type}, String → (Int → Bool) → (Int → W) → (W → Int) → (W → W → Bool) → IO Json` | Checks signed input/round trips, executes chronological writes, optional queries, two caller defaults, enumeration with/without suffix, and empty observations against fixed independent expectations. |
| `comparisonCases` | `∀ {W : Type}, String → Int → Int → (Int → Bool) → (Int → W) → (W → Int) → (W → W → Bool) → (W → W → Bool) → IO Json` | Parameters include minimum/maximum and strict/nonstrict comparisons. Executes five signed less/equal/greater/endpoint pairs after validation. |
| `stableSortCase` | `∀ {W : Type}, String → (Int → Bool) → (Int → W) → (W → Int) → (W → W → Bool) → IO Json` | Executes the existing generic sort on `(key,String)` pairs, comparing keys only, and checks original labelled records in stable order. |
| `finiteSortCase` | `∀ {W : Type}, String → Nat → Int → Int → (Int → W) → (W → Int) → (W → W → Bool) → IO Json` | Parameters are carrier/width/minimum/upper-exclusive/encode/decode/leb. Executes the source sort on signed extremes, negative repeats, and zero after full range and round-trip checks. |
| `natSortCase` | `List Nat → List Nat → IO Json` | Executes the actual Nat sort and compares its returned list with the supplied independent expectation. |
| `examples` | `IO Json` | Runs all Nat/Int/finite sorting, labelled ties, comparison, table, and word-boundary cases; adds the signed/unsigned four-bit disagreement. It prints no partial success record. |
| Global `main` | `List String → IO UInt32` | Dispatches the two public subcommands, prints checked compressed JSON, and reports controlled failures on stderr with the exit codes specified above. |

The complete source was re-read after freezing. As an additional change check, the `wordAdditionCase`-through-`main` suffix is byte-for-byte unchanged from the earlier 431-line development snapshot. The generated/source workload and repetition bodies were assessed as new/changed bodies, not inferred from that earlier review.

An independent `lean --stdin` probe imported the built module and used `Lean.getConstInfo` for every row; it completed with exit 0 without requesting any output module. The exact private-name prefix is `_private.ExtractSearchTree.0.ExtractSearchTree.`. All generic `W` binders above are `{W : Type}` at universe zero. This reproduces the signature inspection in the established toolchain environment:

```sh
lake env lean --stdin <<'EOF'
import ExtractSearchTree
open Lean
set_option pp.universes true
#eval show CoreM Unit from do
  let names := ["WorkloadConfig", "parseWorkloadOptions", "readKeyFile",
    "generatedKey", "generatedKeys", "sourceQueries", "workloadSampleFor",
    "workloadFor", "workload", "wordAdditionCase", "wordBoundaries", "tableCase",
    "comparisonCases", "stableSortCase", "finiteSortCase", "natSortCase", "examples"]
  for shortName in names do
    let n := ("_private.ExtractSearchTree.0.ExtractSearchTree." ++ shortName).toName
    let info ← getConstInfo n
    logInfo m!"{n} : {info.type}"
  let info ← getConstInfo `main
  logInfo m!"main : {info.type}"
EOF
```

### Actual algorithm closure

| Operation | Existing callable chain |
| --- | --- |
| Nat sort | [`ExtractedPrograms.sort`](../../Examples/ExtractedPrograms.lean) → [`InsertionSorting.sort`](../../Examples/InsertionSorting.lean) → `List.insertionSort (· ≤ ·)` → `List.foldr (List.orderedInsert ...) []`. `orderedInsert` inserts before ties. |
| Int/finite/labelled sort | `ExtractedPrograms.sortZ` or `sort_int` → [`DecodedInsertion.sort`](../../Applications/Sorting/DecodedInsertion.lean), which calls the same list insertion sort using the supplied Boolean comparison. Labels remain ordinary data, and only projected keys are compared. |
| Chronological build | [`bindAll`](../../Applications/Search/OrderedMap/Interface.lean) with [`DecodedKeys.ops ltb`](../../Applications/Search/OrderedMap/DecodedKeysModels.lean) and [`Workload.sourceWrites`](../../Applications/Search/OrderedMap/Workload.lean). `ops.bind` is exactly `DecodedKeys.insert ltb`; each actual returned tree is passed to the next write. |
| Insert and optional lookup | [`DecodedKeys`](../../Applications/Search/OrderedMap/DecodedKeys.lean) supplies its Boolean relation/decision to existing [`OrderedMap.bind/lookup`](../../Applications/Search/OrderedMap/Basic.lean). Query/pivot is tested first, pivot/query second; equality returns/replaces the payload. |
| Default lookup | `DecodedKeys.lookup` applies `Option.getD default` to the actual optional search. `Examples.ExtractedTrees.lookup` is this adapter. |
| Enumeration | [`ExtractedTrees.elements/elements_aux`](../../Examples/ExtractedTrees.lean) → `DecodedKeys.elements/elementsAux` → [`fastEntries/fastEntriesAcc`](../../Applications/Search/OrderedMap/Enumeration.lean) → [`Trees.fold`](../../Applications/Trees/Observations.lean). The arbitrary suffix is retained exactly. |
| Independent reference | `Std.HashMap Int Nat`, built with the original Int inputs and queried with original Int queries. Its DHashMap-backed insert/get?/size operations do not call the tested tree comparator, encoding, insertion, or lookup. |

These paths use ordinary Lean Bool, List, Prod, Nat, Int, and the existing tree datatype. No new list/pair representation, sorting implementation, search-tree implementation, extraction backend, or comparison axioms are introduced.

## 4. Signed carriers, erasure, and range validation

| CLI carrier | Actual key type | Input range and executable comparison |
| --- | --- | --- |
| `int` | `Int` | Unbounded mathematical integers; `SignedComparison.intLtb/intLeb` use ordinary signed Int decisions. |
| `word63` | `BitVec 63` | `−4611686018427387904 ≤ k < 4611686018427387904`; `wordLtb/wordLeb` call `BitVec.slt/sle`. |
| `int64` | `Int64` | `−9223372036854775808 ≤ k < 9223372036854775808`; `int64Ltb/int64Leb` explicitly select `Int64.decLt/decLe`. |

The actual definitions and reflection theorems are in [SignedComparison.lean](../../Applications/Representations/SignedComparison.lean). In the pinned core, `BitVec.slt/sle` compare `toInt` values internally. Thus a Boolean-only sort/tree API has no extra proof-decoder argument, but the BitVec comparator itself performs signed interpretation work. It must not be described as the native Int64 primitive. The inspected generated C selects `int64Ltb/int64Leb`, which call the pinned native overrides `lean_int64_dec_lt/le`; the runtime header casts their two `uint64_t` carriers to `int64_t` before comparing. In the identified ELF, the retained boxed wrappers contain signed `setl`/`setle` comparisons, while `l_BitVec_slt` calls `l_BitVec_toInt` for both inputs. These observations identify the delivered paths without making a constant-time claim about the wrappers, allocation, or surrounding algorithms.

Finite consecutive counts are checked against their positive capacities before allocating schedules: count may equal `2^62` for word63 or `2^63` for Int64 because the final key is count−1. Finite random universes have the same capacity bounds. Every actual original key is additionally checked before conversion, followed by a decoded round-trip check. Source timing performs those per-query checks inside the timed loop. Counters and workload sizes remain Nat and are not silently truncated to finite machine keys.

The width-zero example intentionally maps original `[-3,4,99]` to `[0,0,0]`; it is explicitly a modular-collapse counterexample, not a faithful-input conversion. Four-bit 7+1 has modular signed result −8 and mathematical sum 8; the safe 2+1 example yields 3. The four-bit comparison of −1 with 0 is true for signed less-than and false for unsigned `ult`. These observations expose the representability/overflow boundary behind the source's unsound-extraction warning.

Lean erases proof terms in `Prop`. A decoder or specification function used as `Type`-level data is executable unless actual dependency analysis shows otherwise. The sort/tree operation records take the supplied Boolean comparisons and original data, not reflection proofs or proof-only decoders. Decoding remains present where the driver validates and reports keys, inside source checked conversion, and inside the chosen BitVec comparator. Naming a function `Abs` or putting it in a `Squares.Square` is not an erasure argument. This repository's separately modeled compiler theorem does not verify Lean's compiler or its runtime overrides.

## 5. Workload and timing semantics

### What the source companion measures

The supplied ML program visits descending indices `n,n−1,…,1`, inserting payload 1 before reading `Sys.time`. Its timed loop generates a fresh `f j` at each query, uses default 0, and increments the result when lookup returns 1. The printed insertion-and-lookup label therefore overstates that interval, and the source printer discards the hit result. This driver retains and checks its hit result.

For consecutive `f j=n-j`, both lists are `0,…,n−1`. For random `f j=Random.int n`, insertion and query keys are separate draws from `[0,n−1]`; queries need not have been inserted, and duplicates reduce distinct size. The source's named `test_random n` is specifically **N=n insertion draws, Q=n queries, U=n**. An N=8/U=13 smoke is a useful generalized finite workload, not that named source specialization.

The Lean driver uses explicit local `StdGen` state with pinned `mkStdGen` and `randNat`. It does not use a shared `IO.rand` stream. `randNat` has inclusive endpoints, so positive U requests use `0` and `U−1`; the driver rejects the empty interval before drawing. Empty schedules make no call and preserve state. Logical key draws may require more than one internal core generator step. No equality with OCaml's PRNG bitstream or formal distribution theorem is asserted.

### Controlled region

The exact region label is:

> precomputed queries: traversal, lookup, hit count

Both original lists are prepared before the timer. Random queries continue the post-build generator state. All key range/round-trip checks, conversion, and the actual tree build finish before the first clock. The timed fold traverses the precomputed encoded query list, performs actual total lookup, and updates the hit count. The second clock precedes independent model construction, optional-query checking, enumeration, and JSON serialization. Controlled consecutive insertion and query counts may differ; their lists independently start at 0.

### Source region

The exact region label is:

> generated queries: descending schedule creation/traversal, key generation, checked conversion, lookup, hit count

Source mode requires Q=N. It generates and builds insertion keys before the timer, then starts query generation at the actual post-build state. Inside the timed `sourceQueries` call, it creates/traverses the descending schedule and performs each fresh key draw, range check, conversion, round-trip check, lookup, and hit update. It retains generator state and hit count, not a query-key list. The temporary index-schedule allocation is included in the interval and is an explicit Lean adaptation cost.

After the end clock, it deterministically replays the same query generator from the post-build state to recover exact keys. It checks replayed final generator state against the timed final state, validates replay keys and conversions, and compares the timed hit result with both the actual optional-query replay count and the independent reference count. The replay does not silently enter a query-only timing region. Source and controlled timing describe different experiments even when their non-timing observations agree.

Both regions use monotonic elapsed nanoseconds from `IO.monoNanosNow`, not the source's process CPU time. `IO.lazyPure` places the pure computation at the explicit IO sequencing points. The inspected generated C preserves build before start, the selected query work between clock calls, and replay/validation after end. Section 8 follows the actual closures and control-flow joins; it also records the ELF's `IO.lazyPure` thunk call. This is inspection of particular artifacts, not a proof about all compiler transformations or clock implementations.

### Sampling and independent validation

Every warmup and measured repetition starts at the recorded seed and rebuilds the tree. Replay files are read once and each sample uses the same immutable parsed lists. All samples are returned, with warmup/measured phases and indices; there is no hidden warmup deletion, retained tree between repetitions, cross-sample state advancement, or timing-based pass threshold.

After timing, the original insertion list builds an independent `Std.HashMap Int Nat`. Actual optional results are compared pointwise with that reference. The timed hit result must equal both the reference `some 1` count and the replayed actual optional `some 1` count. Canonical enumeration requires strict increasing decoded keys, length equal to reference distinct size, and matching reference bindings for every listed pair. Together those checks establish a complete distinct canonical listing for the observed workload; checking length or per-entry soundness alone would not suffice.

Separate table examples write `[(-3,7),(4,8),(-3,9),(0,0)]`. For queries `[-3,4,0,-1]` the required optional results are `[some 9,some 8,some 0,none]`, default-0 results `[9,8,0,0]`, and default-99 results `[9,8,0,99]`. Enumeration is `[(-3,9),(0,0),(4,8)]`, and `elements_aux` preserves suffix `[(99,123)]`. This distinguishes stored default from absence, unlike a single total-default observation.

## 6. All thirteen source-command correspondences

These mappings identify actual source bodies and checked runtime observations. A row's final execution qualification requires stable-source results in both direct and compiled modes and the generated dependency inspection. Multiple source directives intentionally share the same connected example; they do not require artificial duplicate executables. The inspected closure and bounded compiled smoke are recorded in section 8; the enclosing exact-candidate receipts decide final execution qualification for every row.

| Source line / directive | Actual Lean connection | Meaningful observed-result contract |
| --- | --- | --- |
| 40 — `Extraction sort` | `natSortCase` calls `ExtractedPrograms.sort`. | Actual Nat cases `[]→[]`, `[7]→[7]`, `[4,3,2,1]→[1,2,3,4]`, and `[3,1,3,0,1]→[0,1,1,3,3]`, retaining duplicates. |
| 47 — `Recursive Extraction sort` | The same specialization and actual `List.insertionSort`/`orderedInsert` dependency closure. | The Nat cases exercise the imported operation; section 8 identifies the built generated specialization and provider path. |
| 58 — native `bool` directive | Ordinary Lean Bool from actual signed comparison functions. | Less/equal/greater and min/max comparisons: strict `[true,false,false,true,false]`, nonstrict `[true,true,false,true,false]` for the driver's five pairs. |
| 59 — native `list` directive | Ordinary List in the existing sort, client schedules, queries, and traversal. | Empty, singleton, reversed, repeated, and labelled lists are actual inputs/results; no duplicate list datatype. |
| 60 — recursive sort after directives | Same Nat source sort using those ordinary datatypes. | Shares the independently checked Nat observations and actual closure with 40/47/58/59. |
| 86 — `Recursive Extraction sortZ` | `examples` calls `ExtractedPrograms.sortZ`. | `[-3,2,-3,0,1]→[-3,-3,0,1,2]`, empty, and `[-7]→[-7]`; generic correctness/stability remains a separate mathematical contract. |
| 114 — inline carrier `int` | Explicit Int, BitVec63, and Int64 specializations with guarded conversions. | Distinct carrier labels, finite endpoint round trips, signed examples, and rejected finite out-of-range inputs; no identification of finite keys with unbounded Int. |
| 127 — inline `ltb` as `<` | Supplied `intLtb`, `wordLtb`, or `int64Ltb` reaches actual tree branches and comparison cases. | Signed negative/equality/endpoints and the four-bit signed/unsigned disagreement. BitVec internal interpretation and Int64 native overrides remain distinct paths. |
| 131 — inline `leb` as `<=` | Supplied nonstrict comparator reaches `sort_int`, including projected-key comparisons on labelled pairs. | `[(2,"first"),(1,"middle"),(2,"last")]→[(1,"middle"),(2,"first"),(2,"last")]` for all three carriers. |
| 245 — `Recursive Extraction sort_int` | `finiteSortCase` and `stableSortCase` invoke the actual generic Boolean-only insertion sort. | Each finite carrier sorts `[-1,max,min,0,-1]` to `[min,-1,-1,0,max]`, while labelled cases preserve original records and tie order. |
| 349 — native `prod` directive | Ordinary Prod in `(key,payload)` trees, write lists, and enumeration. | The unequal-payload signed history and exact nonempty traversal suffix above. |
| 350 — recursive empty/insert/lookup/elements | `tableCase` and workloads call the complete `ExtractedTrees`/DecodedKeys operation set and shared `bindAll`. | Empty/default/optional behavior, latest repeated write, signed key order, stored zero versus absence, actual canonical entries, and actual fast traversal. |
| 358 — standalone `searchtree.ml` extraction | Global `main`, selected ordinary Lake executable, and the same driver under both launch paths. | Checked controlled replay, generated source/controlled workloads, fresh random queries, state boundaries, repetitions, nonzero rejection paths, actual standalone ELF and same-source results. |

Coq's extraction-output directory and import/scope/output commands are language mechanics. Lean's source/module imports, ordinary data, Lake target, and executable output provide the relevant adaptation. No Coq-to-OCaml implementation is claimed.

## 7. Reproducible recipes and bounded expectations

The recipes below are explicit configurations, not retained execution results. Replace the standalone prefix with the direct `lake env lean --run scripts/ExtractSearchTree.lean` prefix to exercise the other mode.

A small generalized random case with fixed independent test expectations is:

```sh
.lake/build/bin/extract-searchtree workload --carrier int64 --pattern random --timing source --size 8 --queries 8 --universe 13 --seed 1729 --warmups 1 --repetitions 2
```

The public test fixture expects insertion keys `[10,0,10,11,6,10,0,0]`, fresh query keys `[9,7,4,11,1,8,11,8]`, canonical keys `[0,6,10,11]` with value 1, and two hits. Its generator states are initially `[1730,1]`, after building `[1689113473,525453832]`, and after queries `[1827515937,1554910725]`. This literal oracle was obtained independently from the pinned core generator before the driver implemented random generation. Final mode receipts must establish the delivered program's actual agreement; these expected constants alone are not evidence of a run.

For the named source `test_random n`, set **size=queries=universe=n**, not merely size=queries=n. A bounded source-specialization recipe is:

```sh
.lake/build/bin/extract-searchtree workload --carrier int64 --pattern random --timing source --size 32 --queries 32 --universe 32 --seed 1729 --warmups 0 --repetitions 1
```

The three published source sizes remain explicit opt-in recipes:

```sh
.lake/build/bin/extract-searchtree workload --carrier int64 --pattern random --timing source --size 1000000 --queries 1000000 --universe 1000000 --seed 1729 --warmups 0 --repetitions 1
.lake/build/bin/extract-searchtree workload --carrier int64 --pattern random --timing source --size 20000 --queries 20000 --universe 20000 --seed 1729 --warmups 0 --repetitions 1
.lake/build/bin/extract-searchtree workload --carrier int64 --pattern consecutive --timing source --size 20000 --queries 20000 --seed 1729 --warmups 0 --repetitions 1
```

A completed bounded smoke cannot be reported as one of these larger runs. Output retains full lists and checking observations, so large scenarios also have substantial untimed validation/output work. No historical OCaml timing is substituted for a current Lean measurement.

For controlled replay, supply files such as insertion lines `3`, `1`, `3` and query lines `3`, `2`, `1`, `3`, `7`, one per line. This recipe must return three hits and canonical bindings `(1,1),(3,1)`:

```sh
.lake/build/bin/extract-searchtree workload --carrier int64 --pattern replay --inserted-file inserted.txt --queries-file queries.txt --warmups 0 --repetitions 1
```

The same retained files, carrier, values, defaults, and validation protocol can later support the Redblack comparison. That future realization must use its own proved source operations while preserving the controlled workload exactly.

## 8. Generated code and retained development execution

### Build, native executable, and selected generated-file identities

The retained build command ran through the established native host profile and invoked `lake --no-cache --rehash build extract-searchtree`. Its red receipt recorded exit 1 with `unknown target`; after the exact executable entry was added, the green receipt recorded exit 0, 1,812 jobs, and 100.227675489 seconds. The before/after driver, toolchain-file, and dependency-manifest hashes remained equal in that successful build. This is a development build observation, separate from the eventual clean acceptance build.

The inspected `.lake/build/bin/extract-searchtree` is a **64-bit x86-64 Linux ELF PIE executable**, dynamically linked, with debug information and not stripped. It is 135,477,624 bytes with SHA-256 **`ad48ceb7386c139446d811b5d649c3926b53f7da3e78456501ec5aaa1df1dcb3`**. The ELF magic, file type, hash, and selected disassembly were checked directly. The successful invocations described below identify this exact binary through the native profile's executable/hash arguments.

These paths are relative to the project root. The manifest selects the actual generated driver and computational provider files needed for the correspondence inspection; it is not an inventory of every linked module. The Examples files retain thin callable wrappers even where the driver directly calls their inlined or specialized dependency. `Basic.c` supplies comparison with the generic tree implementation; the actual Boolean-specialized tree bodies occur in `DecodedKeys.c`. Proof-only dependency modules need not retain theorem bodies in C.

| Selected generated C path | Bytes | SHA-256 |
| --- | ---: | --- |
| `.lake/build/ir/ExtractSearchTree.c` | 901772 | `22a37a3805389e2381e68f87cee0c7cc4837d9b42b415d20f83956b51ad8b33d` |
| `.lake/build/ir/Examples/ExtractedPrograms.c` | 7200 | `d6be13e7251e17ab7aab5d0bc219756f4211c80d16548a1a9fe4fa6ebd2fddec` |
| `.lake/build/ir/Examples/ExtractedTrees.c` | 22767 | `0683bdda3fdd143b0004ff2abcbf08000b92bf0aad711d89f218307149e5a7f5` |
| `.lake/build/ir/Examples/InsertionSorting.c` | 3714 | `20d8ed5355959585900bac7a881f16e74dcf9186cebdbd4e44604f78d9759cdc` |
| `.lake/build/ir/Applications/Sorting/DecodedInsertion.c` | 15063 | `2aac0f11b7a9714c7d9ae66384c29041966e8974425b05067c1ecd15b629b173` |
| `.lake/build/ir/Applications/Representations/SignedComparison.c` | 29856 | `b6b2894ac473f25461295a726e8fa1e4c59b3c4e14d20532f6329a08fc27b70a` |
| `.lake/build/ir/Applications/Search/OrderedMap/Basic.c` | 20680 | `b19f70998bc1dc780316ad2a0e74e4335b608ff39683ec2872110e7e880894c6` |
| `.lake/build/ir/Applications/Search/OrderedMap/Interface.c` | 21104 | `dda9da107fcbad57854745ebc6f56e1a093156b200d7f09cb62721c2c2594744` |
| `.lake/build/ir/Applications/Search/OrderedMap/DecodedKeys.c` | 34163 | `63ceb29f8d5cb33eda4ade93aeaac2d6f8d7c5425186191ef2142712965be32e` |
| `.lake/build/ir/Applications/Search/OrderedMap/DecodedKeysModels.c` | 19736 | `ac5fad8dd46c587919b760486e8661370479a127048f536e4fc256d0b93757fa` |
| `.lake/build/ir/Applications/Search/OrderedMap/Enumeration.c` | 13874 | `8f825028e23029d11f09dcc5e6132482a4d214987fd0d7c8a935c9205692115e` |
| `.lake/build/ir/Applications/Search/OrderedMap/Workload.c` | 25877 | `f5beb64b5239f54237450fbdb12f0e756043aeff7e65e0a792bbbbfac70fa7dd` |
| `.lake/build/ir/Applications/Trees/Observations.c` | 6071 | `28bf9afd40b6d2c6fe4e704b4ecdbffdf12132602d0d5920d86bf99b01b75b9c` |
| `.lake/packages/mathlib/.lake/build/ir/Mathlib/Data/List/Sort.c` | 90695 | `63b51cd068020ba2bfdf3d2bd4c9c516cf464b382b1149543edc2b7b01515143` |

### Actual generated computational closure

The inspected functions below are executable bodies and call edges, not an inference from import lists or matching source names. Generated `___redArg` functions drop arguments irrelevant to computation; `___boxed` functions adapt runtime representations. Compiler specialization may place an imported algorithm's body in the driver or reuse an identical specialization with another module's name.

| Observation | Inspected generated behavior |
| --- | --- |
| Public entry and serialization | `_lean_main` dispatches to the actual `examples` or parsed `workload` computation. Only successful IO results reach `l_Lean_Json_compress` and printing; the supplied default configuration and error handling remain executable. |
| Nat insertion sort | The driver's `natSortCase` thunk calls the generated `List_insertionSort` specialization. Its ordered insertion body uses `lean_nat_dec_le`, inserting before the current head on true. Its generated `List_foldrTR` builds an array and walks it backwards while repeatedly calling that ordered insertion. This is the compiler's implementation of the imported sort, not an extra user-authored sorting algorithm or a unary-Nat cost claim. |
| Generic and labelled sorting | `Applications_Sorting_DecodedInsertion_sort___redArg` wraps the supplied comparison and calls `lp_mathlib_List_insertionSort___redArg`; the latter uses `l_List_foldrTR___redArg` and `lp_mathlib_List_orderedInsert`. The labelled comparator projects each pair's first component before applying `leb`; labels remain in the sorted records. The finite-sort thunk directly calls this same generic provider. |
| Comparison selection | Driver closure constants bind Int64 encode/decode to their Int64 primitives and `ltb` to `SignedComparison_int64Ltb___boxed`; the example nonstrict path binds `int64Leb___boxed`. Width-63 closures separately bind `BitVec.ofInt`, `BitVec.toInt`, and the width-parameterized signed comparator. `SignedComparison.c` calls Int decisions for Int, `l_BitVec_slt/sle` for word comparisons, and `lean_int64_dec_lt/le` for Int64. |
| Chronological tree build | `workloadSampleFor___redArg___lam__3` calls `DecodedKeys_ops___redArg`, `Workload_sourceWrites___redArg`, then `Search_OrderedMap_bindAll___redArg`. `sourceWrites` constructs `(key,1)` pairs in input order. `bindAll` applies the record's insertion closure to each head and passes its returned tree into the next iteration. The record contains actual empty/insert/optional-lookup operations without reflection-proof arguments. |
| Tree search and insertion | `DecodedKeys.c` contains Boolean-specialized `OrderedMap.lookup` and `bind` bodies. They apply the supplied comparator first to query/key versus pivot, then in the opposite direction; true chooses the corresponding child, and two false outcomes return or replace the payload. The total-lookup wrapper inspects the returned Option and uses the caller's default only for none. No decoder argument enters these tree branches. |
| Enumeration and suffix | `DecodedKeys.elements/elementsAux` and their Examples wrappers reach `fastEntries/fastEntriesAcc`. The latter calls `Trees_fold___redArg`, then applies the produced function to the supplied suffix. Its combine body computes `right suffix`, constructs `binding :: ...`, then calls `left`; empty is the identity function. The actual returned list retains the suffix. |
| Independent reference and rejection | The driver's checker closure uses specialized `Std_DHashMap` insert/get functions on original Int inputs. Their bucket hashing and equality use Int arithmetic/`lean_int_dec_eq`; they do not invoke the tested comparator or tree operations. The checker separately obtains actual tree enumeration and optional queries, checks strict Int ordering, reference size and bindings, option-list equality, and both hit equalities. A failed condition returns an error before JSON serialization. |
| Explicit generator | `generatedKey` retains the positive-universe check, calls the pinned StdGen specialization of `randNat` with `0` and `U-1`, then checks the returned key `< U`. In this build the reused specialization is named `l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0`. That generated symbol name does not turn the workload into a shuffle or supply a distribution theorem. Local state is passed and returned explicitly. |
| Erasure boundary | The private Boolean relation's C value is an erased placeholder; its executable decision applies the retained Boolean comparator. `DecodedInsertion.sort` and the tree operations retain exactly their data/comparator dependencies, with validation decoding retained in the driver. The inspected call path has no executable reflection proof. Absence of a source alias name is not itself an erasure argument. |

Selected ELF disassembly corroborates the concrete comparator boundary. `lp_compilingWithSquares_Representations_SignedComparison_int64Ltb___boxed` and `int64Leb___boxed` load their 64-bit payloads and use signed `cmp`/`setl` or `cmp`/`setle`. Their object-unboxing/reference-counting work is also present. `l_BitVec_slt` calls `l_BitVec_toInt` twice before the signed Int comparison. The Int64 unboxed wrapper need not survive as a separate symbol after native optimization; the observed boxed body is the closure target that does survive.

### Generated timing order and range/model boundaries

For this exact driver C, let `D` abbreviate the generated prefix `lp_compilingWithSquares___private_ExtractSearchTree_0__ExtractSearchTree_`. The following control-flow observations use its actual bodies and closure bindings:

| Stage | Generated observation |
| --- | --- |
| Before conversion | `DworkloadSampleFor___redArg` checks all original prepared keys with `inRange` before the `lam__2` encoding thunks. It then checks both decoded round trips. Finite carrier count/universe bounds remain in `Dworkload` before workload generation. |
| Before first clock | The build thunk is `DworkloadSampleFor___redArg___lam__3`, captured as `v___f_1718_`, passed to the join as `v___y_1622_`, and executed by `l_IO_lazyPure___redArg` at generated C line 6216. Its returned tree is captured by the query thunk before the first clock call. |
| Timed interval | `lean_io_mono_nanos_now` at line 6237 is followed by `l_IO_lazyPure___redArg` on `DworkloadSampleFor___redArg___lam__4`; the second clock is at line 6258. Controlled mode calls the actual query-list lookup/hit fold. Source mode calls `DsourceQueries___redArg`, which constructs `Workload.sourceIndices config.queries` inside the call, then generates, checks, converts, decodes, searches, and counts each query. |
| Per-source-query safety | The generated source fold calls `generatedKey`, checks `inRange`, calls encode, calls decode, checks Int equality, and only then invokes actual `DecodedKeys.lookup` with default 0. It returns generator state and hits; it has no accumulator of generated query keys. |
| After second clock | Source replay calls the retained `generatedKeys` thunk after the clock and validates the final state and conversion. The validation join `v___jp_1545_` executes `lam__5` for enumeration, optional queries, the HashMap model, and all equalities. Both incoming success edges to that join occur after the end clock. JSON construction follows a successful checker result. |

The generated C lays out some joins earlier in the file than the code that jumps to them. In particular, the validation `IO.lazyPure` call appears textually at line 5894; its incoming control-flow edges are after the second clock. Inspection therefore follows branches and captures, not just increasing source line numbers. In the identified ELF, `l_IO_lazyPure___redArg` calls `lean_apply_1` on its thunk and constructs the IO success result after that call; the returned computation is not left as an unevaluated thunk. Normal allocation, reference-counting, and IO-wrapper overhead remain within whichever interval executes them.

### Historical bounded native smoke and observer results

The inspected final development harness is 54,482 bytes at SHA-256 `0a98340766236464f9b9c2939db3a371990c41413b7183e27e1098717f8b2d93`, containing 26 public tests. The records below were created under the old checkpoint039 runtime-tdd workspace. Their filenames and hashes preserve attribution; they are not claims of present source-file availability. The original records bound commands, exits, source identities, streams and copied inputs. The maintained public behavior is in `scripts/ExtractSearchTree.lean` and `scripts/test-extract-searchtree.py`. The successful native driver invocations use the profile's `exec --executable ... --sha256 ad48ceb7...` route for the exact ELF identified above, rather than a direct Lean `--run` invocation.

| Historical JSON record | Observed result | Record SHA-256 |
| --- | --- | --- |
| `22-standalone-target-red.json` | Build exit 1, unknown target before the Lake entry. | `cf9219e2d6d3642ca11491e1f56424ecc660be28b60b3e9de9bb025affa23404` |
| `22-standalone-target-green-01.json` | Build exit 0, 1,812 jobs after the entry, same driver. | `b02b8cd83aef77d880b65f6781b8b3e606b37c01a3de0a68687a33c119012556` |
| `28-compiled-examples-smoke-01.json` | Native `examples` exit 0; the independent receipt-observer invocation also exits 0; test passes. | `03dc5bb377293d775d7c8b5190ebd9497558a06ad97d3bf518e902c590d6a7cb` |
| `29-compiled-workloads-smoke-01.json` | Four native workloads and four independent observer invocations all exit 0; test passes. | `0eb412776fa7c36300d928f35f95cf19438c02794f3f0f887c5a871ff64aec6c` |
| `26-receipt-coherent-stream-regression-02.json` | The development regression rejecting incorrect workload receipts, including a coherent but wrong random stream, passes. | `4389aa76228568738ee83ccc7a705f67b8cb46cb37be7e16319bcbbd9bb9a0df` |
| `27-unbounded-int-regression-01.json` | The development unbounded-Int replay regression passes. | `a95758aef6d6344025d608c79f261ecd006f6ec6073ab827b336e8d74b058387` |

The four compiled workloads are the default controlled Int64 consecutive workload; source-timed random Int64 with N=Q=8, U=13, one warmup and two measured repetitions; empty word63 random with N=Q=U=0; and signed Int replay from retained input files. These are bounded development observations. They do not report execution of the large named source scenarios, completion of all 26 tests in both modes on the final candidate, or a measured comparison between the unbalanced tree and a future Redblack implementation.

## 9. Final acceptance gate and limits of the observations

This note preserves the original bounded development observations. Current receiving acceptance must bind the selected source/configuration/toolchain/dependency identities and actual generated executable, rechecking affected behavior and code observations. Binaries, caches and raw operational streams stay outside checkpoints; concise current evidence belongs to CTB-78, while CTB-91 retains historical attribution. If an executable differs, an old hash/result is not substituted for a new run. Detailed historical receipt names below are identifiers, not a requirement to carry their full files forever.

| Evidence item | Status in this document / final obligation |
| --- | --- |
| Driver source and signatures | Complete for the hash at the top, including all authored bodies. A later source change requires assessment of the change and affected dependencies. |
| Configuration and build | Actual exact target and successful development build observed above; the external clean acceptance build supplies final source/configuration/compiler/dependency binding. |
| Generated computational closure | Selected files, calls, comparator branches, chronological history, and suffix traversal inspected above. Recheck the selected hashes against acceptance output and assess any differences. |
| Timing boundary | The identified generated driver preserves build/query/replay/check order; concrete comparator and thunk observations were also inspected in its ELF. No general compiler-scheduling theorem is claimed. |
| Standalone execution | Exact ELF identity and bounded successful compiled invocations retained above. Final compiled execution must identify the actual accepted binary. |
| Both launch modes | Final full public success/failure suites and matching non-timing observations remain external acceptance obligations, with actual argv and retained exits/stdout/stderr/input identities. |
| Receipt independence | Development observer acceptance and rejection records exist. Final candidate-bound independent receipt checks and compact evidence remain required; driver success alone is insufficient. |
| Named large scenarios | Recipes only unless a separate actual run is retained; no completion or performance result claimed here. |

Compilation, linking, native runtime overrides, PRNG implementation, and clock behavior remain trusted execution mechanisms, not consequences of the source theorems. Generated-code inspection permits ordinary inlining and specialization while following actual symbols and branches; the selected identities make the scope of that inspection explicit.

The accepted mathematical development proves semantic contracts and explicitly modeled resource counts. It does not imply constant native comparison time, constant allocation, constant stack space, pointer sharing, or equal costs for value-equivalent traversals. The source's unary-`leb` difference-based cost claim is corrected by the separate terminal-inclusive `min n m + 1` model; that model is not Lean's native Nat comparison time. Ordinary increasing-key BST histories form a chain, so a full consecutive scan can have quadratic aggregate modeled work. A bounded random timing does not prove expected logarithmic behavior, and BST validity does not imply balanced height.

Runtime evidence supplements mathematical statement checks, proof audit and independent reviews. [CTB-91 and CTB-78](../textbooks/CTB.json) distinguish the donor Extract result from current receiving acceptance. Historical chapter ordering does not direct the current task; new formalization waits for the current integration gate.
