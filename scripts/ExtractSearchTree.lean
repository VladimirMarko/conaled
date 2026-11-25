import Examples.ExtractedPrograms
import Examples.ExtractedTrees
import Applications.Search.RedBlack.Models
import Applications.Search.RedBlack.Depth
import Applications.Search.BinomialQueue.Core
import Applications.Representations.DecodedBinomialQueue
import Init.Data.Random
import Lean.Data.Json
import Std.Data.HashMap.Basic

/-!
# Runnable Extract textbook programs

This entry point calls the proved source adapters. Runtime observations are
checked independently before they are reported; they do not replace the proofs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace ExtractSearchTree

private structure WorkloadConfig where
  realization : String := "ordinary"
  carrier : String := "int64"
  pattern : String := "consecutive"
  timing : String := "controlled"
  size : Nat := 32
  queries : Nat := 32
  rangeSize : Nat := 32
  seed : Nat := 1729
  warmups : Nat := 0
  repetitions : Nat := 1
  insertedFile : Option String := none
  queriesFile : Option String := none

private def parseWorkloadOptions :
    List String → WorkloadConfig → List String → Except String WorkloadConfig
  | [], config, seen => do
    if config.pattern == "replay" then
      unless config.timing == "controlled" do throw "replay supports controlled timing only"
      unless config.insertedFile.isSome && config.queriesFile.isSome do
        throw "replay requires both --inserted-file and --queries-file"
      if seen.any (fun flag => ["--size", "--queries", "--seed", "--universe"].contains flag) then
        throw "replay derives counts from files and does not accept generator options"
    else if config.insertedFile.isSome || config.queriesFile.isSome then
      throw "key files require --pattern replay"
    if config.pattern == "random" && config.rangeSize == 0 &&
        (config.size != 0 || config.queries != 0) then
      throw "random generation requires a positive universe when any draw is requested"
    if config.timing == "source" && config.queries != config.size then
      throw "source timing requires the query count to equal the construction size"
    if config.repetitions == 0 then throw "repetitions must be positive"
    pure config
  | [flag], _, _ => .error s!"missing value for {flag}"
  | flag :: value :: rest, config, seen => do
    if seen.contains flag then throw s!"duplicate option: {flag}"
    let next ← match flag with
      | "--realization" =>
        if ["ordinary", "redblack"].contains value then pure { config with realization := value }
        else throw s!"unsupported realization: {value}"
      | "--carrier" =>
        if ["int", "word63", "int64"].contains value then pure { config with carrier := value }
        else throw s!"unsupported carrier: {value}"
      | "--pattern" =>
        if ["consecutive", "random", "replay"].contains value then pure { config with pattern := value }
        else throw s!"unsupported pattern: {value}"
      | "--timing" =>
        if ["controlled", "source"].contains value then pure { config with timing := value }
        else throw s!"unsupported timing: {value}"
      | "--size" => do
        let some n := value.toNat? | throw "size must be a natural number"
        pure { config with size := n }
      | "--queries" => do
        let some n := value.toNat? | throw "queries must be a natural number"
        pure { config with queries := n }
      | "--universe" => do
        let some n := value.toNat? | throw "universe must be a natural number"
        pure { config with rangeSize := n }
      | "--seed" => do
        let some n := value.toNat? | throw "seed must be a natural number"
        pure { config with seed := n }
      | "--warmups" => do
        let some n := value.toNat? | throw "warmups must be a natural number"
        pure { config with warmups := n }
      | "--repetitions" => do
        let some n := value.toNat? | throw "repetitions must be a natural number"
        pure { config with repetitions := n }
      | "--inserted-file" => pure { config with insertedFile := some value }
      | "--queries-file" => pure { config with queriesFile := some value }
      | _ => throw s!"unknown option: {flag}"
    parseWorkloadOptions rest next (flag :: seen)

private def readKeyFile (path : String) : IO (List Int) := do
  let text ← IO.FS.readFile path
  text.lines.toList.zipIdx.mapM fun (line, index) => do
    let some key := line.toInt? |
      throw (IO.userError s!"invalid decimal key in {path} at line {index + 1}")
    pure key

private def generatedKey (config : WorkloadConfig) (count index : Nat)
    (state : StdGen) : Except String (Int × StdGen) := do
  if config.pattern == "random" then
    if config.rangeSize == 0 then throw "cannot draw from an empty random universe"
    let (key, next) := randNat state 0 (config.rangeSize - 1)
    unless key < config.rangeSize do throw "random generator returned a key outside its requested range"
    pure ((key : Int), next)
  else
    pure (((count - index : Nat) : Int), state)

private def generatedKeys (config : WorkloadConfig) (count : Nat)
    (initial : StdGen) : Except String (List Int × StdGen) := do
  let (reversed, final) ← (Search.OrderedMap.Workload.sourceIndices count).foldlM
    (fun (state : List Int × StdGen) index => do
      let (key, next) ← generatedKey config count index state.2
      pure (key :: state.1, next)) ([], initial)
  pure (reversed.reverse, final)

-- These executable observations are checked outside the query interval. They
-- supplement the proved invariants; their returned Booleans are not proofs.
private def orderedWithin {W : Type} (decode : W → Int) (lower upper : Option Int) :
    BinaryTree (W × Nat) → Bool
  | .nil => true
  | .node binding left right =>
      let key := decode binding.1
      (lower.all (fun bound => decide (bound < key))) &&
        (upper.all (fun bound => decide (key < bound))) &&
        orderedWithin decode lower (some key) left &&
        orderedWithin decode (some key) upper right

private def ordinaryPreorder {W : Type} (decode : W → Int) :
    BinaryTree (W × Nat) → List Lean.Json → List Lean.Json
  | .nil, suffix => Lean.Json.null :: suffix
  | .node binding left right, suffix =>
      Lean.Json.arr #[Lean.Json.null, Lean.toJson (toString (decode binding.1)),
        Lean.toJson binding.2] :: ordinaryPreorder decode left (ordinaryPreorder decode right suffix)

private def redblackPreorder {W : Type} (decode : W → Int) :
    Search.RedBlack.Tree W Nat → List Lean.Json → List Lean.Json
  | .nil, suffix => Lean.Json.null :: suffix
  | .node color left binding right, suffix =>
      let name := match color with | .red => "red" | .black => "black"
      Lean.Json.arr #[Lean.toJson name, Lean.toJson (toString (decode binding.1)),
        Lean.toJson binding.2] :: redblackPreorder decode left (redblackPreorder decode right suffix)

private def rootBlack {W : Type} : Search.RedBlack.Tree W Nat → Bool
  | .nil => true
  | .node .black _ _ _ => true
  | .node .red _ _ _ => false

private def noRedRed {W : Type} : Search.RedBlack.Tree W Nat → Bool
  | .nil => true
  | .node color left _ right =>
      (match color with
        | .red => rootBlack left && rootBlack right
        | .black => true) && noRedRed left && noRedRed right

private def blackHeight? {W : Type} : Search.RedBlack.Tree W Nat → Option Nat
  | .nil => some 0
  | .node color left _ right => do
      let leftHeight ← blackHeight? left
      let rightHeight ← blackHeight? right
      if leftHeight == rightHeight then
        pure (leftHeight + match color with | .red => 0 | .black => 1)
      else none

private def ordinaryTreeObservation {W : Type} (decode : W → Int)
    (tree : BinaryTree (W × Nat)) : Except String Lean.Json := do
  let bst := orderedWithin decode none none tree
  unless bst do throw "ordinary tree failed the all-descendant ordering check"
  pure <| Lean.Json.mkObj [
    ("nodes", Lean.toJson tree.numNodes), ("height", Lean.toJson tree.height),
    ("bst", Lean.toJson bst), ("redblack", Lean.Json.null),
    ("preorder", Lean.Json.arr (ordinaryPreorder decode tree []).toArray)]

private def redblackTreeObservation {W : Type} (requireValid : Bool) (decode : W → Int)
    (tree : Search.RedBlack.Tree W Nat) : Except String Lean.Json := do
  let bst := orderedWithin decode none none (Search.RedBlack.eraseColors tree)
  let blackRoot := rootBlack tree
  let localInvariant := noRedRed tree
  let commonBlackHeight := blackHeight? tree
  let nodes := tree.size
  let height := Search.RedBlack.height tree
  let logBound := decide (height ≤ 2 * (nodes + 1).log2)
  if requireValid && !(bst && blackRoot && localInvariant && commonBlackHeight.isSome && logBound) then
    throw "redblack tree failed the separate ordering, color, black-height or height-bound checks"
  pure <| Lean.Json.mkObj [
    ("nodes", Lean.toJson nodes), ("height", Lean.toJson height), ("bst", Lean.toJson bst),
    ("redblack", Lean.Json.mkObj [
      ("rootBlack", Lean.toJson blackRoot), ("noRedRed", Lean.toJson localInvariant),
      ("equalBlackHeight", Lean.toJson commonBlackHeight.isSome),
      ("blackHeight", Lean.toJson commonBlackHeight), ("logHeightBound", Lean.toJson logBound)]),
    ("preorder", Lean.Json.arr (redblackPreorder decode tree []).toArray)]

private def sourceQueries {W T : Type} (config : WorkloadConfig) (inRange : Int → Bool)
    (encode : Int → W) (decode : W → Int) (ops : Search.OrderedMap.Ops W Nat T)
    (tree : T) (initial : StdGen) : Except String (StdGen × Nat) :=
  -- The timed loop retains generator state and hits, never a captured key list.
  (Search.OrderedMap.Workload.sourceIndices config.queries).foldlM
    (fun (state : StdGen × Nat) index => do
      let (key, next) ← generatedKey config config.size index state.1
      unless inRange key do throw "generated query is outside the carrier's signed range"
      let encoded := encode key
      unless decode encoded == key do throw "generated query conversion changed its key"
      let hits := if (ops.lookup encoded tree).getD 0 = 1 then
        state.2 + 1 else state.2
      pure (next, hits)) (initial, 0)

private def workloadSampleFor {W T : Type} (config : WorkloadConfig)
    (replayInputs : Option (List Int × List Int)) (phase : String) (index : Nat)
    (inRange : Int → Bool) (encode : Int → W) (decode : W → Int)
    (ops : Search.OrderedMap.Ops W Nat T) (elements : T → List (W × Nat))
    (observeTree : T → Except String Lean.Json) : IO Lean.Json := do
  let initial := mkStdGen config.seed
  let (inserted, postBuild) ←
    if config.pattern == "replay" then do
      let some keys := replayInputs | throw (IO.userError "missing prepared replay inputs")
      pure (keys.1, initial)
    else do
      let generated ← IO.lazyPure fun _ => generatedKeys config config.size initial
      IO.ofExcept generated
  let (queries, postQuery) ←
    if config.timing == "source" then
      pure ([], postBuild)
    else if config.pattern == "replay" then do
      let some keys := replayInputs | throw (IO.userError "missing prepared replay inputs")
      pure (keys.2, postBuild)
    else do
      let generated ← IO.lazyPure fun _ => generatedKeys config config.queries postBuild
      IO.ofExcept generated
  unless (inserted ++ queries).all inRange do
    throw (IO.userError s!"{config.carrier}: workload input is outside the signed range")
  let encodedInserted ← IO.lazyPure fun _ => inserted.map encode
  let encodedQueries ← IO.lazyPure fun _ => queries.map encode
  unless encodedInserted.map decode == inserted && encodedQueries.map decode == queries do
    throw (IO.userError s!"{config.carrier}: workload conversion changed an input key")
  let tree ← IO.lazyPure fun _ => Search.OrderedMap.bindAll
    ops (Search.OrderedMap.Workload.sourceWrites encodedInserted) ops.empty
  let started ← IO.monoNanosNow
  let observed ← IO.lazyPure fun _ =>
    if config.timing == "source" then
      sourceQueries config inRange encode decode ops tree postBuild
    else
      Except.ok (postQuery, encodedQueries.foldl
        (fun count key => if (ops.lookup key tree).getD 0 = 1 then count + 1 else count) 0)
  let ended ← IO.monoNanosNow
  unless started ≤ ended do
    throw (IO.userError "monotonic clock moved backwards during the query interval")
  let (observedPostQuery, hits) ← IO.ofExcept observed
  let (queries, encodedQueries, postQuery) ←
    if config.timing == "source" then do
      let replayed ← IO.lazyPure fun _ => generatedKeys config config.queries postBuild
      let (keys, replayedState) ← IO.ofExcept replayed
      unless replayedState.s1 == observedPostQuery.s1 && replayedState.s2 == observedPostQuery.s2 do
        throw (IO.userError "source query replay did not reproduce the observed generator state")
      unless keys.all inRange do
        throw (IO.userError "source query replay contains an unrepresentable key")
      let encoded ← IO.lazyPure fun _ => keys.map encode
      unless encoded.map decode == keys do
        throw (IO.userError "source query replay conversion changed an input key")
      pure (keys, encoded, observedPostQuery)
    else
      pure (queries, encodedQueries, observedPostQuery)
  -- All independent model and optional/enumeration checking occurs after timing.
  let checked ← IO.lazyPure fun _ =>
    let reference := inserted.foldl (fun (model : Std.HashMap Int Nat) key => model.insert key 1) ∅
    let entries := (elements tree).map
      (fun (key, value) => (decode key, value))
    let options := encodedQueries.map (fun key => ops.lookup key tree)
    let expectedOptions := queries.map (fun key => reference[key]?)
    let expectedHits := expectedOptions.foldl
      (fun count value => if value == some 1 then count + 1 else count) 0
    let observedHits := options.foldl
      (fun count value => if value == some 1 then count + 1 else count) 0
    let ordered := (entries.foldl (fun (state : Option Int × Bool) binding =>
      (some binding.1, state.2 && (match state.1 with
        | none => true
        | some previous => decide (previous < binding.1)))) (none, true)).2
    let canonical := ordered && entries.length == reference.size &&
      entries.all (fun binding => reference[binding.1]? == some binding.2)
    if options == expectedOptions && hits == expectedHits && hits == observedHits && canonical then
      (Except.ok (entries, options, expectedHits, reference.size) :
        Except String (List (Int × Nat) × List (Option Nat) × Nat × Nat))
    else .error "workload result does not match the independent Int-key finite map"
  let (entries, options, expectedHits, distinct) ← IO.ofExcept checked
  let treeObservation ← IO.lazyPure fun _ => observeTree tree
  let treeObservation ← IO.ofExcept treeObservation
  let stateJson := fun (state : StdGen) => Lean.toJson [state.s1, state.s2]
  let generator := if config.pattern == "replay" then Lean.Json.null else Lean.Json.mkObj [
    ("name", Lean.toJson "StdGen/mkStdGen/randNat"),
    ("initial", stateJson initial), ("postBuild", stateJson postBuild),
    ("postQuery", stateJson postQuery),
    ("buildDraws", Lean.toJson (if config.pattern == "random" then config.size else 0)),
    ("queryDraws", Lean.toJson (if config.pattern == "random" then config.queries else 0))]
  return Lean.Json.mkObj [
    ("phase", Lean.toJson phase), ("index", Lean.toJson index),
    ("inserted", Lean.toJson (inserted.map toString)),
    ("queries", Lean.toJson (queries.map toString)),
    ("entries", Lean.toJson (entries.map (fun (key, value) => (toString key, value)))),
    ("queryOptions", Lean.toJson options), ("hits", Lean.toJson hits),
    ("expectedHits", Lean.toJson expectedHits), ("distinct", Lean.toJson distinct),
    ("elapsedNs", Lean.toJson (ended - started)), ("generator", generator),
    ("tree", treeObservation)]

private def workloadFor {W : Type} (config : WorkloadConfig)
    (inRange : Int → Bool) (encode : Int → W) (decode : W → Int)
    (ltb : W → W → Bool) : IO Lean.Json := do
  -- Read file inputs once. Every sample rebuilds from these same immutable lists.
  let (config, replayInputs) ←
    if config.pattern == "replay" then do
      let some insertedPath := config.insertedFile | throw (IO.userError "missing insertion key file")
      let some queryPath := config.queriesFile | throw (IO.userError "missing query key file")
      let inserted ← readKeyFile insertedPath
      let queries ← readKeyFile queryPath
      pure ({ config with size := inserted.length, queries := queries.length }, some (inserted, queries))
    else
      pure (config, none)
  let sampleFor := fun phase index =>
    if config.realization == "redblack" then
      workloadSampleFor config replayInputs phase index inRange encode decode
        (Search.RedBlack.ops ltb) Search.RedBlack.elements (redblackTreeObservation true decode)
    else
      workloadSampleFor config replayInputs phase index inRange encode decode
        (Search.OrderedMap.DecodedKeys.ops ltb) Examples.ExtractedTrees.elements
        (ordinaryTreeObservation decode)
  let warmups ← (List.range config.warmups).mapM fun index => sampleFor "warmup" index
  let measured ← (List.range config.repetitions).mapM fun index => sampleFor "measured" index
  return Lean.Json.mkObj [
    ("schema", Lean.toJson (2 : Nat)), ("kind", Lean.toJson "workload"),
    ("config", Lean.Json.mkObj [
      ("realization", Lean.toJson config.realization),
      ("carrier", Lean.toJson config.carrier), ("pattern", Lean.toJson config.pattern),
      ("timing", Lean.toJson config.timing), ("size", Lean.toJson config.size),
      ("queries", Lean.toJson config.queries),
      ("universe", if config.pattern == "replay" then Lean.Json.null else Lean.toJson config.rangeSize),
      ("seed", if config.pattern == "replay" then Lean.Json.null else Lean.toJson config.seed),
      ("warmups", Lean.toJson config.warmups),
      ("repetitions", Lean.toJson config.repetitions),
      ("insertedFile", Lean.toJson config.insertedFile),
      ("queriesFile", Lean.toJson config.queriesFile)]),
    ("clock", Lean.toJson "IO.monoNanosNow"), ("unit", Lean.toJson "ns"),
    ("timedRegion", Lean.toJson (if config.timing == "source" then
      "generated queries: descending schedule creation/traversal, key generation, checked conversion, lookup, hit count"
      else "precomputed queries: traversal, lookup, hit count")),
    ("samples", Lean.Json.arr (warmups ++ measured).toArray)]

private def workload (config : WorkloadConfig) : IO Lean.Json := do
  match config.carrier with
  | "int" =>
    workloadFor config (fun _ => true) id id
      Representations.SignedComparison.intLtb
  | "word63" =>
    -- Reject unrepresentable prefixes before allocating their schedules or keys.
    if config.pattern == "consecutive" then
      unless config.size ≤ 2^62 ∧ config.queries ≤ 2^62 do
        throw (IO.userError "word63 consecutive prefixes exceed the signed positive capacity")
    if config.pattern == "random" then
      unless config.rangeSize ≤ 2^62 do
        throw (IO.userError "word63 random key range exceeds the signed positive capacity")
    workloadFor config
      (fun key => decide (-(2 : Int)^62 ≤ key ∧ key < (2 : Int)^62))
      (BitVec.ofInt 63) BitVec.toInt Representations.SignedComparison.wordLtb
  | "int64" =>
    if config.pattern == "consecutive" then
      unless config.size ≤ 2^63 ∧ config.queries ≤ 2^63 do
        throw (IO.userError "int64 consecutive prefixes exceed the signed positive capacity")
    if config.pattern == "random" then
      unless config.rangeSize ≤ 2^63 do
        throw (IO.userError "int64 random key range exceeds the signed positive capacity")
    workloadFor config
      (fun key => decide (-(2 : Int)^63 ≤ key ∧ key < (2 : Int)^63))
      Int64.ofInt Int64.toInt Representations.SignedComparison.int64Ltb
  | _ => throw (IO.userError s!"unsupported carrier: {config.carrier}")

private def wordAdditionCase (left right expected : Int) (expectedOverflow : Bool) : IO Lean.Json := do
  unless decide (-8 ≤ left ∧ left < 8 ∧ -8 ≤ right ∧ right < 8) do
    throw (IO.userError "four-bit addition input is outside the signed range")
  let a := BitVec.ofInt 4 left
  let b := BitVec.ofInt 4 right
  let sum ← IO.lazyPure fun _ => (a + b).toInt
  let overflow ← IO.lazyPure fun _ => BitVec.saddOverflow a b
  unless sum == expected && overflow == expectedOverflow do
    throw (IO.userError "four-bit addition did not match the checked boundary case")
  return Lean.Json.mkObj [
    ("width", Lean.toJson (4 : Nat)), ("left", Lean.toJson (toString left)),
    ("right", Lean.toJson (toString right)), ("sum", Lean.toJson (toString sum)),
    ("mathematicalSum", Lean.toJson (toString (left + right))),
    ("overflow", Lean.toJson overflow)]

private def wordBoundaries : IO Lean.Json := do
  let overflow ← wordAdditionCase 7 1 (-8) true
  let safe ← wordAdditionCase 2 1 3 false
  -- This deliberate modular collapse is separate from guarded finite inputs.
  let sourceIntegers : List Int := [-3, 4, 99]
  let keys := sourceIntegers.map (BitVec.ofInt 0)
  let decodedKeys ← IO.lazyPure fun _ => keys.map BitVec.toInt
  let tree ← IO.lazyPure fun _ => Search.OrderedMap.bindAll
    (Search.OrderedMap.DecodedKeys.ops Representations.SignedComparison.wordLtb)
    (keys.zip [7, 8, 9]) (Examples.ExtractedTrees.emptyTree : BinaryTree (BitVec 0 × Nat))
  let strict ← IO.lazyPure fun _ => Representations.SignedComparison.wordLtb
    (BitVec.ofInt 0 (-3)) (BitVec.ofInt 0 99)
  let nonstrict ← IO.lazyPure fun _ => Representations.SignedComparison.wordLeb
    (BitVec.ofInt 0 (-3)) (BitVec.ofInt 0 99)
  let entries ← IO.lazyPure fun _ =>
    (Examples.ExtractedTrees.elements tree).map (fun (key, value) => (key.toInt, value))
  let optional ← IO.lazyPure fun _ => Search.OrderedMap.DecodedKeys.lookup?
    Representations.SignedComparison.wordLtb (BitVec.ofInt 0 4) tree
  let default99 ← IO.lazyPure fun _ => Examples.ExtractedTrees.lookup
    Representations.SignedComparison.wordLtb 99 (BitVec.ofInt 0 99) tree
  unless decodedKeys == [0, 0, 0] && !strict && nonstrict &&
      entries == [(0, 9)] && optional == some 9 && default99 == 9 do
    throw (IO.userError "width-zero operations did not exhibit singleton-carrier replacement")
  return Lean.Json.mkObj [
    ("overflow", overflow), ("safe", safe),
    ("zeroWidth", Lean.Json.mkObj [
      ("sourceIntegers", Lean.toJson (sourceIntegers.map toString)),
      ("decodedKeys", Lean.toJson (decodedKeys.map toString)),
      ("strict", Lean.toJson strict), ("nonstrict", Lean.toJson nonstrict),
      ("entries", Lean.toJson (entries.map (fun (key, value) => (toString key, value)))),
      ("optional", Lean.toJson optional), ("default99", Lean.toJson default99)])]

private def tableCase {W T : Type} (carrier : String) (inRange : Int → Bool)
    (encode : Int → W) (decode : W → Int) (ops : Search.OrderedMap.Ops W Nat T)
    (elements : T → List (W × Nat)) (elementsAux : T → List (W × Nat) → List (W × Nat))
    (observeTree : T → Except String Lean.Json) : IO (Lean.Json × Lean.Json) := do
  let writes : List (Int × Nat) := [(-3, 7), (4, 8), (-3, 9), (0, 0)]
  let queries : List Int := [-3, 4, 0, -1]
  let keys := writes.map Prod.fst ++ queries ++ [99]
  unless keys.all inRange do
    throw (IO.userError s!"{carrier}: table input is outside the signed range")
  unless keys.all (fun key => decode (encode key) == key) do
    throw (IO.userError s!"{carrier}: table conversion changed an input key")
  let empty := ops.empty
  let encodedWrites := writes.map (fun (key, value) => (encode key, value))
  let encodedQueries := queries.map encode
  let tree ← IO.lazyPure fun _ => Search.OrderedMap.bindAll ops encodedWrites empty
  let optional ← IO.lazyPure fun _ => encodedQueries.map (fun key => ops.lookup key tree)
  let default0 ← IO.lazyPure fun _ => encodedQueries.map
    (fun key => (ops.lookup key tree).getD 0)
  let default99 ← IO.lazyPure fun _ => encodedQueries.map
    (fun key => (ops.lookup key tree).getD 99)
  let entries ← IO.lazyPure fun _ =>
    (elements tree).map (fun (key, value) => (decode key, value))
  let withSuffix ← IO.lazyPure fun _ =>
    (elementsAux tree [(encode 99, 123)]).map
      (fun (key, value) => (decode key, value))
  let emptyEntries ← IO.lazyPure fun _ => elements empty
  let emptyOptional ← IO.lazyPure fun _ => ops.lookup (encode 0) empty
  let emptyDefault ← IO.lazyPure fun _ => (ops.lookup (encode 0) empty).getD 99
  unless optional == [some 9, some 8, some 0, none] &&
      default0 == [9, 8, 0, 0] && default99 == [9, 8, 0, 99] &&
      entries == [(-3, 9), (0, 0), (4, 8)] &&
      withSuffix == [(-3, 9), (0, 0), (4, 8), (99, 123)] &&
      emptyEntries.isEmpty && emptyOptional.isNone && emptyDefault == 99 do
    throw (IO.userError s!"{carrier}: table observations do not match the independent history")
  let pairsJson := fun (pairs : List (Int × Nat)) =>
    Lean.toJson (pairs.map (fun (key, value) => (toString key, value)))
  let treeObservation ← IO.lazyPure fun _ => observeTree tree
  let treeObservation ← IO.ofExcept treeObservation
  return (Lean.Json.mkObj [
    ("carrier", Lean.toJson carrier), ("writes", pairsJson writes),
    ("queries", Lean.toJson (queries.map toString)),
    ("optional", Lean.toJson optional), ("default0", Lean.toJson default0),
    ("default99", Lean.toJson default99), ("entries", pairsJson entries),
    ("withSuffix", pairsJson withSuffix),
    ("empty", Lean.Json.mkObj [
      ("entries", pairsJson (emptyEntries.map (fun (key, value) => (decode key, value)))),
      ("optional", Lean.toJson emptyOptional), ("default", Lean.toJson emptyDefault)])], treeObservation)

private def comparisonCases {W : Type} (carrier : String) (minimum maximum : Int)
    (inRange : Int → Bool) (encode : Int → W) (decode : W → Int)
    (ltb leb : W → W → Bool) : IO Lean.Json := do
  let cases : List (Int × Int × Bool × Bool) :=
    [(-3, 0, true, true), (0, 0, false, true), (4, -1, false, false),
      (minimum, maximum, true, true), (maximum, minimum, false, false)]
  let results ← cases.mapM fun (left, right, expectedLt, expectedLe) => do
    unless inRange left && inRange right do
      throw (IO.userError s!"{carrier}: comparison input is outside the signed range")
    let a ← IO.lazyPure fun _ => encode left
    let b ← IO.lazyPure fun _ => encode right
    unless decode a == left && decode b == right do
      throw (IO.userError s!"{carrier}: comparison conversion changed an input")
    let actualLt ← IO.lazyPure fun _ => ltb a b
    let actualLe ← IO.lazyPure fun _ => leb a b
    unless actualLt == expectedLt && actualLe == expectedLe do
      throw (IO.userError s!"{carrier}: signed comparison returned an incorrect result")
    pure <| Lean.Json.mkObj [
      ("left", Lean.toJson (toString left)), ("right", Lean.toJson (toString right)),
      ("lt", Lean.toJson actualLt), ("le", Lean.toJson actualLe)]
  return Lean.Json.mkObj [
    ("carrier", Lean.toJson carrier), ("cases", Lean.Json.arr results.toArray)]

private def stableSortCase {W : Type} (carrier : String) (inRange : Int → Bool)
    (encode : Int → W) (decode : W → Int) (leb : W → W → Bool) : IO Lean.Json := do
  let input : List (Int × String) := [(2, "first"), (1, "middle"), (2, "last")]
  unless input.all (fun binding => inRange binding.1) do
    throw (IO.userError s!"{carrier}: labelled sorting input is outside the signed range")
  let encoded ← IO.lazyPure fun _ => input.map (fun (key, label) => (encode key, label))
  unless encoded.map (fun (key, label) => (decode key, label)) == input do
    throw (IO.userError s!"{carrier}: labelled conversion changed an input")
  let output ← IO.lazyPure fun _ =>
    Examples.ExtractedPrograms.sort_int (fun a b => leb a.1 b.1) encoded
  let decoded ← IO.lazyPure fun _ => output.map (fun (key, label) => (decode key, label))
  unless decoded == [(1, "middle"), (2, "first"), (2, "last")] do
    throw (IO.userError s!"{carrier}: source sort did not preserve labelled ties")
  let pairsJson := fun (pairs : List (Int × String)) =>
    Lean.toJson (pairs.map (fun (key, label) => (toString key, label)))
  return Lean.Json.mkObj [
    ("carrier", Lean.toJson carrier),
    ("input", pairsJson input), ("output", pairsJson decoded)]

private def finiteSortCase {W : Type} (carrier : String) (width : Nat)
    (minimum upperExclusive : Int) (encode : Int → W) (decode : W → Int)
    (leb : W → W → Bool) : IO Lean.Json := do
  let maximum := upperExclusive - 1
  let input : List Int := [-1, maximum, minimum, 0, -1]
  unless input.all (fun key => decide (minimum ≤ key ∧ key < upperExclusive)) do
    throw (IO.userError s!"{carrier}: sorting input is outside the signed range")
  let encoded ← IO.lazyPure fun _ => input.map encode
  unless encoded.map decode == input do
    throw (IO.userError s!"{carrier}: signed conversion changed an input key")
  let output ← IO.lazyPure fun _ => Examples.ExtractedPrograms.sort_int leb encoded
  let decoded ← IO.lazyPure fun _ => output.map decode
  unless decoded == [minimum, -1, -1, 0, maximum] do
    throw (IO.userError s!"{carrier}: source sort returned an incorrect signed result")
  return Lean.Json.mkObj [
    ("carrier", Lean.toJson carrier), ("width", Lean.toJson width),
    ("minimum", Lean.toJson (toString minimum)),
    ("maximum", Lean.toJson (toString maximum)),
    ("input", Lean.toJson (input.map toString)),
    ("output", Lean.toJson (decoded.map toString))]

private def natSortCase (input expected : List Nat) : IO Lean.Json := do
  let output ← IO.lazyPure fun _ => Examples.ExtractedPrograms.sort input
  unless output == expected do
    throw (IO.userError "sort returned an incorrect natural-number sorting result")
  return Lean.Json.mkObj [
    ("input", Lean.toJson (input.map toString)),
    ("output", Lean.toJson (output.map toString))]

private def examples : IO Lean.Json := do
  let input : List Int := [-3, 2, -3, 0, 1]
  let output ← IO.lazyPure fun _ => Examples.ExtractedPrograms.sortZ input
  unless output == [-3, -3, 0, 1, 2] do
    throw (IO.userError "sortZ returned an incorrect signed sorting result")
  let intBoundaryCases : List (List Int × List Int) := [([], []), ([-7], [-7])]
  let intBoundaryResults ← intBoundaryCases.mapM fun (xs, expected) => do
    let result ← IO.lazyPure fun _ => Examples.ExtractedPrograms.sortZ xs
    unless result == expected do
      throw (IO.userError "sortZ returned an incorrect empty or singleton result")
    pure <| Lean.Json.mkObj [
      ("input", Lean.toJson (xs.map toString)),
      ("output", Lean.toJson (result.map toString))]
  let natCases : List (List Nat × List Nat) :=
    [([], []), ([7], [7]), ([4, 3, 2, 1], [1, 2, 3, 4]),
      ([3, 1, 3, 0, 1], [0, 1, 1, 3, 3])]
  let natResults ← natCases.mapM (fun (xs, expected) => natSortCase xs expected)
  let wordResult ← finiteSortCase "word63" 63 (-(2 : Int)^62) ((2 : Int)^62)
    (BitVec.ofInt 63) BitVec.toInt Representations.SignedComparison.wordLeb
  let int64Result ← finiteSortCase "int64" 64 (-(2 : Int)^63) ((2 : Int)^63)
    Int64.ofInt Int64.toInt Representations.SignedComparison.int64Leb
  let intStable ← stableSortCase "int" (fun _ => true) id id
    Representations.SignedComparison.intLeb
  let wordStable ← stableSortCase "word63"
    (fun key => decide (-(2 : Int)^62 ≤ key ∧ key < (2 : Int)^62))
    (BitVec.ofInt 63) BitVec.toInt Representations.SignedComparison.wordLeb
  let int64Stable ← stableSortCase "int64"
    (fun key => decide (-(2 : Int)^63 ≤ key ∧ key < (2 : Int)^63))
    Int64.ofInt Int64.toInt Representations.SignedComparison.int64Leb
  let intComparisons ← comparisonCases "int" (-(2 : Int)^70) ((2 : Int)^70 - 1)
    (fun _ => true) id id Representations.SignedComparison.intLtb
    Representations.SignedComparison.intLeb
  let wordComparisons ← comparisonCases "word63" (-(2 : Int)^62) ((2 : Int)^62 - 1)
    (fun key => decide (-(2 : Int)^62 ≤ key ∧ key < (2 : Int)^62))
    (BitVec.ofInt 63) BitVec.toInt Representations.SignedComparison.wordLtb
    Representations.SignedComparison.wordLeb
  let int64Comparisons ← comparisonCases "int64" (-(2 : Int)^63) ((2 : Int)^63 - 1)
    (fun key => decide (-(2 : Int)^63 ≤ key ∧ key < (2 : Int)^63))
    Int64.ofInt Int64.toInt Representations.SignedComparison.int64Ltb
    Representations.SignedComparison.int64Leb
  let fourBitSigned ← IO.lazyPure fun _ =>
    Representations.SignedComparison.wordLtb (BitVec.ofInt 4 (-1)) (BitVec.ofInt 4 0)
  let fourBitUnsigned ← IO.lazyPure fun _ =>
    (BitVec.ofInt 4 (-1)).ult (BitVec.ofInt 4 0)
  unless fourBitSigned && !fourBitUnsigned do
    throw (IO.userError "four-bit signed and unsigned comparisons did not differ as expected")
  let intTable ← tableCase "int" (fun _ => true) id id
    (Search.OrderedMap.DecodedKeys.ops Representations.SignedComparison.intLtb)
    Examples.ExtractedTrees.elements Examples.ExtractedTrees.elementsAux (ordinaryTreeObservation id)
  let wordTable ← tableCase "word63"
    (fun key => decide (-(2 : Int)^62 ≤ key ∧ key < (2 : Int)^62))
    (BitVec.ofInt 63) BitVec.toInt
    (Search.OrderedMap.DecodedKeys.ops Representations.SignedComparison.wordLtb)
    Examples.ExtractedTrees.elements Examples.ExtractedTrees.elementsAux (ordinaryTreeObservation BitVec.toInt)
  let int64Table ← tableCase "int64"
    (fun key => decide (-(2 : Int)^63 ≤ key ∧ key < (2 : Int)^63))
    Int64.ofInt Int64.toInt
    (Search.OrderedMap.DecodedKeys.ops Representations.SignedComparison.int64Ltb)
    Examples.ExtractedTrees.elements Examples.ExtractedTrees.elementsAux (ordinaryTreeObservation Int64.toInt)
  let boundaries ← wordBoundaries
  return Lean.Json.mkObj [
    ("schema", Lean.toJson (1 : Nat)),
    ("kind", Lean.toJson "examples"),
    ("sortZ", Lean.Json.mkObj [
      ("input", Lean.toJson (input.map toString)),
      ("output", Lean.toJson (output.map toString))]),
    ("sortZBoundary", Lean.Json.arr intBoundaryResults.toArray),
    ("natSort", Lean.Json.arr natResults.toArray),
    ("finiteSort", Lean.Json.arr #[wordResult, int64Result]),
    ("stableSort", Lean.Json.arr #[intStable, wordStable, int64Stable]),
    ("comparisons", Lean.Json.arr #[intComparisons, wordComparisons, int64Comparisons]),
    ("fourBitComparison", Lean.Json.mkObj [
      ("left", Lean.toJson "-1"), ("right", Lean.toJson "0"),
      ("signedLt", Lean.toJson fourBitSigned), ("unsignedLt", Lean.toJson fourBitUnsigned)]),
    ("tables", Lean.Json.arr #[intTable.1, wordTable.1, int64Table.1]),
    ("wordBoundaries", boundaries)]

private def redblackInvariantCases : IO (List Lean.Json) := do
  -- Raw finite fixtures independently separate the four executable checks.
  -- The red singleton satisfies the general shape invariant under a black
  -- parent; it violates only the black-root convention of the public history.
  let fixtures : List (String × Search.RedBlack.Tree Int Nat) := [
    ("deep-key-outside-bound", .node .black
      (.node .black .nil (-2, 1) (.node .red .nil (1, 1) .nil)) (0, 1)
      (.node .black .nil (2, 1) .nil)),
    ("red-red", .node .black
      (.node .red (.node .red .nil (-3, 1) .nil) (-2, 1) .nil) (0, 1) .nil),
    ("unequal-black-height", .node .black (.node .black .nil (-1, 1) .nil) (0, 1) .nil),
    ("red-root", .node .red .nil (0, 1) .nil)]
  fixtures.mapM fun (name, tree) => do
    let observation ← IO.lazyPure fun _ => redblackTreeObservation false id tree
    let observation ← IO.ofExcept observation
    let validity ← IO.lazyPure fun _ => redblackTreeObservation true id tree
    let accepted := match validity with | .ok _ => true | .error _ => false
    if accepted then throw (IO.userError s!"invalid public-tree fixture was accepted: {name}")
    let entries ← IO.lazyPure fun _ => Search.RedBlack.elements tree
    pure <| Lean.Json.mkObj [
      ("name", Lean.toJson name), ("publicTreeAccepted", Lean.toJson accepted),
      ("entries", Lean.toJson (entries.map (fun (key, value) => (toString key, value)))),
      ("tree", observation)]

private def redblackExamples : IO Lean.Json := do
  let intTable ← tableCase "int" (fun _ => true) id id
    (Search.RedBlack.ops Representations.SignedComparison.intLtb)
    Search.RedBlack.elements Search.RedBlack.elementsAux (redblackTreeObservation true id)
  let wordTable ← tableCase "word63"
    (fun key => decide (-(2 : Int)^62 ≤ key ∧ key < (2 : Int)^62))
    (BitVec.ofInt 63) BitVec.toInt
    (Search.RedBlack.ops Representations.SignedComparison.wordLtb)
    Search.RedBlack.elements Search.RedBlack.elementsAux (redblackTreeObservation true BitVec.toInt)
  let int64Table ← tableCase "int64"
    (fun key => decide (-(2 : Int)^63 ≤ key ∧ key < (2 : Int)^63))
    Int64.ofInt Int64.toInt
    (Search.RedBlack.ops Representations.SignedComparison.int64Ltb)
    Search.RedBlack.elements Search.RedBlack.elementsAux (redblackTreeObservation true Int64.toInt)
  let package := fun (result : Lean.Json × Lean.Json) =>
    Lean.Json.mkObj [("observations", result.1), ("tree", result.2)]
  let invariantCases ← redblackInvariantCases
  return Lean.Json.mkObj [
    ("schema", Lean.toJson (2 : Nat)), ("kind", Lean.toJson "redblack-examples"),
    ("tables", Lean.Json.arr #[package intTable, package wordTable, package int64Table]),
    ("invariantCounterexamples", Lean.Json.arr invariantCases.toArray)]

-- Flat structural observations retain empty children and slot holes. This
-- reporting traversal is outside every timed queue-operation interval.
private def binomialPreorder {K : Type} (showKey : K → String) :
    BinaryTree K → List Lean.Json → List Lean.Json
  | .nil, suffix => Lean.Json.null :: suffix
  | .node key left right, suffix =>
      Lean.toJson (showKey key) ::
        binomialPreorder showKey left (binomialPreorder showKey right suffix)

private def binomialExamples : Lean.Json :=
  let input : List Nat := [3, 1, 4, 1, 5, 9, 2, 3, 5]
  let queue := input.foldl
    (fun queue key => Search.BinomialQueue.insert Search.BinomialQueue.natGreater key queue) []
  let forest := queue.map (fun tree =>
    Lean.Json.arr (binomialPreorder toString tree []).toArray)
  Lean.Json.mkObj [
    ("schema", Lean.toJson (3 : Nat)),
    ("kind", Lean.toJson "binomial-examples"),
    ("sourceFold", Lean.Json.mkObj [
      ("input", Lean.toJson (input.map toString)),
      ("forest", Lean.Json.arr forest.toArray),
      ("slots", Lean.toJson queue.length),
      ("maximum", Lean.toJson
        ((Search.BinomialQueue.findMax Search.BinomialQueue.natGreater queue).map toString))])]

-- Generated or replay keys, checked machine values and the operation schedule
-- are prepared once and reused by all sample intervals.
-- The interval includes the actual queue operations, persistent snapshots and
-- retention of removal results. Decoding and structural reporting follow it.
private structure BinomialWorkloadConfig where
  implementation : String := "binomial"
  pattern : String := "random"
  schedule : String := "drain"
  size : Nat := 32
  rangeSize : Nat := 32
  seed : Nat := 1729
  warmups : Nat := 0
  repetitions : Nat := 1
  keysFile : Option String := none

private def parseBinomialOptions :
    List String → BinomialWorkloadConfig → List String → Except String BinomialWorkloadConfig
  | [], config, seen => do
    if config.pattern == "replay" then
      unless config.keysFile.isSome do throw "replay requires --keys-file"
      if seen.any (fun flag => ["--size", "--universe", "--seed"].contains flag) then
        throw "replay derives its keys from the file and does not accept generator options"
    else
      if config.keysFile.isSome then throw "key files require --pattern replay"
      if config.pattern == "random" then
        if config.rangeSize == 0 && config.size != 0 then
          throw "random generation requires a positive universe when draws are requested"
        unless config.rangeSize ≤ 2^63 do
          throw "int64 random universe exceeds the signed positive capacity"
      else
        if seen.any (fun flag => ["--universe", "--seed"].contains flag) then
          throw "deterministic patterns do not accept random generator options"
        if config.pattern == "ascending" || config.pattern == "descending" then
          unless config.size ≤ 2^63 do
            throw "int64 ordered input size exceeds the signed positive capacity"
    if config.repetitions == 0 then throw "repetitions must be positive"
    pure config
  | [flag], _, _ => .error s!"missing value for {flag}"
  | flag :: value :: rest, config, seen => do
    if seen.contains flag then throw s!"duplicate option: {flag}"
    let next ← match flag with
      | "--implementation" =>
        if ["binomial", "list"].contains value then pure { config with implementation := value }
        else throw s!"unsupported implementation: {value}"
      | "--pattern" =>
        if ["random", "replay", "ascending", "descending", "equal"].contains value then
          pure { config with pattern := value }
        else throw s!"unsupported binomial pattern: {value}"
      | "--schedule" =>
        if ["drain", "mixed", "merge", "padding"].contains value then
          pure { config with schedule := value }
        else throw s!"unsupported binomial schedule: {value}"
      | "--size" => do
        let some n := value.toNat? | throw "size must be a natural number"
        pure { config with size := n }
      | "--universe" => do
        let some n := value.toNat? | throw "universe must be a natural number"
        pure { config with rangeSize := n }
      | "--seed" => do
        let some n := value.toNat? | throw "seed must be a natural number"
        pure { config with seed := n }
      | "--warmups" => do
        let some n := value.toNat? | throw "warmups must be a natural number"
        pure { config with warmups := n }
      | "--repetitions" => do
        let some n := value.toNat? | throw "repetitions must be a natural number"
        pure { config with repetitions := n }
      | "--keys-file" => pure { config with keysFile := some value }
      | _ => throw s!"unknown option: {flag}"
    parseBinomialOptions rest next (flag :: seen)

private inductive BinomialQueueName where
  | main
  | left
  | right

private def binomialQueueName : BinomialQueueName → String
  | .main => "main"
  | .left => "left"
  | .right => "right"

private inductive BinomialEvent where
  | insert (queue : BinomialQueueName) (key : Int64)
  | save (label : String) (queue : BinomialQueueName)
  | delete (queue : BinomialQueueName)
  | merge (destination first second : BinomialQueueName)

private structure BinomialRunState (K Q : Type) where
  main : Q
  left : Q
  right : Q
  saved : List (String × String × Q) := []
  removals : List (Nat × String × Option K) := []

private def binomialGet {K Q : Type} (state : BinomialRunState K Q) : BinomialQueueName → Q
  | .main => state.main
  | .left => state.left
  | .right => state.right

private def binomialSet {K Q : Type} (state : BinomialRunState K Q)
    (name : BinomialQueueName) (queue : Q) : BinomialRunState K Q :=
  match name with
  | .main => { state with main := queue }
  | .left => { state with left := queue }
  | .right => { state with right := queue }

private def binomialEventJson : BinomialEvent → Lean.Json
  | .insert name key => Lean.Json.arr #[Lean.toJson "insert", Lean.toJson (binomialQueueName name),
      Lean.toJson (toString key.toInt)]
  | .save label name => Lean.Json.arr #[Lean.toJson "save", Lean.toJson label,
      Lean.toJson (binomialQueueName name)]
  | .delete name => Lean.Json.arr #[Lean.toJson "delete", Lean.toJson (binomialQueueName name)]
  | .merge destination first second => Lean.Json.arr #[Lean.toJson "merge",
      Lean.toJson (binomialQueueName destination), Lean.toJson (binomialQueueName first),
      Lean.toJson (binomialQueueName second)]

private def binomialStep {Q : Type} (insert : Int64 → Q → Q)
    (deleteMax : Q → Option (Int64 × Q)) (merge : Q → Q → Q)
    (state : BinomialRunState Int64 Q) (event : BinomialEvent × Nat) : BinomialRunState Int64 Q :=
  match event.1 with
  | .insert name key => binomialSet state name (insert key (binomialGet state name))
  | .save label name =>
    { state with saved := (label, binomialQueueName name, binomialGet state name) :: state.saved }
  | .delete name =>
    match deleteMax (binomialGet state name) with
    | none =>
      { state with removals := (event.2, binomialQueueName name, none) :: state.removals }
    | some (key, queue) =>
      let next := binomialSet state name queue
      { next with removals := (event.2, binomialQueueName name, some key) :: state.removals }
  | .merge destination first second =>
    binomialSet state destination (merge (binomialGet state first) (binomialGet state second))

private def binomialQueueJson (queue : Search.BinomialQueue.Queue Int64) : Lean.Json :=
  Lean.Json.mkObj [
    ("contents", Lean.toJson ((Search.BinomialQueue.contents queue).map
      (fun key => toString key.toInt))),
    ("slots", Lean.toJson queue.length),
    ("forest", Lean.Json.arr (queue.map (fun tree =>
      Lean.Json.arr (binomialPreorder (fun key => toString key.toInt) tree []).toArray)).toArray)]

private def binomialListJson (queue : List Int64) : Lean.Json :=
  Lean.Json.mkObj [
    ("contents", Lean.toJson (queue.map (fun key => toString key.toInt))),
    ("slots", Lean.Json.null), ("forest", Lean.Json.null)]

-- The independent finite model runs only after the operation clock stops.
-- It uses decoded mathematical integers, list insertion/concatenation and a
-- sorted maximum followed by one erase. No queue implementation is called.
private def binomialModelStep (state : BinomialRunState Int (List Int))
    (event : BinomialEvent × Nat) : BinomialRunState Int (List Int) :=
  match event.1 with
  | .insert name key => binomialSet state name (key.toInt :: binomialGet state name)
  | .save label name =>
    { state with saved := (label, binomialQueueName name, binomialGet state name) :: state.saved }
  | .delete name =>
    let queue := binomialGet state name
    match queue.mergeSort (fun left right => decide (right ≤ left)) with
    | [] =>
      { state with removals := (event.2, binomialQueueName name, none) :: state.removals }
    | maximum :: _ =>
      let next := binomialSet state name (queue.erase maximum)
      { next with removals := (event.2, binomialQueueName name, some maximum) :: state.removals }
  | .merge destination first second =>
    binomialSet state destination (binomialGet state first ++ binomialGet state second)

private def binomialCheck {Q : Type} (events : List (BinomialEvent × Nat))
    (contents : Q → List Int) (result : BinomialRunState Int64 Q) : Except String Unit := do
  let initial : BinomialRunState Int (List Int) := { main := [], left := [], right := [] }
  let reference := events.foldl binomialModelStep initial
  let normalize := fun (keys : List Int) => keys.mergeSort (fun left right => decide (right ≤ left))
  let actualRemovals := result.removals.reverse.map fun (index, name, key) =>
    (index, name, key.map Int64.toInt)
  unless actualRemovals == reference.removals.reverse do
    throw "queue removals differ from the independent finite maximum model"
  let names : List BinomialQueueName := [.main, .left, .right]
  unless names.all (fun name => normalize (contents (binomialGet result name)) ==
      normalize (binomialGet reference name)) do
    throw "final queue contents differ from the independent occurrence model"
  let actualSaved := result.saved.reverse.map fun (label, name, queue) =>
    (label, name, normalize (contents queue))
  let expectedSaved := reference.saved.reverse.map fun (label, name, queue) =>
    (label, name, normalize queue)
  unless actualSaved == expectedSaved do
    throw "saved queue identities or occurrence multisets differ from the independent model"

private def binomialSample {Q : Type} (phase : String) (index : Nat)
    (keys : List Int) (generator : Lean.Json)
    (events : List (BinomialEvent × Nat)) (empty : Q)
    (insert : Int64 → Q → Q) (deleteMax : Q → Option (Int64 × Q)) (merge : Q → Q → Q)
    (contents : Q → List Int) (observe : Q → Lean.Json) : IO Lean.Json := do
  let initial : BinomialRunState Int64 Q := { main := empty, left := empty, right := empty }
  let started ← IO.monoNanosNow
  let result ← IO.lazyPure fun _ => events.foldl (binomialStep insert deleteMax merge) initial
  let ended ← IO.monoNanosNow
  unless started ≤ ended do
    throw (IO.userError "monotonic clock moved backwards during queue operations")
  let checked ← IO.lazyPure fun _ => binomialCheck events contents result
  IO.ofExcept checked
  let removals := result.removals.reverse.map fun (index, name, key) =>
    Lean.Json.arr #[Lean.toJson index, Lean.toJson name,
      Lean.toJson (key.map (fun value => toString value.toInt))]
  let saved := result.saved.reverse.map fun (label, name, queue) =>
    Lean.Json.arr #[Lean.toJson label, Lean.toJson name, observe queue]
  return Lean.Json.mkObj [
    ("phase", Lean.toJson phase), ("index", Lean.toJson index),
    ("elapsedNs", Lean.toJson (ended - started)),
    ("keys", Lean.toJson (keys.map toString)),
    ("operations", Lean.Json.arr (events.map (fun event => binomialEventJson event.1)).toArray),
    ("removals", Lean.Json.arr removals.toArray),
    ("final", Lean.Json.mkObj [
      ("main", observe result.main), ("left", observe result.left), ("right", observe result.right)]),
    ("saved", Lean.Json.arr saved.toArray), ("generator", generator)]

private def binomialInputs (config : BinomialWorkloadConfig) :
    IO (List Int × List Int64 × Lean.Json) := do
  let (keys, generator) ←
    if config.pattern == "replay" then do
      let some path := config.keysFile | throw (IO.userError "missing replay key file")
      let keys ← readKeyFile path
      pure (keys, Lean.Json.null)
    else if config.pattern == "random" then do
      let initial := mkStdGen config.seed
      let generatorConfig : WorkloadConfig :=
        { pattern := "random", size := config.size, rangeSize := config.rangeSize, seed := config.seed }
      let generated ← IO.lazyPure fun _ => generatedKeys generatorConfig config.size initial
      let (keys, final) ← IO.ofExcept generated
      unless keys.all (fun key => decide (0 ≤ key) && decide (key.toNat < config.rangeSize)) do
        throw (IO.userError "generated key is outside its requested natural-number universe")
      let stateJson := fun (state : StdGen) => Lean.toJson [state.s1, state.s2]
      pure (keys, Lean.Json.mkObj [
        ("name", Lean.toJson "StdGen/mkStdGen/randNat"),
        ("initial", stateJson initial), ("final", stateJson final),
        ("draws", Lean.toJson config.size)])
    else if config.pattern == "ascending" then do
      let keys ← IO.lazyPure fun _ => (List.range config.size).map (fun key => (key : Int))
      pure (keys, Lean.Json.null)
    else if config.pattern == "descending" then do
      let keys ← IO.lazyPure fun _ => (List.range config.size).reverse.map (fun key => (key : Int))
      pure (keys, Lean.Json.null)
    else if config.pattern == "equal" then do
      let keys ← IO.lazyPure fun _ => List.replicate config.size (0 : Int)
      pure (keys, Lean.Json.null)
    else throw (IO.userError s!"unsupported binomial pattern: {config.pattern}")
  let converted ← IO.lazyPure fun _ =>
    if config.pattern == "replay" then
      keys.mapM Representations.DecodedBinomialQueue.checkedInt64
    else
      keys.mapM (fun key => Representations.DecodedBinomialQueue.checkedNat64 key.toNat)
  let some encoded := converted |
    throw (IO.userError "int64: input key is outside the signed range")
  unless encoded.map Int64.toInt == keys do
    throw (IO.userError "int64: input conversion changed a key")
  return (keys, encoded, generator)

-- Mixed deletion is deliberately key-dependent: insert each key, then delete
-- when its decoded integer is odd. Random keys therefore also determine the
-- operation pattern; no distributional claim is made about this schedule.
private def binomialSchedule (schedule : String) (keys : List Int64) (zero : Int64) :
    Except String (List BinomialEvent) := do
  let inserts := keys.map (BinomialEvent.insert .main)
  let drain := List.replicate (keys.length + 1) (BinomialEvent.delete .main)
  match schedule with
  | "drain" => pure (inserts ++ [.save "built" .main] ++ drain)
  | "mixed" =>
    let mixedEvents := keys.flatMap fun key =>
      [.insert .main key] ++ if key.toInt % 2 == 1 then [.delete .main] else []
    pure (mixedEvents ++ [.save "mixed-prefix" .main] ++ drain)
  | "merge" =>
    let split := keys.zipIdx.map fun (key, index) =>
      BinomialEvent.insert (if index % 2 == 0 then .left else .right) key
    pure (split ++ [.save "left-before" .left, .save "right-before" .right,
      .merge .main .left .right, .save "merged" .main, .delete .left, .delete .right] ++ drain)
  | "padding" =>
    pure (inserts ++ [.save "peak" .main] ++ drain ++
      [.save "drained" .main, .insert .main zero, .delete .main, .delete .main])
  | _ => throw s!"unsupported binomial schedule: {schedule}"

private def binomialWorkload (config : BinomialWorkloadConfig) : IO Lean.Json := do
  let (keys, encoded, generator) ← binomialInputs config
  let some zero := Representations.DecodedBinomialQueue.checkedNat64 0 |
    throw (IO.userError "checked zero is not representable")
  let scheduled ← IO.lazyPure fun _ => binomialSchedule config.schedule encoded zero
  let schedule ← IO.ofExcept scheduled
  let events ← IO.lazyPure fun _ => schedule.zipIdx
  let sampleFor := fun phase index =>
    match config.implementation with
    | "binomial" =>
      binomialSample phase index keys generator events ([] : Search.BinomialQueue.Queue Int64)
        (Search.BinomialQueue.insert Representations.DecodedBinomialQueue.int64Greater)
        (Search.BinomialQueue.deleteMax Representations.DecodedBinomialQueue.int64Greater)
        (Search.BinomialQueue.merge Representations.DecodedBinomialQueue.int64Greater)
        (fun queue => (Search.BinomialQueue.contents queue).map Int64.toInt) binomialQueueJson
    | "list" =>
      binomialSample phase index keys generator events ([] : List Int64) List.cons
        (Representations.DecodedBinomialQueue.listDeleteMax Representations.SignedComparison.int64Leb)
        List.append
        (List.map Int64.toInt) binomialListJson
    | _ => throw (IO.userError s!"unsupported implementation: {config.implementation}")
  let warmups ← (List.range config.warmups).mapM fun index => sampleFor "warmup" index
  let measured ← (List.range config.repetitions).mapM fun index => sampleFor "measured" index
  return Lean.Json.mkObj [
    ("schema", Lean.toJson (3 : Nat)), ("kind", Lean.toJson "binomial-workload"),
    ("clock", Lean.toJson "IO.monoNanosNow"), ("unit", Lean.toJson "ns"),
    ("timedRegion", Lean.toJson "precomputed queue operations, persistent snapshots and result retention"),
    ("config", Lean.Json.mkObj [
      ("implementation", Lean.toJson config.implementation), ("carrier", Lean.toJson "int64"),
      ("pattern", Lean.toJson config.pattern), ("schedule", Lean.toJson config.schedule),
      ("size", Lean.toJson keys.length), ("universe", Lean.toJson config.rangeSize),
      ("seed", Lean.toJson config.seed), ("warmups", Lean.toJson config.warmups),
      ("repetitions", Lean.toJson config.repetitions), ("keysFile", Lean.toJson config.keysFile)]),
    ("samples", Lean.Json.arr (warmups ++ measured).toArray)]

end ExtractSearchTree

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["examples"] =>
      IO.println (← ExtractSearchTree.examples).compress
      return 0
    | ["redblack-examples"] =>
      IO.println (← ExtractSearchTree.redblackExamples).compress
      return 0
    | ["binom-examples"] =>
      IO.println ExtractSearchTree.binomialExamples.compress
      return 0
    | "binom-workload" :: options =>
      let config ← IO.ofExcept (ExtractSearchTree.parseBinomialOptions options {} [])
      IO.println (← ExtractSearchTree.binomialWorkload config).compress
      return 0
    | "workload" :: options =>
      let config ← IO.ofExcept (ExtractSearchTree.parseWorkloadOptions options {} [])
      IO.println (← ExtractSearchTree.workload config).compress
      return 0
    | _ =>
      IO.eprintln "usage: extract-searchtree examples | redblack-examples | binom-examples | workload [options] | binom-workload [options]"
      return 2
  catch error =>
    IO.eprintln error.toString
    return 1
