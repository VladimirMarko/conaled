# VFA computational assumptions and Lean realization boundaries

**Status: bounded cross-cutting design note, 2026-11-02.** No later chapter
algorithm is implemented, no new Lean declaration is introduced, and no chapter
or candidate is accepted by this note. Only this Markdown file was written for
the assignment. No compiler, build, cache, dependency, or main-source change
was performed.

The purpose is to preserve exactly what a client may assume, what a concrete
implementation must prove, and what can actually be executed. The existing
conaled operations, laws, representations, and ordinary Lean decision
procedures provide the needed structure; a new hierarchy is unnecessary.

## 1. Pinned sources and evidence

The reference is VFA 2.1, release cover dated 2026-08-24 10:11. The verified
official versioned source archive is
<https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz>;
`SOURCE-RECOVERY.md` records its exact identity and recovery checks.

| Inspected source | SHA-256 |
| --- | --- |
| `Maps.v` | `19e79f4b7ac5bce3ffc246e19dd926b14fa5720b47d9618d2607d809d0504aea` |
| `ADT.v` | `87d7ca279b38d22f31ff56bf9f2b11103b382c325969a269bc542de27e4a8fe2` |
| `Extract.v` | `c132273a13fafe176573469e664b9cbe8dd3366ec00e2f9a3ab8ab1d42a2e15d` |
| `Decide.v` | `f929d55e2b7b39f2ba0bb72f2e70285dc8e10e64cf18322060bdbfc0552a4b26` |

All source line references below are to those files. Source inventories remain
unchanged. `RESOURCE-AND-EXECUTION-OBLIGATIONS.md` owns the broader resource and
benchmark audit; this note connects its assumptions to implementation seams.

Current project code was read, including `Squares.lean`,
`SquareKit/Relations.lean`, `SquareKit/ListFusion.lean`,
`Applications/Sequences/AbstractFIFO.lean`,
`Applications/Dijkstra/Store.lean`, `Applications/Checking/OrderCertificate.lean`,
the sorting contracts, and the two language decision implementations. The
in-progress Perm reflection examples and the staged table/resource drafts were
also inspected; their presence does not imply chapter acceptance.

## 2. Keep four kinds of statement distinct

| Kind | Lean treatment | Completion evidence |
| --- | --- | --- |
| Abstract data and operations, e.g. carrier, default, lookup, comparison | Ordinary parameters or operation fields in `Type`; preserve the arguments needed by clients. | A client theorem can be generic, but a runnable closed example must supply concrete executable values/functions. |
| Abstract behavioral laws, e.g. lookup-after-update or comparison reflection | Explicit theorem hypotheses or separate law fields in `Prop`. | Each concrete realization proves the fields. Do not introduce global `axiom` declarations merely because a Coq signature uses that keyword. |
| Mathematical observations, e.g. total maps, decoder, sortedness | Ordinary functions and predicates; equality is stated at the intended observation. | Proved refinement/equivalence, with invariants and injectivity only where needed. No executable equality oracle or efficient representation is implied. |
| Extraction, native primitives, timing, allocation, IO | An explicitly chosen Lean executable realization and, where appropriate, a separate model or experiment. | Kernel proofs establish the mathematical contract; compiler/runtime experiments and primitive boundaries remain separately described. |

The repository's README permits the foundational audit dependencies
`propext`, `Classical.choice`, and `Quot.sound`; it rejects admissions,
application-specific axioms, and native-evaluation proof shortcuts. A theorem
parameterized by a law is not a new axiom: its conclusion remains conditional
on that argument. Conversely, presenting a generic conditional theorem without
an actual realization does not complete a request for an executable algorithm.

Classical reasoning inside a proof is compatible with that audit policy.
An executable operation should receive or construct a computable decision
procedure for its actual domain. A `Classical.decEq` or classical proposition
decision used to state/prove a theorem is not evidence of an executable
algorithm for arbitrary function equality or arbitrary propositions.

## 3. Maps: observations, executable updates, and lost information

### Exact source statements

| Source location | Required interpretation |
| --- | --- |
| Maps 9–10, 16–28 | Functional extensionality supports equality of maps represented as `Nat → V`; it does not enumerate their keys or decide equality of arbitrary maps. |
| Maps 34–35 | Empty total-map observation is the constant supplied default. |
| Maps 42–44 | Update branches on executable Nat equality, returning the new value at the written key and the prior function elsewhere. |
| Maps 83–150 | Empty lookup, same-key update, different-key lookup, shadowing, self-update, and commuting distinct updates are proof obligations. They are not extra primitive assumptions for the function realization. |
| Maps 161–168 | A partial map is a function `Nat → Option V`; absence is `none`, and setting a value produces `some v`. |
| Maps 173–218 | The partial-map equations are specializations of the total-map laws, retaining the `some` premise in `update_same`. |

Use existing `Function.update` under `[DecidableEq K]` for the reusable key
generalization; the source Nat case has a constructive instance. The pinned
`Mathlib.Logic.Function.Basic` supplies `update_self`, `update_of_ne`,
`update_eq_self`, `update_idem`, and `update_comm`. Their query/write argument
orientation must match the source. Prove pointwise equality and use `funext`
when a function equality is requested; do not add a functional-extensionality
axiom to the project.

Useful statement shapes, with names deliberately left to chapter integration:

```lean
-- Schematic obligations; not new declarations in this planning note.
get q (set k v t) = if q = k then v else get q t
(fun q => get q (set k v t)) = Function.update (fun q => get q t) k v
Abs (set k v t) = Function.update (Abs t) k (some v)
```

The first two are total observations. The third preserves optional binding,
including a binding whose value happens to equal the default. None states
equality of concrete function/list/tree representations.

### Boundaries that must survive the port

- Both `K → V` and `K → Option V` are unrestricted function spaces. The latter
  can contain infinitely many bindings. Finite update histories and finite
  data structures occupy particular images; they do not identify the whole
  function type with an enumerable finite map.
- Forgetting absence by `fun q => (m q).getD d` is not injective: no binding
  and an explicit binding to `d` have the same total observation. Separate
  `bound` evidence is needed when an interface talks about stored bindings.
- First-binding association lists may contain shadowed old entries. Raw list
  membership does not then mean “current stored binding.” Enumeration laws
  need their own invariant or cleanup operation.
- Function equality forgets update history. It does not prove closure-chain
  lookup time, storage use, or equivalence of allocation behavior. If such
  claims are made, retain an explicit history/representation and an independent
  measured traversal, rather than assign history cost to an extensional map.

The existing staged `TablePreparation` draft already separates `Ops`, `Laws`,
and pointwise `ObservedEq`, and checks function/association-list realizations
and a common two-write client. Its `withDefault`, `binding_iff`,
`forget_default_not_injective`, and shadowed-membership example cover the
important observation boundaries. Reuse that seam when the owning chapters
are reached; its status remains staged, not accepted.

## 4. Module Type axioms are implementation obligations

### Source interface inventory and exact law scope

| Source interface | Data/operations to preserve | Laws to pass abstractly and prove concretely |
| --- | --- | --- |
| `Table`, ADT 50–87 | Carrier, Nat keys, value type, explicit default, empty/get/set. | `get_empty_default`, `get_set_same`, `get_set_other` at 78–85. All three are unconditional on represented table states. |
| `ValType`, ADT 100–103 | Value type and a particular default value. | No behavioral axiom. An explicit default suffices; do not require a global distinguished `Inhabited` value unnecessarily. |
| `ETable_first_attempt`, ADT 300–320 | Table operations plus bound/elements. | The unguarded completeness direction is proved for raw trees at 342–349. The soundness direction at 351–360 is the failed design: its proof lacks BST validity and ends admitted. Do not generalize that failed obligation to all raw trees or discard the valid completeness result. |
| `ETable`, ADT 375–414 | Table plus `rep_ok`, bound, elements. | Empty validity and set preservation at 385–388; bound laws at 392–399; elements soundness/completeness at 403–412 require `rep_ok`. Included Table equations and the bound equations remain unconditional. |
| `SimpleTable` and sharing examples, ADT 626–670 | Types and default, with selected type/value equalities exposed. | These demonstrate module typing/encapsulation, not extra mathematical axioms or physical heap sharing. |
| `ETableAbs`, ADT 806–847 | Operations, partial-map `Abs`, and `rep_ok`. | Valid empty/set; empty abstraction; bound/get/set correspondence; map-of-elements correspondence. Preserve exactly which laws require validity and which do not. |
| `Queue`, ADT 978–992 | Carrier, empty/is_empty/enq/deq/default-valued peek. | Six algebraic equations, including literal equality of queue representations in the dequeue equations. Prove these for the requested list realization; do not replace them silently by equality only after decoding. |
| `QueueAbs`, ADT 1057–1070 | The same operations and list-valued `Abs`. | Four decoder laws for empty/enqueue/peek/dequeue, with no invariant premise. **No law for the declared `is_empty` operation occurs in this signature.** |
| `ETableSubset`, ADT 1342–1369 | Table plus bound/elements over a carrier that can already enforce validity. | Bound and elements equations without a separate `rep_ok` argument. In `TreeETableSubset` the carrier is a subtype of valid trees, so this does not justify dropping BST validity from raw-tree claims. |

This scope matters. A reusable law record may allow validity-dependent
operations, but the source's unconditional `Table` equations still need
unconditional source-facing theorems or a genuinely restricted carrier.
Do not weaken them merely because a generalized record offers an invariant
parameter. Conversely, do not strengthen ETable's elements laws to arbitrary
raw trees by omitting their premise.

The source itself explains at ADT 129–142 that an implementation proves the
theorems written as axioms in the interface. Preserve this discipline in Lean.
The function and association-list instances can use `Valid := True`; a tree
enumerator needs its actual invariant. Nonvacuity is established by valid empty
and validity preservation, together with concrete clients.

### Observation gaps are not automatically new law fields

`ETableAbs.elements_relate` at ADT 843–845 states equality of partial-map
observations with `map_of_list (elements t)`. It does not itself establish
sorted enumeration or absence of duplicate keys. With first-binding semantics,
redundant/shadowed suffix bindings can disappear from that map observation.
The stronger `elements_spec` exercise at ADT 766–774 independently requests
sortedness, nonduplication, and further specification directions. Retain those
as additional proved obligations, rather than infer them from map equality.

On valid states, a finite elements list plus this abstraction equation does
establish that the observed map has finite support. It does not establish that
every inhabitant of the unrestricted partial-map type is finite.

Similarly, the missing `QueueAbs.is_empty` law must remain visible in the
coverage map. Its four laws alone permit replacing `is_empty` by an arbitrary
Boolean function. The concrete source implementation can prove an additional
emptiness correspondence, or a separately described strengthened interface
can require one. It must not be presented as a consequence of the original
signature. The existing queue resource counterexample concerns the actual
observing peek and is unaffected by this interface omission.

### Encapsulation, subtypes, and semantic independence

ADT 501–759 contrasts transparent, overly sealed, and selectively exposed
modules. Lean's narrow adaptation should make `V` and the supplied default
explicit parameters while keeping client proofs generic in the state carrier
and operations. Prove their observations through laws, not by inspecting tree
constructors. Type sharing is ordinary agreement of parameters/definitions;
it does not require a separate module-generativity framework.

`Sequences.AbstractFIFO.Ops` and its separate `Simulation` already demonstrate
the desired pattern. `Simulation.client_eq`, `representation_independent`, and
composed simulation give semantic independence of ordinary clients. They do
not claim that Lean's namespace/private/opaque mechanisms reproduce every Coq
module visibility rule. The source's `Fail` examples need explicit language
adaptations, not fabricated mathematical contradictions.

ADT 1173–1267 and 1378–1398 distinguish witness-carrying subtypes from
existential propositions. Use existing Lean `Subtype` for `{x // P x}`,
`Subtype.val` and `.property`, and actual proved invariant-preserving
constructors. A proof of `∃ x, P x` alone is not an executable witness producer.
Classical choice may select a witness in a noncomputable specification; it does
not replace the requested constructive subtype operation. No new subset or
vector hierarchy is needed merely to reproduce the teaching examples.

## 5. Executable comparisons and decisions

### Reuse the two existing presentations

For a Boolean implementation, keep the computation and its law separate:

```lean
test : X → Bool
law : ∀ x, test x = true ↔ P x
```

For a decision implementation, use existing `Decidable (P x)` or
`DecidablePred P`. The current Perm source contains the relevant concrete
pattern:

```lean
decidable_of_bool (decide (a < b)) (ltb_reflect a b)
```

Its `reflected_true_branch` and `reflected_false_branch` exercise the actual
decision constructors. This is in the pending Perm candidate, so use its
accepted identity once that gate is passed. `OrderCertificate.reference_correct`
and `adjacent_correct` already consume an independent Boolean relation law,
while `checkerSquare` and `checkedLength_correct` connect the validated checker
to another consumer. These are appropriate shared interfaces for later
comparison adaptations.

### Exact Decide obligations and adaptations

| Source statements | Lean treatment |
| --- | --- |
| Decide 21–26, 55–103: `reflect`, two proofs of `3 < 7`, Boolean branch/proposition coherence. | Use a Boolean correctness equivalence and a proof-carrying `Decidable` adapter; retain true and false branch demonstrations. No new reflection framework is needed. |
| Decide 121–173: generic `sumbool A B`, including the case where both propositions hold and either constructor is possible. | A sum of lifted proofs in `Type`, such as `Sum (PLift A) (PLift B)`, preserves both data tags. Do not replace arbitrary `sumbool A B` with `Decidable A`; that is appropriate only for the proposition/negation specialization. |
| Decide 192–213 and 232–242: two ways to build a decision from reflection and their equality. | Build ordinary `def` values with the existing Boolean-to-decision adapter or direct constructive instances; prove the requested agreement. Identical propositions alone do not demonstrate their computational behavior. |
| Decide 247–284: insertion sort branching on `le_dec`, with the `insert_sorted_le_dec` exercise. | Supply a constructive `[DecidableRel (· ≤ ·)]`, preserve the direct source recurrence, and connect it to the already accepted Sort adapter when this chapter is reached. |
| Decide 328–369: two pedagogical global axioms, `max_with_axiom`, and a proof despite blocked computation. | Do not introduce either global axiom. Preserve the distinction between a proposition argument `h : ∀ i j : Nat, i < j ∨ ¬ i < j` and a decision argument `d : ∀ i j : Nat, Decidable (i < j)`. The max demonstration can branch on `d`; prove its result by cases, then instantiate an actual computable Nat decision. An uninstantiated decision parameter explains why closed reduction cannot choose a branch. |
| Decide 388–411: aborted opaque-reflection computation and successful standard-library computation. | Document the Rocq opacity phenomenon and demonstrate actual Lean branch computation with the chosen definition. Do not import `Qed`/`Defined` as Lean syntax or assert that every opaque Lean declaration is unexecutable. |
| Decide 450–471: list equality decisions, both Boolean results, and `list_nat_in`/`in_4_pi`. | Reuse constructive Nat equality and standard list equality/membership decisions; retain order-sensitive unequal/equal list examples and the membership result for the exact source list. |
| Decide 481–504: Boolean versus decision-valued implementation tradeoffs. | Describe the two actual local interfaces and examples. The source's possible efficiency advantage is not a universal performance theorem. |

Two source qualifications should be recorded explicitly:

- At Decide 337–339, the claim that propositional disjunction is not inductive
  is inaccurate. The relevant distinction is its sort and permitted
  elimination/computational content, not the absence of constructors.
- At Decide 275–282, destructing `le_dec a x` provides `a ≤ x` or `¬ a ≤ x`.
  The prose's `¬ a < x` in the false branch is a typo and must not become the
  Lean branch specification.

Lean's classical foundations can provide a noncomputable decision for an
arbitrary proposition. That is not an algorithm deciding all propositions.
For executable branches, select a computable instance or branch on an explicit
Boolean with a proved law. The law itself may be an opaque proof in `Prop`:
the branch can be computed from the Boolean without evaluating proof content.
That distinction is why the existing Lean Boolean adapter need not reproduce
Rocq's exact opaque `reflect` evaluation behavior.

The repository already has two further examples worth reusing as evidence:
`LanguageDerivatives.decideMembership` in `Applications/Languages/Regex.lean` derives a
`Decidable` from a Boolean recognizer correctness theorem;
`LanguageWitnesses.Decision` in `Applications/Languages/Parser.lean` returns
actual witnesses of a type or a refutation and proves `test_correct`.
The latter is proof-relevant parser data, not a reason to replace ordinary
`Decidable` in VFA's proposition-valued comparisons or list membership.

## 6. Extract: replace global integer axioms with proved realizations

### Exact active assumptions and minimal dependencies

Extract 113–132 introduces one carrier, one decoder, two Boolean operations,
and three active axioms. Their narrow Lean shape is:

```lean
-- Parameters and separate law hypotheses; schematic, not compiled here.
W : Type
decode : W → Int
ltb leb : W → W → Bool
decode_injective : Function.Injective decode
ltb_correct : ∀ x y, ltb x y = true ↔ decode x < decode y
leb_correct : ∀ x y, leb x y = true ↔ decode x ≤ decode y
```

Use ordinary section parameters first. If repeated clients justify packaging,
reuse `Squares.Rep` for the carrier/decoder and keep comparison operations and
laws separate. The decoder need not be surjective or have an inverse. Do not
introduce a global “machine integer” axiom family or require every represented
value to be an arbitrary mathematical integer.

| Source statement | Needed law and concrete proof responsibility |
| --- | --- |
| `int`, `Abs`, `Abs_inj`, Extract 113–121 | Concrete carrier and decoder; prove injectivity for the chosen realization. Finite carriers cannot cover all of `Int`. |
| `ltb_lt`, Extract 126–128 | Prove the actual Boolean less-than operator reflects decoded signed order. |
| `leb_le`, Extract 130–132 | Prove the actual Boolean less-or-equal operator reflects decoded signed order. |
| Reflection lemmas, Extract 162–200 | Derive from those comparison laws and standard Int decisions; they are not further primitive assumptions. |
| `ins_int`/`sort_int` and `sort_int_correct`, Extract 230–273 | Comparator correctness and Int order laws suffice for decoded sortedness; occurrence preservation is a direct property of the source sorting recurrence. Decoder injectivity is not needed merely for this sorting contract. |
| BST lookup/insert and `lookup_insert_neq`, Extract 293–336 | With neither strict comparison true, Int order gives equal decoded keys; decoder injectivity then identifies the original keys. Preserve this extra requirement for distinct-key behavior. |
| Optional `int_elements`, Extract 339–345 | Supply the actual integer-keyed BST invariant and enumeration proofs; comparison laws do not eliminate the tree invariant. |

This dependency distinction prevents over-generalization in either direction:
do not demand key identity reflection for a sorting claim that only orders by
decoded keys, and do not infer distinct original BST keys from distinctness
or equality of their decoded values without the appropriate injectivity fact.
Likewise, a permutation of decoded lists does not automatically prove a
permutation of original records under a noninjective decoder. Retain the
algorithm's direct original-element permutation theorem.

### Two useful realizations with different claims

1. **Unbounded mathematical Int.** Take `W := Int`, decoder `id`, and Boolean
   comparisons from constructive Int decisions. All three law obligations
   have ordinary proofs. This supports the `insZ`/`sortZ` correctness request
   at Extract 73–89 and realizes the abstract comparison assumptions. It does
   not claim to be OCaml's finite integer representation.
2. **A specified signed finite word.** Reuse the existing Lean `BitVec w`
   representation and its signed `toInt` observation, or an explicit bounded
   integer subtype. Define/sign-check comparisons against that signed
   observation and prove decoder injectivity. The pinned Mathlib
   `Mathlib/Data/BitVec.lean` already uses the core `BitVec.eq_of_toInt_eq` fact
   and supplies finite-word algebra; there is no reason to rebuild bitvectors.
   Choose and record `w` and the signed range. A mathematical `BitVec 63`
   model, when that is the selected OCaml payload width, is not automatically
   a verified native Lean/OCaml backend bridge.

For positive width, the signed range is
`[-2^(w-1), 2^(w-1))`. Conversions from Int require that range for an exact
roundtrip; otherwise they wrap. Unsigned `UInt64` comparison is not signed
order, and 64 raw bits are not the same representation as a 63-bit tagged
payload. Runtime word width/platform details must be confirmed for the later
execution experiment, rather than guessed from the type name.

A scoped repository search found no existing VFA/OCaml signed-integer adapter
in `Applications`, `SquareKit`, or `Examples`; a `UInt8` IO use is not such an
adapter. Standard Lean/Mathlib Int/BitVec facilities are available, but their
specific realization and source-algorithm bridges remain future chapter work.

### Overflow: the false law must remain a counterexample

Extract 139–156 presents the commented-out `ocaml_plus_plus` law as unsound
for actual finite machine arithmetic. Do not activate it as a law field.
The abstract comparison interface by itself does not assert finiteness; the
addition equation can hold for unbounded Int. The precise failure concerns
its purported finite wrapping realization.

Retain a checked overflow witness for a small signed width and then prove one
of the meaningful replacement shapes:

```lean
-- A range-guarded integer observation:
inSignedRange w (decode x + decode y) →
  decode (wordAdd x y) = decode x + decode y

-- Or a total modular observation with a separately defined/proved normalization:
decode (wordAdd x y) = signedNormalize w (decode x + decode y)
```

For example, four-bit signed 7 plus 1 represents -8, not 8. This is a proposed
independent expected case, not a newly checked theorem in this note. Include
a negative-versus-nonnegative comparison case as well, so an unsigned
comparison cannot accidentally pass the realization examples.

### Decoder and execution correspondence

For a sort adapter, a useful commuting statement has the shape

```lean
(sourceSort leb xs).map decode =
  sourceSort (fun a b : Int => decide (a ≤ b)) (xs.map decode)
```

provided the primitive comparison correspondence and direct recurrence bridge
are proved. This fits an ordinary `Squares.Square`. It does not require decoder
surjectivity, prove machine timing, or identify two implementations' allocation
behavior. Reuse the accepted Sort adapter when available; do not port Extract's
duplicate sorter before its chapter gate merely to obtain this statement now.

Extract's type directives for Bool/List/pairs and external integer primitives
(38–59, 113–132, 349–350) become a documented Lean compile/run path with
concrete realizations. The requested performance driver is separately owned
by the extraction/resource audit. The conaled `Compiler.lean` correctness
theorem concerns its own modeled compiler; it does not certify Lean's native
compiler or Rocq-to-OCaml extraction.

`Squares.lean` explicitly distinguishes proof fields in `Prop` from
specification functions stored in `Type`. Calling a function “Abs” or “spec”
does not alone prove it is erased from a generated executable. Keep executable
operations separate from proof-only uses and state what the actual build runs.
Similarly, a source unary numeral presentation does not imply Lean's runtime
Nat representation or comparison cost. The checked unary-cost preparation
provides a particular model, not that runtime claim.

## 7. Existing shared APIs to consume, not replace

| Capability | Existing source inspected | Appropriate use and limit |
| --- | --- | --- |
| Decoding/refinement | `Squares.Rep`, `Squares.Square`, composition | Decoder correspondence for total operations; arbitrary decoders need not be injective or surjective. Add those assumptions only at consumers that require them. |
| Relational observations | `Relational.RelRep`, `RelSquare`, composition in `SquareKit/Relations.lean` | Invariant-dependent/many-representation semantics; do not choose an arbitrary functional decoder merely to fit a preferred interface. |
| Representation-independent FIFO clients | `Sequences.AbstractFIFO.Ops`, `Simulation.client_eq`, `representation_independent` | Reuse the operation/law separation. Its Option-valued head requires an explicit default adapter for source peek. It does not supply source representation equalities or charged-peek amortization automatically. |
| Fold/update history transport | `SquareKit.ListFusion.foldl_reachable`, `foldr_reachable` | Batch clients with actual invariant preservation; avoid another generic instruction-word executor. |
| Total/partial table observations | Staged `TablePreparation` definitions and proofs | Small shared seam and concrete realizations; not yet integrated or accepted, and not an enumeration theorem. |
| Bounded mutable-style store observation | `Dijkstra.Store.lookup_write` and `accum_lookup` | Checked Vector/Fin operations; not a general unbounded-key or explicit-binding map implementation. |
| Comparator checking and composition | `OrderCertificate` correctness/refinement/consumer results | Bool/Prop law reuse, with transitivity only for adjacent/all-pairs equivalence. |
| Comparison branch data | Pending Perm `reflectedLt`, true/false branch cases | Standard Boolean-to-Decidable adaptation after that candidate is accepted. |
| Key sorting contracts | `KeySorted`, `StableSort`, `insertionOn_spec`, `StableSort.map` | Separate key order, occurrence preservation, and payload stability. Do not impose an order on payloads or infer stability from decoded sortedness alone. |
| Existing decision algorithms | Regex Boolean recognition plus `decideMembership`; witness parser `Decision` | Two already demonstrated computational presentations; use ordinary Decidable for propositions and preserve actual witnesses only when the source asks for them. |
| Explicit resource accounting | `Resources.Measured`, `run`, `budget`, potential theorems | Charge the actual represented traversal/trajectory. The checked queue adapters already consume these APIs; value refinement alone supplies no runtime cost theorem. |
| Finite integer representation | Standard Lean/Mathlib Int and BitVec facilities | Realize the selected signed width and comparison laws; no existing source-specific machine/backend bridge was established by this survey. |

## 8. Concrete follow-through obligations in chapter order

This note records requirements for later consuming tickets, not permission to
start their algorithms before earlier chapter acceptance.

- **Maps #1008:** bridge the literal source update to `Function.update`, prove
  the six laws and partial specializations, retain exact source observations,
  and keep absence/default and function-equality boundaries explicit.
- **ADT #1010:** package operations and proved laws at the narrow existing
  seam; preserve unconditional versus invariant-dependent statements; retain
  the failed raw-tree enumeration counterexample and separately requested
  sorted/duplicate-free elements properties. Account explicitly for the
  missing QueueAbs emptiness law and literal versus decoded queue equality.
- **Extract #1011:** use law parameters rather than global axioms; prove both
  the Int and selected finite signed realization; prove actual sorting/tree
  bridges, overflow qualifications, and the optional integer-key elements
  obligations. Treat compile/run and benchmark evidence separately.
- **Decide #1016:** retain generic sum examples and the proposition/negation
  decision specialization, both branch values, proof/computation distinctions,
  constructive list equality/membership, and source opacity adaptations.
  The two pedagogical axiom declarations become parameterized demonstrations
  plus concrete realizations, never trusted project axioms.

Meaningful checked uses should expose the boundaries: overwrite at one key;
an unrelated key; explicit default binding versus absence; shadowed list
membership; the same client on two representations; negative signed keys;
finite-word overflow; both decision branches; an abstract decision parameter
followed by a concrete executable instance; and equal/unequal list decisions.
Reuse existing staged or project examples where they already establish the
needed connection. No new framework or quota of duplicate examples is needed.

All Lean snippets above are proposed statement shapes, not compiler-checked
new code. The inspected existing declarations supply evidence for the reuse
choices. Owning chapters must still provide their exact source coverage,
checked realizations, statement review, clean candidate build/audit, and
independent acceptance reviews. This note makes no additional acceptance claim.
