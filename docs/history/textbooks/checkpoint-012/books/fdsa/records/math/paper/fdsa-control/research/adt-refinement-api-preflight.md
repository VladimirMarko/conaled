# Model-oriented Set/Map contracts and refinement: API preflight

Status: **bounded read-only preparation; no implementation, compilation,
chapter activation, or acceptance**. Date: 2026-11-02.

## Recommendation

The existing construction for this source is already present: an explicit
representation relation, a preserving `Relational.RelSquare`, ordinary
composition of operations, and existential composition of representation
routes. Do not add another general refinement record, ADT syntax, interpreter,
state carrier, or preservation hierarchy for Chapter 6.

There is a justified smaller domain gap: operation-only Set and Map interfaces,
separate proposition-valued law packages matching the seven and six source
laws, and thin specialization/translation theorems. The inspected local
application interfaces do not already provide those exact Set/Map contracts.
`Sequences.AbstractFIFO` is an established pattern and a source of shared
relational machinery; its FIFO-specific operation signature is not itself a
Set/Map interface.

Keep new domain statements universe-independent. The legacy square records
have one common universe parameter, whereas ordinary laws and the pinned
`Relator.LiftFun` do not need that restriction. This is an encoding boundary to
handle in an optional bridge, not a reason to weaken the public domain
contracts or redesign all existing foundations.

No unit is frozen by this report. In particular, it neither changes the
initial Chapter 2 prefix `c80eec92f5458eccfd1c34c8314d666c2a1e3847` nor becomes
an additional prerequisite for that prefix. The original Chapter 6 inventory,
concrete implementations, exercises, and operational obligations remain intact.

## Evidence and provenance

Read the applicable `AGENTS.md`, architecture/domain guidance, `GLOSSARY.md`,
ADRs 0001, 0002 and 0010, the language direction, the preservation-contract
inventory, and the existing implement guidance. This is planning inside the
existing workflow, not a newly initiated implementation or acceptance loop.
The inventory was used as a guide to actual definitions, not as proof that a
single abstraction already handles every preservation family.

The code inspection used the local canonical checkout at
`/workspace/scratch/845aa1048b05/conaled`. The source reading includes all of
`Applications/Sequences/AbstractFIFO.lean`, `SquareKit/Relations.lean`,
`SquareKit/RelationComposition.lean`, `SquareKit/RelationTransport.lean`,
`Applications/Sequences/Symmetric/Observation.lean`,
`Applications/Sequences/RandomAccess/Representation.lean`,
`Applications/Resources/FIFOContracts.lean`, and the relevant ordinary and
optional-syntax FIFO examples. The operation/invariant pattern in
`Applications/Incremental/Stateful.lean` was also checked. Searches of the
application paths and Set/Map law names found no existing exact seven-law Set
or six-law Map package; this is a bounded local finding, not a claim about all
possible external libraries.

Primary book evidence is the retained complete Chapter 6 extraction, printed
pp. 77–83, and `research/chapter06-obligations.md` (C06-001–074). The full
`book-source/Set_Specs.thy` and `Map_Specs.thy` were read, with the pertinent
ordered-list laws in `List_Ins_Del.thy`, `AList_Upd_Del.thy` and
`Sorted_Less.thy`. No source algorithm is implemented in this preflight.

| Evidence | Retained identity |
| --- | --- |
| Book, July 27, 2026 edition | SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645` |
| Isabelle companion | `f86f290225eebcc52c1ae7dba2e098f405f51c21` |
| `Set_Specs.thy` | SHA-256 `601f6ff60e58de9d0c608b3b40ddf9105f9eb9fbeb7caabfeb9efc038d0d99d0` |
| `Map_Specs.thy` | SHA-256 `54e97e50dc6e44d4d5533b92a109b50e781520c99bd0c50637b42470493b3e5d` |
| `AList_Upd_Del.thy` | SHA-256 `42f603405ff3fec058ba284c76183924139c42711ec66edaf623bd5b0a921f9a` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Lean | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` / 4.35.0 |

Pinned companion URL prefix:
`https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/`.
The original inventory records the BSD-3-Clause companion license and the
limits of the PDF/companion relationship. This report reuses those receipts;
it makes no new claim that the later companion revision built the pinned PDF.

## 1. Exact source contracts and justified thin interfaces

The following names are **proposals**, not current declarations:
`Collections.Sets.Ops`/`Laws` and `Collections.Maps.Ops`/`Laws`, placed by
subject under `Applications`, for example in `Applications/Collections/Set.lean`
and `Applications/Collections/Map.lean`. A different domain-consistent path
would not change the mathematics. Do not introduce a general `ADT` record to
hold both these small signatures and every future signature.

### Set: seven laws

Operations have independent carriers `α : Type u`, `Q : Type v`:
`empty : Q`, `insert : α → Q → Q`, `delete : α → Q → Q`, and
`isin : Q → α → Bool`. Supply `decode : Q → Set α` and `Valid : Q → Prop`
separately as specification arguments. They are not executable client fields.

The seven obligations in `Set_Specs.thy:18–24` are:

| Source field | Exact Lean-facing meaning |
| --- | --- |
| `set_empty` | `decode ops.empty = ∅` |
| `set_isin` | `Valid q → (ops.isin q x = true ↔ x ∈ decode q)` |
| `set_insert` | `Valid q → decode (ops.insert x q) = decode q ∪ {x}` |
| `set_delete` | `Valid q → decode (ops.delete x q) = decode q \ {x}` |
| `invar_empty` | `Valid ops.empty` |
| `invar_insert` | `Valid q → Valid (ops.insert x q)` |
| `invar_delete` | `Valid q → Valid (ops.delete x q)` |

No linear order, equality algorithm, finite semantic carrier, or decidable
invariant belongs in these abstract laws. Bool reflection avoids demanding a
global membership decision for arbitrary `Set α`. A concrete executable
membership operation supplies its own algorithm; the law says that its result
reflects membership on valid represented states. An abstract Boolean model
for all sets can instead use an explicitly classical specification, but must
not be presented as an executable membership algorithm.

The source's `Set2` adds union, intersection and difference with **both** input
validity hypotheses. That extension is not part of the seven basic fields.
Exercise 6.1 supplies union and targets-minus-cutters difference, but not the
additional intersection operation of `Set2`; do not manufacture a `Set2`
instance or reverse the exercise's difference arguments silently.

### Map: six laws, with lookup itself the abstraction

Use independent `α : Type u`, `β : Type v`, `M : Type w`. The proposed
operation fields are `empty : M`, `update : α → β → M → M`,
`delete : α → M → M`, and `lookup : M → α → Option β`. The model is the
ordinary function type `α → Option β`; do not define another partial-map
carrier or require a default value of β.

`Map_Specs.thy:17–22` gives:

| Source field | Exact semantic or invariant obligation |
| --- | --- |
| `map_empty` | `ops.lookup ops.empty = fun _ => none` |
| `map_update` | On valid m, `ops.lookup (ops.update a b m)` is `ops.lookup m` updated at a to `some b`. |
| `map_delete` | On valid m, `ops.lookup (ops.delete a m)` is `ops.lookup m` updated at a to `none`. |
| `invar_empty` | `Valid ops.empty` |
| `invar_update` | `Valid m → Valid (ops.update a b m)` |
| `invar_delete` | `Valid m → Valid (ops.delete a m)` |

There is no seventh independent lookup-simulation law: the public lookup is
also the abstraction, so its own observation law is reflexive. The empty laws
have no precondition. Mutation laws remain restricted to valid input.

**Avoid an accidental global `DecidableEq α`.** Pinned
`Mathlib/Logic/Function/Basic.lean:633–642` declares `Function.update` in a
section with `[DecidableEq α]`. The record can instead state each mutation's
single semantic field as a grouped pointwise contract. For update, this is

`lookup (update a b m) a = some b ∧
 ∀ x, x ≠ a → lookup (update a b m) x = lookup m x`.

Deletion replaces `some b` by `none`. Under any supplied key decision, the
existing `Function.eq_update_iff` at lines 696–698 is exactly the equivalence
between this pair and the original function equality. A local classical
instance suffices for a noncomputable notation/correspondence theorem; it
need not become an assumption on the operational interface. This grouping
retains one semantic law per mutation and all unaffected-key equations. It
is not a weaker query-at-the-updated-key specification.

The other directly useful pinned lemmas are `Function.update_self a v f`
(line 644), `Function.update_of_ne h v f` (648), `Function.update_apply f a b x`
(664), and `Function.update_eq_self a f` (709). Keep the direction of
`eq_update_iff` distinct from `update_eq_iff`: the former has the newly observed
function on the left of the equality, matching the source Map law.

The supplied `empty` already witnesses that the representation carrier has a
value. No additional global `Inhabited M`, `Inhabited α` or `Inhabited β` is
needed. In particular β may be Empty: `Option β` and its constant-none function
still exist, and insertion parameters become vacuous where no β value exists.

## 2. Existing generic constructions that suffice

| Inspected API | Exact use and boundary |
| --- | --- |
| `Squares.Rep`, `Square` (`Squares.lean:32–41`) | Total decoder plus commuting implementation/specification arrows. Neither injectivity nor surjectivity is a field. For a raw invariant-conditioned implementation, first restrict to valid states or use a relation; the total `commutes` law cannot be asserted on invalid raw states. |
| `Squares.compose` (63), `Rep.after` (83), `vertical` (92) | Horizontal operation composition, composed decoders, and vertical refinement composition. `vertical da db f g middle` requires `∀ x, f.spec x = g.impl x`; it retains both actual operation arrows. |
| `Relational.RelRep`, `RelSquare` (`SquareKit/Relations.lean:17–25`) | Relation and preservation, with no totality/uniqueness/reflection fields. The raw valid-graph relation directly contains both validity and decoding equality. |
| `Relational.compose` (42), `terminal` (59), `product` (66), `pair` (81) | Sequential operations, nullary input and explicit argument products. Product relations retain both component premises, so binary ADT operations must supply both valid inputs. |
| `Relational.graph`, `ofSquare`, `toSquare` (126–143) | Exact total-square specializations of the relational construction. These do not turn a partial valid-graph relation into a total raw-state decoder contract. |
| `Relational.witnessSquare`, `witness_compose` (153–161) | Existing mathematical witness presentation. It is not a runtime erasure theorem and need not become an ADT's executable state. |
| `Relational.compRel`, `existentialSquare` (`RelationComposition.lean:12–35`) | Compose implementation routes through an actual intermediate witness; the latter maps that witness by `f.spec` and uses pointwise middle-map agreement. |
| `transportRelations`, `existential_reassociate` (39–60) | Replace endpoint relations by proved equivalent predicates and retain both operation arrows; reuse for simplifying valid-graph compositions and three-stage reassociation. |
| `Relator.LiftFun` (`Mathlib/Logic/Relator.lean:17–35`) | The unbundled preservation proposition `∀ ⦃a b⦄, R a b → S (f a) (g b)`, with four independent Sort universes. This is a direct minimal public statement when legacy bundling would couple universes. |
| `Relation.Comp`, `Relation.comp_assoc` (`Mathlib/Logic/Relation.lean:144,174`) | Existing ordinary existential relation composition and associativity. No parallel relation definition or new associativity proof framework is needed. |
| `SquareKit.RelationTransport.image_comp`, `requirement_comp` (27,36) | Existing predicate transport. `requirement` is universal partial correctness and can be vacuous when no related target exists; it alone cannot supply a correct initialized implementation or a simulation witness. |

Pinned `Relator.lean` defines `LiftFun` but does not supply a general named
`LiftFun.comp` theorem in the inspected file; do not cite such a declaration.
A short specialization proof or the existing bundled composition is sufficient.
There is no need to repackage the same preservation predicate into a second
public generic record merely to obtain a different name.

### Existing domain evidence

`Sequences.AbstractFIFO.Ops` (line 8) contains only operations. Its separate
`Simulation` (33) supplies empty, step and observation preservation.
`Simulation.stepSquare` (44) and `runSquare` (54) use existing relational
composition; `run_preserves` (71), `client_eq` (78), `client_empty` (82),
`comp` (86), and `representation_independent` (108) expose usable clients.
`Simulation.comp` retains `∃ r, rel q r ∧ next r s`, not merely equality of
final observations. This is the relevant reusable pattern, not a command
signature to force Set/Map operations into.

`Sequences.Symmetric.representation` is exactly
`Inv q ∧ fromSL q = xs`. `snocSquare`, `tailSquare` and `headSquare` show how
the state relation and an equality-only endpoint observation compose. The
existing `Examples.AbstractFIFO` proves one ordinary operation-only client
against lists and symmetric queues, then shows that two related layouts have
different private front lengths. It already demonstrates why representation
independence is observation-specific.

The alternative valid-subtype route is also concrete:
`RandomAccess.Carrier`, `representation`, `updateSquare` and `lookupSquare`
(lines 12–44 of its Representation module), and
`Resources.FIFOContracts.ValidQueue`, `validOps`, `valid_correct` (126–151).
RandomAccess additionally has canonical encoding/injectivity theorems, but
those are particular facts of that representation, not generic ADT premises.
Its stronger `pushPop_exact` cannot be inferred merely from `pushPop_refinement`
for an arbitrary future Set/Map implementation.

`Resources.FIFOContracts.Instrumentation` and `Accounting` keep behavior apart
from measured observations. `run_erases` and `cost_noninterference` illustrate
why an ADT behavior law supplies no equality or bound on two implementations'
work. The separate interval-list linear-time exercise is not solved by the
model-oriented interface.

`Incremental.Stateful.CompValid` (line 36) likewise retains the second
validity predicate at the **first state's actual observation**. Its
`Laws.comp` demonstrates the same intermediate-boundary discipline for another
native interface. There is no reason to force this finite-change signature
into a Set/Map record or replace its native theorem.

## 3. Exact invariant/schema bridge and universe boundary

For arbitrary input/output representation and model types, write ordinary
relations

`R t a := I t ∧ decode t = a`,
`R' u b := J u ∧ decode' u = b`.

A narrowly useful **proposed bridge lemma**, rather than a new framework, is
that `Relator.LiftFun R R' impl spec` is equivalent to

`∀ t, I t → J (impl t) ∧ decode' (impl t) = spec (decode t)`.

Forward: apply preservation to `⟨ht, rfl⟩`. Reverse: obtain the conjunction at
`t`, substitute the related abstract input, and transport the semantic equation
by `congrArg spec`. The statement has no existence, canonicality, or
surjectivity premise. Two concrete consumers, Set and Map, justify this small
shared equivalence if it reduces repeated proof work; the theorem can live
beside the existing relation API rather than in a second ADT calculus.

Represent ordinary arguments by equality and explicit product components;
represented state arguments use R. Represent ordinary outputs by equality,
with a trivial validity predicate. The Bool/Prop membership observation is an
explicit reflection relation or its ordinary pointwise theorem. It must not be
silently written as an equality between a Boolean and a proposition.

This recovers the source's n-argument schema without a type-equality test:
an ordinary key or value whose underlying Lean type happens to equal the state
type is still an ordinary argument. Nullary operations use a terminal input
with True, giving unconditional empty correctness and validity. A binary
state operation uses both state predicates, not just the first.

**Inspected encoding limitation:** `Squares.Rep`, `Relational.RelRep`,
`RelSquare`, `compRel`/`existentialSquare`, and `AbstractFIFO.Ops` currently use
one universe `u` for all their carriers. Do not copy that restriction into
new public `Set.Ops α Q` or `Map.Ops α β M`. Use ordinary independently
quantified laws or `Relator.LiftFun` for the domain-level formulation. When a
bundled square is actually needed, an internal explicit ULift bridge is an
existing idiom: `Sequences.Symmetric.lengthsRepresentation` and `lengthsSquare`
(lines 55–68) lift the small `List Nat` observation to the shared universe.
No caller-facing inhabitance assumption is needed for ULift. A broader
universe retrofit would be a separate, explicitly justified change preserving
all old consumers; this report neither requires nor authorizes it.

## 4. Composition through an ordered list model

Let `u : T → L`, `v : L → A`, `I : T → Prop`, and `J : L → Prop`. The exact
existential composition of valid graphs simplifies to

`(∃ l, (I t ∧ u t = l) ∧ (J l ∧ v l = a))
 ↔ I t ∧ J (u t) ∧ v (u t) = a`.

This is the essential boundary: the composite invariant contains **both**
`I t` and `J (u t)`. It may be simplified only after a proved implication
from I to that intermediate validity. Neither decoder composition nor equality
of final observations supplies J by itself.

For the source's ordered interfaces, take I to be the extra representation
condition and J to be strict sortedness of the decoded list. Both
`Set_by_Ordered` and `Map_by_Ordered` explicitly choose the conjunction.
`Sorted_Less.thy` defines its `sorted` as `sorted_wrt (<)`; for maps,
`sorted1 ps` is strict sortedness of `ps.map Prod.fst`, not an order on full
key/value pairs. Values β acquire no order or equality assumption.

For a fixed operation, the reusable proof route is:

1. On `I t ∧ J (u t)`, the tree/representation law yields the correct middle
   operation result and preserves I at the actual resulting state.
2. The list operation preserves J at `u t` and simulates its abstract model
   operation through v.
3. Use the first semantic equality to transport this J proof to `u (impl t)`.
4. Compose the two semantic equations by congruence/transitivity, or by
   `existentialSquare` with the same middle operation.
5. Simplify the endpoint relation by the equivalence above, through
   `transportRelations` when retaining a bundled square.

Empty operations use their own unconditional abstraction and invariant laws;
observations end in the appropriate equality/reflection relation. These steps
recover all seven Set or six Map clauses, including the invariant clauses,
rather than proving only the final decoded mutation equations.

### Middle-map agreement is a real premise

`existentialSquare f g middle` requires
`middle : ∀ b, f.spec b = g.impl b`. For the literal source routes the middle
arrows can be the identical named `ins_list`/`del_list` or `upd_list`/`del_list`,
so this premise is immediate. If two arrows are proved equal only on valid
middle values, use the valid middle subtype and its preservation proofs;
do not strengthen that fact to equality on all raw lists.

If the two middle implementations merely have equal lookup/set observations,
they need not be equal as valid lists either. In that situation compose through
the appropriate observation relation, or prove the domain-specific semantic
bridge directly; the existing middle equality must not be filled with an
observation equality of the wrong type. No new general framework is needed
just to hide this missing premise.

### Standard association-list reuse and its limits

Pinned `Mathlib/Data/List/AList.lean` has independent universes for keys and
values, dependent Sigma entries and a built-in `NodupKeys` invariant (49–53).
For the nondependent case use `AList (fun _ : α => β)` without ordering β.
Under `[DecidableEq α]`, existing `lookup_empty` (150), `lookup_insert` (280),
`lookup_insert_ne` (284), `lookup_erase` (233), and `lookup_erase_ne` (237)
already discharge the pointwise Map observation laws for those actual
operations. This assumption belongs to this executable realization. The
`DecidableEq (AList β)` instance additionally needs equality of values, but
nothing here requires that instance.

Do not claim that `AList.insert` is the source's ordered list update:
`entries_insert` (252–254) gives a new head followed by `kerase`, so its entry
order and recurrence differ. Similarly, an `AList` cannot represent arbitrary
raw duplicate-key lists for the source's unrestricted `map_of` definition.
Its semantic adapter is useful as a distinct connected model; it does not
replace the still-required literal ordered-list correspondence.

The pinned source gives `map_of_ins_list` with **no sortedness premise**.
`map_of_del_list` requires strict key sortedness; first-match deletion on
`[(1,10),(1,20)]` would reveal the second binding instead of making lookup 1
absent. Preserve this difference in later list-model proofs. `Finmap` or an
`AList` realizes finite support, whereas the source model is every function
`α → Option β`. No surjection onto that unrestricted model is required.

## 5. Exercise 6.2: observation-level interface translations

These are **proposed future specialization proofs** of the existing source
exercise, not implementations made here. Keep empty and lookup unchanged and
keep validity separate from the operation-only interface.

For a modify interface, the callback has full type `Option β → Option β`.
Its semantic law changes only key a to `f (lookup m a)` and its other law
preserves validity. There is no restriction `f none = none`: creating a
binding at an absent key is part of the interface.

- From modify, the constant-some and constant-none callbacks supply update
  and delete. Their semantic and invariant laws are direct specializations
  of the two modify laws; combine with the retained empty laws to obtain all
  six original Map obligations.
- Conversely, the source case analysis on the one observed value
  `f (lookup m a)` selects original deletion for none and original update for
  some b. Each branch uses the corresponding semantic and validity laws.
  The existing `eq_update_iff` characterization proves the updated-key and
  every unaffected-key equation without assuming equality or an inhabitant
  for β. This is an interface adapter, not a new tree/list operation.

Round-trip strength is asymmetric. Starting with original update/delete,
forming this case-based modify, and then specializing it to constant callbacks
recovers the original operations pointwise even on raw states, by reduction of
the explicit case expression. No representation equality is inferred from
semantic laws in that direction.

Starting with an arbitrary lawful modify operation, reconstructing it through
constant-callback update/delete generally gives only equal lookup observations
and validity on valid inputs. A concrete implementation may retain hidden
history depending on the supplied callback away from the current value. For
example, with finite Bool values a counter may distinguish `f none = none`
from other callbacks while ignoring that counter in lookup; identity at a
present key and its reconstructed constant-some callback then leave equal
maps but different counters. This is a proposed negative case, not a compiled
witness. It prevents an unjustified representation isomorphism or unconditional
identity theorem.

No runtime count, one-traversal bound, or cost equality follows from these
translations. A value-level case expression retaining one callback result is
not a compiler evaluation or memoization theorem.

## 6. Meaningful connected cases and remaining work

Existing examples already establish the applicable distinctions; future Set/Map
cases should reuse them where they suffice and exercise the new domain surface
where they do not.

| Connection or boundary | Existing evidence / proposed narrow case |
| --- | --- |
| Same interface, different representations | Existing FIFO ordinary client uses both lists and symmetric queues; the Set/Map analogue must use the actual future Ops/Laws, not assert parametricity of arbitrary Lean functions. An `AList` law witness is a small existing-operation client before later ordered tree/interval realizations. |
| Actual intermediate validity | A generic client that mutates and then observes, or mutates twice and observes, must apply the second law to the first operation's proved-valid result. A list-model composition should expose the combined invariant explicitly. |
| Lookup versus representation equality | Existing FIFO `hidden_front_length` and two related layouts distinguish private state. A Map history-counter extension provides a corresponding future boundary for absent deletion or modify round trips. |
| Independently typed payloads | A generic map client should quantify over key, value and state universes independently. Include Empty values/keys where operations permit them; no global default can appear. |
| Duplicate-key invalid middle | The two bindings at key 1 distinguish first-match deletion from abstract removal. This tests the intermediate uniqueness premise rather than only a sorted example. |
| Non-surjective abstraction | A finite association-list implementation satisfies Map laws without representing every infinite-support function. Do not add totality of the reverse relation to obtain a client theorem. |
| Source role distinction | An ordinary key/value parameter whose carrier coincides with the state type must still use identity/equality semantics, not the state decoder. Explicit products already express this. |
| Conditional versus raw claims | Test or state a law on the valid relation/subtype; no useful proof should require asserting the concrete simulation equation on malformed raw states. |

The existing `FirstOrderRelations.compile_preserves` and
`STLCRelations.compile_preserves` are available for their supported syntax and
supplied primitive relations. `AbstractFIFOSyntax` demonstrates an optional
compiler surface whose endpoint observation remains outside its single-base
state fragment. These are not a ready-made many-sorted Set/Map language or a
parametricity theorem for arbitrary polymorphic Lean clients. For the first
ADT client, a direct ordinary composition and its relational proof is smaller;
do not add a syntax/executor merely to re-prove that composition.

Remaining genuine work, if a later bounded unit is chosen:

1. Define only the needed thin operation/law records and prove their exact
   source correspondence, including Bool reflection and the pointwise/function
   update equivalence. No such new declaration exists from this report.
2. Supply the small valid-graph specialization bridge, if both domain clients
   make it useful, using existing preservation relations and composition.
3. Prove the ordered-list-to-model and representation-to-list instances with
   their actual invariants. Existing generic composition removes no algorithm
   correctness obligation; the literal ordered recurrences remain later work.
4. Derive both modify translations and a genuinely interface-only connected
   observation theorem. Retain only the representation equalities that follow
   from explicit definitions, and the weaker observations in the other direction.
5. When implementing, resolve the concrete Lean elaboration/import details of
   local classical update notation and any private universe lift. This source
   preflight ran no compiler and certifies none of those proof scripts.

Concrete insert/delete/lookup algorithms, interval merging/difference, BST
balance, resource bounds, new preservation infrastructure and retrofits of
unrelated clients are outside this preparation. All original source
obligations remain queued in their existing records. Only this report was
written; no source, requirement, ticket, reference, cache, gate or remote
artifact was changed.
