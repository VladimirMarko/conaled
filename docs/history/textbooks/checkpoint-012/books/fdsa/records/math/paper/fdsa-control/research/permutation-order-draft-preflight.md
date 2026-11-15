# Permutation-order draft: bounded implementation-side source assessment

Prepared 2026-11-02 for FDSA-XU02. **One prose clarification was identified and
corrected by root; no remaining mathematical, scope or agreed-API mismatch was
found in the assigned root-written portions.** This is an implementation-side
source assessment, not independent Standards/Spec review, final approval,
compilation, proof audit or acceptance. No elaborated types were inspected.

## 1. Scope and inspected identities

The assigned files were read from `conaled-permutation-order`:

| File | Inspected scope | SHA-256 |
|---|---|---|
| `Examples/PermutationOrder.lean` | Entire stable file, 6,445 bytes | `251c0ee0ce7b96711ea57e1ff7496a784fe33137596e8f13b244fa9e44fd57e5` |
| `docs/research/fdsa-permutation-order.md` | Entire initial file and the subsequently corrected paragraph; updated identity, 8,851 bytes | `39fd16835dccd39c9d34ebfcebbdbdd33f44ec1dad49fdfe582a8ac4801faea3` |
| `docs/research/fdsa-reconstruction-map.md` | Only “Shared whole-subset ordering (draft)” | Whole-file identity: `aa5ae498a2b23a5dee8dcbc0eac1eb5d8735cec4d97ebcdca7877d48ff9f52ce` |

The reviewed reconstruction subsection is 976 bytes, SHA-256
`60e8503a1d83a49745be7efe291647f301096730023e2b409a17071c71c090ea`.
Its containing file's hash does not extend this assessment to earlier sections.
The initial research-note hash was
`662244e2633104f6a579fcf762aae399a119b1e476bc9b6fab1310d44fdbd51d`;
the correction and its disposition are preserved below.

The frozen requirements identity matched
`reviews/permutation-order-requirements.md`, SHA-256
`f473f593bf4a7ef75dcf2f3163440db6fe187b3b9983f87254d2ddfa8191982d`.
The saved independent calculations identity matched
`research/permutation-order-calculations.json`, SHA-256
`54163e6729373a9c78cd82432d48ae827498321c64e53e3c5160cebb54ca2f80`.
Those calculations were already read for this unit's source preflight and
were not rerun here. Repository guidance and the start record were read in
the existing implementation loop.

**Exclusions:** I authored `Examples/PermutationOrderBoundary.lean`; its code
was not reread or treated as independent evidence in this pass. Its import
and root-written prose descriptions were checked against the frozen intended
mathematics. The concurrently finalized core proof was also excluded. This
is not an assessment of the entire import closure or the final core source.

## 2. Agreed public API and deterministic connections

The core contributor directly confirmed all helper argument orders used by
the main file: `restrictedOrder_nodup`, `restrictedOrder_toFinset`,
`restrictedOrder_length`, `restrictedOrder_perm`,
`map_restrictedOrder_sublist`, `orders_card`, and
`filter_restrictedOrder_of_subset`, along with the unchanged fiber and map
interfaces. This is source-level coordination, not elaboration evidence.

The main file fixes positions `[0,1,2,3]`, selected set `{0,2,3}` and smaller
set `{0,3}`. Its Nodup and completeness proofs concern those actual positions.
`selected_structure` invokes the public contracts to obtain Nodup, exact
finset support, length three and the mapped-sublist relation for every π.
`selected_permutation` uses the actual filtered base `[0,2,3]` and the public
permutation theorem. `selected_orders_card` derives six through `orders_card`,
not from an unrelated count of a different carrier.

The only new measurable spaces in this main file are local top instances on
`Equiv.Perm (Fin 4)` and `List (Fin 4)`. Existing discrete-space instances
supply measurable singletons. There is no new global instance or probability
carrier. `law` is exactly the existing uniform measure on all permutations.

## 3. Whole-list probabilities and mapped meaning

| Observation | Actual public connection | Independently expected value |
|---|---|---|
| `[0,2,3]` | `order_023_mass` calls the private supported-case helper, whose body directly invokes `uniformOn_restrictedOrder_eq` and selects its positive branch. | 1/6 |
| `[0,3,2]` | `order_032_mass_via_map` rewrites a singleton event with `Measure.map_apply`, then uses `observed_law`, `uniformOn_apply_finset` and the proved target cardinality. `observed_law` directly invokes `map_restrictedOrder_uniformOn`. | 1/6 |
| Repeated `[0,0,2]` | `repeated_order_mass_zero` establishes nonmembership in the actual `orders` finset and selects the generic fiber theorem's zero branch. | 0 |
| Singleton `[2]` | The same supported-case helper specializes the new fiber theorem to cardinality one. | 1 |
| Full order `[3,1,0,2]` | The supported-case helper uses the full Fin4 support and factorial normalization. | 1/24 |

The two selected triple lists share their first key but differ in their
remaining order. They therefore exercise information beyond a minimum-member
marginal. The retained calculation gives each of the six triples four of the
24 samples, matching the two displayed masses. The invalid list has the
correct length but the wrong multiplicities and support.

The mapped-measure example is substantive: it proves equality for the actual
list-valued observation, then obtains a source-event probability through that
equality and the ordinary finite target measure. Its `map_apply` invocation
supplies a measurable map from the finite permutation space and a measurable
output singleton. It does not merely restate a scalar fiber result or define
a new independent output draw.

## 4. Same-permutation nested restriction

`nestedObservation π` explicitly filters `restrictedOrder positions selected π`
to the smaller set. `nestedObservation_eq` applies
`filter_restrictedOrder_of_subset` with the concrete inclusion proof. The same
π occurs throughout this pointwise equality.

`nested_order_30_mass` rewrites the source event through that equality and
invokes the new fiber result on smaller, giving probability 1/2 for `[3,0]`.
As an independent small account, three of the six equally likely selected
triple orders put 3 before 0, or twelve of the 24 global samples. The proof
uses a value-composition bridge under the existing law; no conditioning,
independence assumption or resampling occurs.

## 5. Prose finding and disposition

**XU02-SP01 — mathematical wording in the numeric-enumeration boundary.**
The initial note called the ordinary label enumeration a “non-increasing
numeric order”. Its values `[-7,100,4]` are not non-increasing in the usual
mathematical sense: the first step increases. The intended statement is
that this sequence is not strictly increasing.

Root changed the paragraph to say that it has “a different numeric order
that is not strictly increasing”. The corrected paragraph was reread and
its updated file identity is recorded above. The wording now matches the
frozen boundary claim; no code or mathematical statement changed. This is a
verified source-text correction within this pass, not closure of an independent
final-review finding or a validation gate.

## 6. Assumptions, source limits and remaining checks

The corrected research note distinguishes the operation's sole equality
decision from its value-law premises. Completeness, Nodup, subset inclusion
and sample measurability are attached to the appropriate contracts. It
correctly separates the fiber theorem's source-space hypotheses from the map
corollary's output-space hypotheses. It describes finite output support and
countable List I without claiming the entire list space is finite.

The inverse orientation, label-versus-numeric order, empty target `{[]}` and
invalid-enumeration descriptions match the frozen mathematics. This checks
root's prose, not my excluded boundary implementation. The right-composition
proof explanation matches the coordinated sample transformation
`π ↦ π * σ.symm`; preservation of S justifies filter/map transport.

The main header, research note and new map subsection consistently leave
adaptive or conditional histories, joint independence, expected positions,
algorithm execution, treap semantics and observed costs outside the present
claims. They retain occurrence/duplicate and source-tariff obligations and
explicitly state that this draft is uncompiled and unaccepted.

No additional source correction is requested by this bounded pass. Later
checks must still elaborate the final core signatures, local instances,
ENNReal arithmetic, factorial/support reductions, `map_apply` rewrites and
finite computations; inspect elaborated public types; and validate the whole
candidate and import closure with the required independent review. This
report supplies none of those results.

Only this requested report was written. No reviewed source, boundary file,
core, requirement, tracker, Git state, compiler output, cache or gate was
changed by this assessment. Identity calculations were ordinary read-only
SHA-256, not a project hash helper or verification command.
