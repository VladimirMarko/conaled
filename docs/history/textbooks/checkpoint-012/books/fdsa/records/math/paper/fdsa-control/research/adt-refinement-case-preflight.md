# Set/Map contract and refinement: bounded case preflight

Prepared 2026-11-02. **Source-only case preparation; no implementation or scope
freeze.** This note makes a small connected family of expected propositions
concrete. Operation/law names below identify mathematical roles or the source
locale fields; they do not assert that proposed Set/Map Lean declarations exist.
The source and API reports remain authoritative for source coverage and API
placement. No new ADT syntax, executor, relation record or state framework is
needed for these cases.

## 1. Read evidence and fixed inputs

Read both stopped reports completely, the complete
[root readback](../reviews/adt-refinement-preflight-readback.md), AGENTS,
example-driven-development and its worked example, applicable implementation,
research, architectural/domain guidance, glossary and ADRs 0001/0002/0010.
The example-driven distinction used here is: calculate the expected observation
independently, then identify the public contract that must supply it and the
validity facts needed to invoke that contract.

| Stopped input | Bytes / lines | Ordinary SHA-256, checked from bytes |
|---|---:|---|
| [Source report](adt-refinement-source-preflight.md) | 22,132 / 342 | `5db706e4afc85913cfd92c8aeace3de2e8aea174fe813b828aa9a30a3d1d8994` |
| [API report](adt-refinement-api-preflight.md) | 28,486 / 445 | `4d63f2616dee5af5e358cc59696745f215698973517dad9d4d77c1310b09e391` |

Primary/local sources inspected for this case note:

- [Set_Specs.thy](../../book-source/Set_Specs.thy) and
  [Map_Specs.thy](../../book-source/Map_Specs.thy), both complete; the complete
  Exercise 6.2 tail in [chapter06.txt](../../book-source/chapter06.txt).
  Their retained PDF/companion identities and source inventories are in the
  stopped reports; this note does not repeat or change them.
- [Relations](../../conaled/SquareKit/Relations.lean) and
  [RelationComposition](../../conaled/SquareKit/RelationComposition.lean),
  including actual `RelSquare.preserves`, `compose`, `product`, `terminal`,
  `compRel`, `existentialSquare` and `transportRelations` definitions.
- [AbstractFIFO](../../conaled/Applications/Sequences/AbstractFIFO.lean) and
  its [ordinary examples](../../conaled/Examples/AbstractFIFO.lean), both
  complete. `Simulation.run_preserves`, `client_eq`, `comp` and
  `representation_independent` are existing FIFO theorems, not Map theorems.
- The actual raw invariant relation and ULift case in
  [Symmetric/Observation](../../conaled/Applications/Sequences/Symmetric/Observation.lean),
  valid-subtype/update-query interfaces in
  [RandomAccess/Representation](../../conaled/Applications/Sequences/RandomAccess/Representation.lean),
  `ValidQueue`/`validOps`/`valid_correct` in
  [FIFOContracts](../../conaled/Applications/Resources/FIFOContracts.lean),
  and `CompValid`/`Laws.comp` in
  [Incremental/Stateful](../../conaled/Applications/Incremental/Stateful.lean).
- Pinned Mathlib's `Relator.LiftFun`, `Function.update` and its exact
  `eq_update_iff`, `update_self`, `update_of_ne`, `update_eq_self` statements;
  `AList`'s type, lookup, insertion, erasure, entry and key laws. The package
  pin is the one recorded in the API report. These were source reads only.

## 2. Smallest useful positive family

Use **K = Fin 2** for the concrete cases and write its distinct keys as 0,1.
The pair displays below list observations at those keys; they do not introduce
a new finite-map carrier. The abstract Set model is `Set K`; the Map model is
the existing function type `K → Option Bool`.

For a direct executable Set observation use a function `s : K → Bool` and
decode it as `{k | s k = true}`. Empty is constantly false; insert sets the
selected entry to true and delete sets it to false. Membership is evaluation.
For Map use `m : K → Option Bool`, constantly-none empty and the usual point
updates to `some v` or `none`. Both have validity True. `Fin 2` supplies the
key decision locally; this choice imposes no global decision on the contracts.

For the nontrivial-invariant realizations pair either observation with a
natural counter: `(s,c)` or `(m,c)`. Empty has counter 0. Every insert/update
or delete performs the indicated point update and replaces c by c+2.
Decode/lookup forgets c and validity is **Even c**. The counter is retained
history, not execution cost. Even 0 and preservation by +2 prove the invariant
clauses. `(s,1)` is invalid even when s is a perfectly good observation; valid
states include arbitrary observations at every even counter, not just states
reachable from empty.

### Contract-to-case connection: all seven Set laws

The source has four semantic laws and three invariant laws. Each proposed
realization must supply these fields before a client theorem specializes it.

| Source field | Obligation for the paired Set realization | Exact client use |
|---|---|---|
| `set_empty` | Decode `(false-everywhere,0)` is ∅. | Fix the initial set, independently of initialization validity. |
| `set_isin` | For Even c, evaluation is true iff the queried key belongs to the decoded set. | Derive each final Boolean query from the final set equation and final validity. |
| `set_insert` | Decode after setting entry a true is `decode q ∪ {a}`. | Apply at the actual first and second states. |
| `set_delete` | Decode after setting entry a false is `decode q \ {a}`. | Apply at the actual second state, not only at empty. |
| `invar_empty` | Even 0. | Supply the first legal input. |
| `invar_insert` | Even c implies Even (c+2). | Obtain the input validity for the next insertion and deletion. |
| `invar_delete` | Even c implies Even (c+2). | Obtain final validity for membership reflection. |

The direct Boolean realization supplies these by observation calculation;
the paired one uses the same point-update facts plus evenness. For the local
point-update facts use `Function.update_self` and `update_of_ne`; Set equality
is extensional. The Set law certificate, rather than a second direct
calculation of the client's final table, must prove the generic client result.

### Contract-to-case connection: all six Map laws

Lookup is already the decoder. The update/delete semantic fields each retain
the changed-key result **and every unaffected-key result** as one grouped law.

| Source field | Paired Map obligation | Required connection |
|---|---|---|
| `map_empty` | Lookup of `(none-everywhere,0)` is constantly none. | Supplies the initial full function. |
| `map_update` | At a, result is `some v`; at x ≠ a, result is the old lookup x. | Use both clauses in the two-key client. |
| `map_delete` | At a, result is none; at x ≠ a, result is the old lookup x. | Distinguishes removal from overwriting to a stored false. |
| `invar_empty` | Even 0. | Initializes the validity chain. |
| `invar_update` | Even c implies Even (c+2). | Carries validity through both updates. |
| `invar_delete` | Even c implies Even (c+2). | Establishes valid final output. |

`Function.eq_update_iff` connects the grouped pointwise semantic field with
the source's whole-function equality when a key decision is supplied. No
seventh lookup law, global value equality, value default or lookup injectivity
is added. A later generic client proof must use the future public law fields;
the existing FIFO client is a design precedent, not an applicable Map law.

## 3. Sequential clients: calculations and actual validity propagation

The client is ordinary composition with named intermediate states, not a
command datatype or trace interpreter. It executes neither the decoder nor an
invariant checker; its proof receives the separate law evidence. For Set,
starting from empty, perform
`insert 0`, `insert 1`, then `delete 0`. For Map perform `update 0 false`,
`update 1 true`, then `delete 0`. Observe only after these operations.

| State | Set membership at (0,1) | Map lookup at (0,1) | Paired counter | Validity witness |
|---|---|---|---:|---|
| q0 = empty | `(false,false)` | `(none,none)` | 0 | Empty validity. |
| q1 = first insertion/update | `(true,false)` | `(some false,none)` | 2 | Preservation applied to q0 and its witness. |
| q2 = second insertion/update | `(true,true)` | `(some false,some true)` | 4 | Preservation applied to q1 and the preceding result. |
| q3 = delete 0 q2 | `(false,true)` | `(none,some true)` | 6 | Preservation applied to q2; this witness is used by final Set reflection. |

This is a nonempty two-key calculation: q2 contains both keys and q3 still
contains key 1. The `some false` entry is observable before its deletion.
For Map lookup at 1, final deletion uses its unaffected-key clause, after the
second update's changed-key clause. For Set the final decode is `{1}` and
reflection proves exactly `(false,true)`; a proof of only the counters or
the final table by reduction would not exercise the new contracts.

The generic client should quantify independently over keys, values and state.
For arbitrary valid initial q, keys a,b and Map values u,v, retain validity of
q1 = update a u q, q2 = update b v q1, q3 = delete a q2. The exact observations
are `lookup q3 a=none`; if b ≠ a then `lookup q3 b=some v`; and, for
x ≠ a and x ≠ b, `lookup q3 x=lookup q x`. If a=b, both displayed queries
are none. These pointwise
statements need no global DecidableEq. With a local decision the full function
is `x ↦ if x=a then none else if x=b then some v else lookup q x`.
The Fin 2 trace has no key untouched by all three mutations. The single
Nat-key AList case in section 7 exercises this last clause nonvacuously.

The Set analogue has final decode `((decode q ∪ {a}) ∪ {b}) \ {a}`;
query a is false, query b is true when b ≠ a, and membership elsewhere is
unchanged. When a=b and q=empty the final set is empty. The distinct-key
assumption is necessary for these particular positive queries at b: when it
fails, deletion returns false/none there. It is not needed for validity or the
unconditional final model formula.

Retain just these additional discriminating values:

- Equal-key Map sequence `update 0 false; update 0 true; delete 0`: intermediate
  lookups at 0 are `some false`, `some true`, none; final pair `(none,none)`
  and counter 6. Equal-key Set sequence also ends empty at counter 6.
- Delete absent key 0 from q3: the observation remains `(false,true)` or
  `(none,some true)`, but the paired state has counter 8 rather than 6.
  Thus semantic idempotence does not establish concrete-state equality.
- Two valid paired states with identical observations and counters 0 and 2
  are unequal but related to the same model. The specified interface-only
  client yields equal observations. This is a concrete specialization of its
  proof, not a parametricity claim about arbitrary Lean functions.

## 4. Two-stage composition: one shared middle operation

Root's subsequent architecture assessment selects the small future module
`SquareKit.ValidGraphs`, with `validGraph I decode c a := I c ∧ decode c = a`,
`liftFun_iff` for output validity and decoder commutation, and `comp_iff` with
right-hand side `(I c ∧ J (decode c)) ∧ decode' (decode c) = b`. These are
accepted design shapes supplied by root, not declarations inspected in the
current source. The cases below target those thin lemmas and existing
relational operations without adding a second preservation record.

Use either paired realization Q above and add a tag: T = Q × Bool, with
state `((observation,c),tag)`. The first decoder d forgets the tag; the second
decoder e forgets the counter (and performs Set reflection when applicable).
Let I t mean `tag=true` and J q mean `Even q.counter`.

For each particular insertion/update/deletion let UQ be **the same actual
paired operation** in both stages. Define the top operation UT by
`UT (q,tag) = (UQ q,tag)`. The first square uses UT and UQ, with relation
`I t ∧ d t = q`. The second uses UQ and the corresponding model operation UA,
with relation `J q ∧ e q = a`. Its preservation proof uses the paired law
certificate, including the output Even witness. For fixed ordinary arguments,
the `middle` argument to `Relational.existentialSquare` is pointwise reflexivity
`∀ q, UQ q = UQ q`, on **all raw middle states**, including odd ones.

For variable keys/values the ordinary-argument relations are equality and are
combined with the state relation through `Relational.product`; their roles do
not change if a key/value type happens to equal the state type. The nullary
empty case uses `Relational.terminal` and the unconditional two empty laws.
All concrete carriers here lie in Type 0, so the existing bundled
square interface needs no universe adaptation for this case.

The actual composite relation simplifies to

`∃ q, (I t ∧ d t = q) ∧ (J q ∧ e q = a)`

iff `(tag=true ∧ Even c) ∧ e (d t)=a`. This is an exact equivalence; use
`transportRelations` if keeping the composed square. Its witness before an
operation is d t, and after it is UQ (d t), not a newly chosen unrelated model.
Compose the three mutation squares with `Relational.compose`, then the
endpoint observation. The actual states of the main client have true tags,
counters 0,2,4,6 and exactly the two observation columns above. Preserve both
validity components at every step. `validGraph`/`liftFun_iff` can expose the
same proof without coupling generic domain universes; `comp_iff` supplies the
displayed relation equivalence for `transportRelations`.
The inspected `Relational.compRel` and Mathlib `Relation.Comp` have the same
existential body, so this connection needs no new composition relation.
For the Set endpoint use the explicit Bool-to-Prop reflection relation
`b=true ↔ p`, or the source's pointwise reflection field. Map endpoint lookup
uses equality on Option values. No global executable membership decision for
arbitrary abstract sets is supplied by the concrete Fin 2 cases.

### Two separate omitted-premise counterexamples

The true-tag/odd-counter state `((observation,1),true)` satisfies I and fails
J(d t); the false-tag/even-counter state fails I while satisfying J(d t).
Their conjunction is therefore not redundant. In the simple +2 realization,
even some invalid inputs happen to have correct decoded operations; do not
mislabel this nonimplication alone as an observation failure.

Use two tiny Bool calculations to isolate the genuine failures:

| Omitted requirement | Individually lawful stages | Invalid proposed conclusion at false |
|---|---|---|
| Middle input validity | Decoders identity; I=True; J a means a=true. First implementation and middle operation are constant true. Second implementation is that same constant-true operation; final specification is identity. First stage preserves equality for all inputs; second preserves its valid graph at true. Actual middle operations agree everywhere. | Dropping J would require `true=false`. The proper composite has no related input witness at false. |
| Actual middle-operation agreement | Both relations are equality, all inputs valid. First square has implementation/specification Bool.not; second has implementation/specification identity. Each preserves equality. | Pasting first implementation with second specification would require `Bool.not false=false`, i.e. `true=false`. Here the missing middle equation is itself false. |

The existing helper's all-state middle equality is sufficient and explicitly
required by its signature. Valid-state agreement can suffice for a different
direct proof or a valid-subtype specialization; it must not be passed as the
helper's stronger premise. Equal decoded middle observations also do not prove
equality of middle states: operations adding 2 versus 4 to a hidden even
counter can agree after e and disagree as functions Q→Q. No generic equality
of those functions follows from two independent law certificates.

### Two minimal product cases for roles and represented inputs

Use the Type 0 state relation `R n a := Even n ∧ n/2=a`, bundled as
`stateRep := ⟨Nat,Nat,R⟩`; bundle ordinary-parameter equality as
`parameterRep := ⟨Nat,Nat,Eq⟩`. These are local descriptions of existing
`Relational.RelRep` values. This arithmetic specialization checks the shared
bridge's argument roles; it adds no Set2
operation to the seven-law Set signature.

- **Ordinary argument:** take `(k,n) ↦ n+2*k` and specification
  `(k,a) ↦ a+k`. Use `Relational.product parameterRep stateRep`, followed
  by the output stateRep. Even n supplies Even (n+2*k); the decoder equation is
  `(n+2*k)/2 = n/2+k`. At k=3,n=4, the raw result is 10 and its observation
  is 5=2+3. Treating k as a represented state would wrongly demand Even 3;
  merely decoding it as 3/2 would give the wrong abstract result 2+1=3.
  The ordinary parameter and state happen to have the same Lean type but
  have different explicit relation roles.
- **Two represented inputs:** take raw addition `(n,m) ↦ n+m` and model
  addition `(a,b) ↦ a+b`, with input representation
  `Relational.product stateRep stateRep` and output stateRep. The bridge
  must consume Even n and Even m to establish
  Even (n+m) and `(n+m)/2=n/2+m/2`. At n=4,m=6, the raw result is 10,
  decoded result 5, and model result 2+3=5. If only the first validity is
  retained, n=4,m=1 produces invalid output 5. By symmetry the other
  input validity cannot be omitted from this uniform preservation contract.

Use `liftFun_iff` for the validity/decoder obligations and the existing product
relation for the actual two input certificates. These positive and negative
values distinguish roles without a general n-argument syntax or a new binary
collection-operation interface.

## 5. Modify translations and the asymmetric round trips

Retain empty and lookup unchanged. From a modify operation derive
`update a v m = modify a (fun _ => some v) m` and
`delete a m = modify a (fun _ => none) m`. Their semantic and validity fields
must be applications of the two modify laws. Conversely, from the original
interface, evaluate `f (lookup m a)` and select delete a m for none or
update a v m for some v. Both branches must use the actual input validity and
the corresponding original mutation fields. The resulting modified semantic
law still includes every unaffected key. Exercise 6.2 supplies no restriction
`f none = none`, and no callback-count or runtime claim is inferred.

For an ordinary positive specialization use the derived modify on the even
counter realization. Start with `(lookup 0, lookup 1)=(none,some true)` and
counter 0, a valid nonempty state. Four successive calls at key 0 give:

| Callback | Result at key 0 | Result at key 1 | Counter | Original branch |
|---|---|---|---:|---|
| Constant `some false` | `some false` | `some true` | 2 | Update: creates an absent binding. |
| Identity | `some false` | `some true` | 4 | Update: preserves the observation, changes history. |
| `Option.map Bool.not` | `some true` | `some true` | 6 | Update: overwrites a present binding. |
| Constant none | none | `some true` | 8 | Delete: removes the binding. |

Connect these expectations through the **derived modify law** and its preserved
validity, not only by unfolding the case expression four times. The first row
explicitly violates the suggested extra callback restriction and is lawful.

Starting with original update/delete, constructing this modify and deriving
constant-callback update/delete back gives the original operations pointwise
by reduction of the case expression, even on invalid raw states. For example,
start the even-counter implementation at counter 1: both original and
twice-translated update produce counter 3 and the same updated table. No law
certificate is applied to the invalid input; this equality is definitional.

The opposite round trip generally supplies only equal lookup functions and
valid outputs **on valid inputs**. Preserve the following counterexample as a
separate realization, with **validity True, not Even**. For K=Fin 2, V=Bool,
raw state (m,c), define

`modify a f (m,c) = (m[a := f (m a)], c + delta(f))`,

where `delta(f)=1` when `f none=none`, and 2 otherwise. The local equality
decision on Option Bool makes this concrete definition available; no equality
assumption on generic values is inferred. Lookup forgets the counter, empty
has counter 0, and both modified laws hold for every state.

Start with m(0)=some false, m(1)=some true, c=0, and use a=0, f=identity.
Original modify returns (m,1), since identity none=none. Its reconstructed
version observes `some false` and selects the derived update, invoking original
modify with constant `some false`; that callback sends none to `some false`,
so the result is (m,2). Both are valid, all lookups agree with m, and the states
are unequal because 1≠2. The even invariant would make the first result
invalid and would destroy this witness's claimed lawfulness; keep the two
counter examples separate.
The modified law certificate uses `Function.update_self` and `update_of_ne`;
the unchanged full observation in this identity case is the existing
`Function.update_eq_self` equation. The inequality concerns the counter
projection of the actual two resulting states.

Additional representation assumptions could strengthen this round trip, for
example injectivity of lookup on valid outputs, or a law that modify's result
depends only on `f (lookup m a)`. Neither follows from the Map/modify laws,
and neither is part of the proposed minimal cases.

## 6. Partial Boolean maps and empty domains

Absence and a stored false are distinct observations: on K=Fin 2, let n be
constantly none and p have p(0)=some false, p(1)=none. Then n(0)≠p(0).
Deleting 0 from p changes that lookup to none. If a Set is extracted by the
test `m k = some true`, n and p both decode to ∅; that Set observation cannot
justify equality of the maps. Encoding this extracted ∅ with none for absence
returns n, not p. The opposite map round trip is exact when the map never
stores `some false`; the Set round trip is exact with the supplied membership
decision. Domain-of-definition decoding would instead map p to `{0}` and is
a different observation. The main client retains the same distinction at q1
and q2 before deletion.

| Boundary | Exact expectation | Consequence for proposed statements |
|---|---|---|
| Key type Empty | Every Set decoder value is ∅; every lookup is the unique function `Empty → Option V`. No insertion/deletion/update/modify key can be supplied. | Empty validity/correctness remain meaningful; this cannot replace the nonempty client. No default key is needed. |
| Value type Empty, keys Fin 2 | Every lookup value is none, since `some v` would require v:Empty. Update has no value argument that can be supplied. Delete 0 on the even-counter map changes counter 0 to 2 while all queries remain none. | Lookup observation equality still does not imply state equality. No default value is needed; deletion remains an actual operation. |
| Modify with Empty values | Every `Option Empty → Option Empty` callback sends none to none; a modify operation can still change hidden state. | This special fact must not be imposed on callbacks at arbitrary V. |
| State type Empty | No operation package with an `empty` field exists. | An actual interface supplies an inhabited state carrier; it does not supply Inhabited keys or values. |

These are Lean generality cases, not claims that Isabelle/HOL has empty types.

## 7. A real AList realization is worthwhile, narrowly

**Recommendation:** include one thin Map law witness over existing
`AList (fun _ : K => V)` and specialize the same generic two-key client to it.
It supplies a real existing finite representation and operation library in
addition to the function/counter witnesses. Do not implement a second list
algorithm or an AList-specific client proof. No additional Set/AList adapter
is needed to obtain the coverage above.

The exact operation adapter is empty `∅`, update `AList.insert`, delete
`AList.erase`, and lookup `fun s k => AList.lookup k s` (state/key order is
reversed relative to the actual AList function). Set external validity to True:
unique keys are already carried by `AList.nodupKeys`. Its six Map laws use
`lookup_empty`, `lookup_insert`, `lookup_insert_ne`, `lookup_erase`,
`lookup_erase_ne`; invariant clauses are trivial because these operations
already return AList values. They require `[DecidableEq K]`, but no ordering
or equality of V. Do not request the separate DecidableEq AList instance.

For K=Fin 2, V=Bool, the main client has actual entry displays

`[] → [(0,false)] → [(1,true),(0,false)] → [(1,true)]`.

Here `(k,v)` abbreviates the actual dependent entry `Sigma.mk k v`, not a new
product-list representation. `entries_insert` says insertion prepends the new
binding after erasing any previous one, and `erase` uses `List.kerase`.
The observation at the end is `(none,some true)` through the shared client
theorem and AList law witness. Equal-key updates yield
`[] → [(0,false)] → [(0,true)] → []`.

To exercise a key untouched by the entire client, specialize the same AList
adapter once at **K=Nat**, V=Bool, with initial entries `[(2,true)]`. The exact
states are

`[(2,true)] → [(0,false),(2,true)] → [(1,true),(0,false),(2,true)] → [(1,true),(2,true)]`.

Final lookups at (0,1,2) are `(none,some true,some true)`. Lookup at 2 is
`some true` after every step because 2≠0 and 2≠1; all three semantic steps
use the unaffected-key clause. Apply the generic theorem for a valid initial
state with the AList law witness, rather than separately proving this result
only from concrete entries. This one case avoids vacuity of the full client's
unaffected-key conclusion without adding another representation or syntax.

An additional existing-operation observation boundary costs little: insertion
in the reverse order gives entries `[(0,false),(1,true)]`, with the same lookup
function as `[(1,true),(0,false)]` but a different AList state. This complements
the history counter without requiring representation extensionality by lookup.
Deleting absent key 0 from `[(1,true)]` happens to leave this AList unchanged;
the paired counter example already refutes exporting that stronger fact as a
generic Map law.

The decreasing key order after the two main insertions is also the explicit
boundary against conflating this realization with the source's ordered-list
update. AList has intrinsic distinct keys but no ascending-order invariant.
It cannot host the raw duplicate-key input `[(1,10),(1,20)]`; first-match
deletion on that source list reveals `some 20` instead of none. That later
source case and strict-key-sortedness hypothesis remain required. AList's
finite support also does not make the unrestricted partial-function model
finite or require every model function to have an AList preimage.
One sufficient concrete non-surjectivity boundary is the function on Nat keys
constantly returning `some false`: all natural keys are present, whereas an
AList has a finite key list. No separate infinite-map representation or
general surjectivity theory is needed for this observation.

## 8. Hypothesis/readback conclusions and retained scope

The smallest coherent family is: one generic sequential Set client and one
Map client; their direct and even-counter specializations; the shared tagged
composition and two product-role checks; the two small composition counterexamples; both modify
translations and the distinct lawful counter1/2 witness; one AList Map
adapter with the bounded clients; and the Option/Empty boundaries. Helpers can share these
connections rather than manufacturing a separate example for every clause.

The seven/six laws are sufficient for these specified clients; the cases do
not claim each field is logically independent or necessary for every single
observation. Validity is required to invoke the conditional laws, though a
particular realization may also work on invalid inputs. The preserved witness
at each actual intermediate state is essential to the generic sequential proof.
Middle validity is exactly part of valid-graph composition; a redundancy proof
would be needed to remove it. Actual all-state middle agreement is a stronger
requirement of the existing bundled helper than valid-state agreement alone.

Keep key, value and state universes independent in generic laws/clients.
`Relator.LiftFun` has the needed independent universes; the legacy square
records use one common universe. Concrete Type 0 cases avoid that encoding
issue, and an internal ULift/subtype bridge can be assessed if later required.
No finite-support, order, global decidable equality, invariant decision,
injective/surjective decoder or global inhabitance premise is justified by
these cases. Local Fin 2 decisions, AList's key decision and the Bool-only
callback test have their separate stated roles.

No concrete inconsistency was found between the stopped reports, root readback
and the inspected actual interfaces. The two important separation points are
now explicit: a true-tag/odd-counter state demonstrates missing middle validity
without itself proving an observation failure; the lawful counter1/2 modify
example must use validity True rather than the earlier Even predicate.

These remain proposed propositions and proof routes, not checked Lean claims.
Exact future record constructors, tactic scripts, imports and any universe
bridge require the later authorized implementation and matching validation.
No new Lean source, frozen requirement, worktree/reference, cache, ticket,
review gate, remote artifact or chapter status was changed. Only this note was
written. No compiler, Lean/Lake, checker or project hash helper ran; root's
session 83124 remains the sole full Chapter 1 compiler/checker at `07e480f`.
The committed XT07 source and all earlier frozen scopes remain untouched.
