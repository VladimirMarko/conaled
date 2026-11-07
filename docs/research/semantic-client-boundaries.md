# Semantic clients and representation boundaries

Issue [#341](https://github.com/VladimirMarko/conaled/issues/341) adds an opt-in,
set-level boundary for existing exact computation squares. The interpretation
and square interfaces remain unchanged. The inspected baseline is
`b8731310f05efdac29f994706fbc1f32eb77de20`.

## Independent client and expected results

The specification selects an element of an indexed family `P w`. For languages,
`P : List α → Type` is a type of parses. A selected parse is data; its mere
existence does not determine it. We compare direct representation `P w` with
redundant representation `P w × Bool`, interpreted by first projection. A
semantic client applies two specified witness maps. Its result must not depend
on the extra flag, and replacing the redundant representation with the direct
one must preserve the selected result. An observer reporting the extra flag is
invalid at this semantic interface.

This case was frozen before encoding in the orchestration evidence. The
independent arithmetic order test applies increment then doubling to 3, giving
8. A nonconstant family selects index n in `Fin (n+1)`; reindexing first by
increment and then by doubling selects index 7 at input 3, in `Fin 8`. The
ambiguous language `fun _ => Bool` has two distinct specified parses at each
word. Flags may be identified while those alternatives must remain distinct.

## Existing guarantees and missing boundary

Felix's pinned [MakeLawful](https://raw.githubusercontent.com/conal/felix/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda)
derives laws with equivalence induced by the interpretation. Its
[comma construction](https://raw.githubusercontent.com/conal/felix/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda)
exposes both component arrows and their compatibility proof. These supply law
transport and certified maps; they do not prohibit arbitrary functions on raw
representations. The earlier [inspection](denotation-boundaries-and-settings.md)
records their relation to local APIs.

Locally, `Squares.compose` derives composite commuting evidence from primitive
squares. `CategoryMap.RawMap.quotientFunctor` already descends category maps to
hom quotients. The new construction applies the same quotient-elimination
principle to represented values and existing `Squares.Square` computations;
it does not add another category law-transport mechanism.

The [#210 FIFO experiment](abstract-fifo-client.md) already proves representation
independence for every finite command-word client using relational simulation.
It retains nonfunctional interpretations and an observation that cannot be
admitted. The [#211 cost experiment](modular-fifo-costs.md) hides a potential
from its public proof interface, without claiming protection against arbitrary
Lean code. Neither establishes invariance for every function on the raw carrier.
The new handle theorem covers every pure total function on a quotient handle,
with the narrower exact functional interpretation and host-equality contract.

## Checked construction and uses

[SemanticBoundary](../../SquareKit/SemanticBoundary.lean) defines a setoid on
`A.R` by `A.decode x = A.decode y` and a `Handle A` as its quotient.
`pack` introduces raw representatives. `meaning` descends the decoder and
returns the entire semantic value. It supplies a specification, not a promise
that all denotations are executable.

`client_invariant` applies to every `client : Handle A → T`, including arbitrary
Lean functions: equal meanings give equal handles by `Quotient.sound`, hence
equal results by congruence. The client need not carry a respectfulness proof.
The type has already identified the irrelevant distinctions. This is a
mathematical guarantee for pure total functions, not a security or timing
noninterference claim about unsafe code or foreign effects.

`lift` turns any existing square into a handle operation. Its elimination
obligation is derived from `Square.commutes`: equal input meanings imply equal
output meanings. `lift_meaning`, `lift_identity` and `lift_compose` establish
correctness, identity and two-step composition. `implementation_independent`
shows that two squares with pointwise equal specification functions return
equal output handles. The implementation functions may differ.

[SemanticClientBoundary](../../Examples/SemanticClientBoundary.lean) checks the
frozen cases. `redundantMap` deliberately toggles the raw flag while applying
the specified witness map. `no_flag_observer` refutes the existence of a handle
client agreeing with raw flag projection on every representative. `repack`
identifies repacking with the original handle although the raw flag can change.
`replacement` passes a shared two-step client through direct/redundant adapters.
`selected_parse` retains an arbitrary chosen `p : P w`, while
`alternatives_distinct` proves that the two parses of the ambiguous language
are not collapsed. `selected_client` and `ordered_client` use `lift_meaning`
to recover the selected result after composed operations.

`reindex` is precomposition of a family of handles. `reindex_compose` and
`reindex_meaning` express its strict index and meaning behavior;
`selected_reindexed` exercises these on the nonconstant `Fin` family.
This is reindexing of already indexed families in Lean, not arbitrary
object-language identity elimination or a higher coherence theorem.

## Alternatives and precise limits

| Boundary | What must be established | What a client obtains |
|---|---|---|
| Abstract handles or modules | Only admitted operations are exposed; their interpretations respect the specification; abstraction/parametricity argument for the chosen language | Representation freedom relative to that interface. Merely marking a definition private is insufficient evidence of universal invariance. |
| Certified operations on raw values | Each primitive has a preservation or relational simulation proof; the client language composes admitted primitives | Existing square and FIFO results derive correctness for the admitted client fragment. Raw carrier access still permits unrelated operations. |
| Quotient handles in this experiment | A setoid identifying exactly the intended set-level distinctions; quotient elimination for primitive operations | Every pure handle client is invariant under that setoid. Existing squares discharge the operation obligations. |

The [Lean quotient reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/)
specifies introduction, elimination with respectfulness, and quotient equality.
The checked code uses the repository's pinned Lean version, rather than relying
on the current documentation alone. A quotient need not enumerate an equivalence
class or execute `decode` to compute `lift` on a packed representative. This
study does not establish runtime erasure, allocation costs or timing independence.

The quotient is not a solution for all meanings. For a many-valued relation,
"sharing a possible meaning" need not be transitive. For example, representation
meanings `{0}`, `{0,1}`, `{1}` share neighbors but not endpoints. Taking its
transitive closure would make an extra identification. ADR 0002's relational
squares and witness-space bridges therefore remain separate and useful.

Likewise, this quotient records a proposition-valued relation and uses host
identity. It does not preserve a type of distinct identity paths merely because
those paths have the same endpoints. Selected parses survive because they are
values *inside* the semantic type, and the equivalence identifies only equal
values. Replacing `P w` with `Nonempty (P w)` would change that contract.
General dependent or higher interfaces must retain their specified path and
transport data explicitly; #340 and #342 own the broader comparison. There is
no claim that every setting admits this quotient boundary.

Raw `A.R` and square implementations remain accessible for compiler work.
A compiler pass may inspect or change a flag, choose an algorithm or normalize
a representation. To expose its result as a semantic operation it supplies a
commuting square (or the appropriate separate relational contract). A function
on raw values is not automatically promoted to a handle client. Even a
noncomputable choice of a representative from a handle cannot recover each
original flag: `no_flag_observer` rules out agreement on both representatives.

## Statement review, validation and decision

The relation is an equivalence for every decoder, including noninjective and
nonsurjective ones. No inverse or decidable equality is assumed. Handles cover
represented meanings only; surjectivity onto all semantic values is not claimed.
The direct and redundant examples inhabit the relevant types. The negative
observer theorem requires a witness to avoid a vacuous empty domain. Its
conclusion concerns exact agreement with raw flags, not the impossibility of
all Boolean observations. Composition and replacement preserve decoded selected
values; no equality of raw implementations follows.

The initial missing connection was descent of existing value squares to a type
whose arbitrary pure clients respect equal meanings. It is now derived once.
Each provider supplies the same local commuting proof it already needed;
clients supply no additional invariance proof. Indexed reindexing is ordinary
precomposition and introduces no new semantic axioms. This is a bounded
obligation comparison, not a measured agent-productivity result.

Adopt this opt-in boundary for exact set-level clients where identifying equal
meanings is the intended contract. Retain relational simulations for their
existing nonfunctional clients. Investigate evidence-sensitive/higher boundaries
under #340/#342 rather than promoting quotient handles to a universal interface.
No migration of existing callers is required by this result. A future executable
consumer must measure costs separately before choosing this runtime encoding.

Focused build: `direnv exec . lake build Examples.SemanticClientBoundary`.
The orchestration review record supplies the final isolated-candidate full build,
exhaustive audit and independent Standards/Spec outcomes. The report's formal
claims are the linked Lean declarations; alternative-interface comparisons and
the many-valued obstruction are paper arguments.
