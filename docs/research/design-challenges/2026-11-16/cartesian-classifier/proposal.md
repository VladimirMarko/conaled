# Cartesian classifier beyond vertex local systems

Candidate research construction for #602, based on repository revision
`7406fbe2aceba3693856cc6998aae613011df1f5`. This is a mathematical construction
for challenge, not a new Lean theorem or an adopted implementation.

## Domain and source boundary

C is the Cartesian cube category of #599: n-tuples of variables and endpoints,
with repetition allowed. I is y(1). Work classically with Cof equal to the
whole subobject classifier Ω. A cofibration over Γ is any subpresheaf φ⊆Γ.
This contains the finite face/diagonal formulas of #600. It imposes a stronger
filling requirement on arbitrary input families than asking only for those
formulas: no extension from formula-cofibrant Kan structures to this class is
claimed. The #600 nerve and tuple fillers already work for this class because
their only extra test is closed-vertex membership, classically decidable.

For every small Γ, the declared domain consists of arbitrary dependent
presheaves A on its category of elements, with Type u fibers and a selected
uniform diagonal composition operation for Cof. This operation takes any
represented line p:y(n)×I→Γ, arbitrary r,s:y(n)→I, tube over φ×I, and a base
over r; it returns an element at s, agrees with the tube, and agrees with the
base on r=s. Uniformity is equality under every Cartesian substitution,
including diagonals. Filling is composition with a fresh variable as target.
Represented charts extend the operation to arbitrary contexts. No discrete,
local-system, groupoidal, finite, or source-lift presentation is an input.

C and each slice C/n are small in Type 0. Sieves on a represented cube are
predicates on a small set of arrows and hence small. Products of Type u sets
indexed by these small shapes remain Type u. The collection of families and
selected operations over y(n) is Type(u+1), while decoding has Type u fibers.
No resizing or inaccessible cardinal is requested. For u=0, use a host
universe containing the small shape indexes; raising all levels by one is
harmless if a concrete Lean encoding needs it.

Every sieve is pointwise decidable in the classical metatheory. This is not
an assertion that the internal presheaf logic is Boolean: a sieve need not
have a pullback-stable complement. Pullback, finite unions, intersections and
interval quantification exist in Ω. Explicitly, (∀I φ)(x) holds when all
restrictions x|f and every interval term t at that restriction lie in φ.
This is a small universal quantification, stable under substitution. Endpoints
are distinct and equalizers of interval terms are cofibrations.

The primary external input is ABCFHL, *Syntax and Models of Cartesian Cubical
Type Theory*, author manuscript
https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf, downloaded 2026-11-16,
SHA-256 `ea235cf09eae29d3859f31976bc43a939a6565410ff4117addb99d0602c213a3`.
Definition 1 specifies diagonal composition. Sections 2.7, 2.11 and 2.12 give
relative extension, aligned Glue, universe composition and ua; Theorem 1 and
§3.2 justify them for represented presheaf universes. Theorem 2 requires a
finite-product base, distinct endpoints and pointwise decidable sieves closed
under interval equality, disjunction and interval quantification. Its §3.2
explicitly permits Ω classically. Strictification is justified there by
Orton–Pitts Theorem 6.3; it is not internal decidability. These external
constructions are used below with their formulas and hypotheses, rather than
claiming a fresh Lean verification or importing model existence alone.

## Represented classifier and decoder

Define U(n) as small families with the specified composition over y(n).
Reindex along h:m→n by represented pullback, including the chosen composition.
Use a split presentation of dependent families; if the implementation uses
categorical records, insert the canonical reassociation equalities. Their
identity/composition laws follow from substitution, not from choosing an
unrelated representative after every pullback.

The universal decoder of a code a∈U(n) at its generic point is a(id_n).
On a restriction h:m→n, its map is the restriction map of a from id_n to h,
followed by the equality identifying (a[h])(id_m) with a(h). Given any input
(A,F) over Γ, define

    code(A,F)(x) = (A,F)[represented(x)].

The decoder isomorphism at x evaluates at id; its inverse regards a∈A(x) as
the same generic element in that chart. Naturality is A's restriction law.
The decoder's composition at a represented line uses the chosen composition
of the code at its generic (n+1)-cube. Thus decoding code(A,F) recovers the
whole operation F, not just the fiber sets. Code substitution is represented
pullback associativity. This is the Cartesian analogue of the inspected
`LocalFamily.code`, `decodeCodeIso` and classification filler comparison in
`SmallFamilyClassification.lean`; those Lean results themselves use D.

The universe has a chosen composition operation, constructed next. Merely
forming this code presheaf does not establish it.

## Aligned Glue as a construction requirement

For φ⊆Γ, a family T over φ, a total B, and a fiberwise homotopy equivalence
f:T→B|φ, start with the family of pairs

    (b, t), where t is a section of T over φ and f(t)=b on φ.

Here partial elements are internal sections over all refinements of a point,
not an external option holding one value when φ happens to hold. Strictify
this family to G so that G|φ=T and unglue|φ=f. An explicit external recipe
uses the canonical isomorphism to T at points lying in φ, retains the pair
family elsewhere, and conjugates each restriction map by these isomorphisms.
There is no need for the complement to be a subpresheaf. Restriction into φ
uses the appropriate target isomorphism. Identity/composition follow by
cancellation. Fixed conditional representatives and proof irrelevance make
the construction stable under reindexing, with the canonical record casts.

For a G box (p,r,s,ψ,u,b), first compose unglue(u), unglue(b) in B, obtaining
b'. Over φ at s, extend a partial element in the contractible homotopy fiber
Fib(f_s,b'). Its prescribed part on ψ∨(r=s) is the actual endpoint u_s or b,
paired with the constant path of its unglued image. The prescribed elements
agree on the intersection by the box boundary law. Let (t,q) be the resulting
extension, where q:f_s(t)~b'. Correct b' along q by composition from 1 to 0,
with an extra constant tube on ψ∨(r=s). The corrected value equals f_s(t)
on φ_s and equals the original prescribed output on ψ∨(r=s), so strict glue
returns a lawful output `icom`. This uses the entire fiber contraction record;
no inverse is chosen from an existence proposition.

`icom` need not recover T's chosen operation when the whole line lies in φ.
Set χ=∀z.φ(p(-,z)). Add on χ the tube obtained by filling the original box
with T's selected composition. Apply `icom` to this enlarged tube. Its
boundary equation gives exactly T's chosen result on χ. This aligned
composition is the needed record-level restriction law. Every step uses
natural maps, selected compositions, and relative extension, hence commutes
with substitution. The diagonal equation is protected by the r=s tube.
This is the operational reason both diagonal cofibrations and ∀I appear.

The extension subroutine is the contraction-and-filler recipe already used
in #600: compose from the contraction center along its partial contraction
tube. `HomotopyContractible.extend` and `extend_reindex` are inspected source
analogues, not already Cartesian Lean implementations. Sigma, Pi and Path
composition supply the homotopy fiber filler; Path composition adds its two
endpoint faces. The Pi formula uses backward filling from the target to the
source, so arbitrary source/target interval terms are required.

For a U box with base B and tube T(z) on ψ, set its output at s to the code of

    Glue [ ψ ↦ (T(s), transport_T(s→r)),
           r=s ↦ (B, id) ] B.

Choose the equivalence record for transport by transporting the identity
record, so it is the identity record on r=s as well as having identity map.
The partial families, equivalences and their chosen compositions then agree
on the overlap. Aligned Glue makes the resulting U code equal to T(s) on ψ
and B on r=s, as complete records. Replacing s by a fresh coordinate produces
a chosen universe filler. All its ingredients are defined before application
to any source client.

For e:A≃B, define

    ua_U(e)(i) = code(Glue [i=0 ↦ (A,e), i=1 ↦ (B,id)] B).

The endpoint equations include the chosen compositions. Glue composition
provides a native homotopy β_e:transport(ua_U(e))~e. The external univalence
argument supplies contraction of each fiber of
`coe:Path_U(A,B)→Equiv(El A,El B)`; this is an explicit dependency on the
ABCFHL univalence construction, not a consequence asserted from endpoint
agreement alone. Its contractible-fiber data is needed for the overlap below.
A formal port must include that construction, not add contraction as a field
which callers are asked to assume. No external code was executed here.

## Finite overlap and original selected witnesses

Let N be #600's finite-set groupoid nerve and D_N its tuple decoder, with its
chosen all-box filler. Define a map J:N→U by represented classification of
that exact decoder. Although N itself is Type(u+1), each represented pullback
of D_N has Type u fibers. The chart construction therefore uses U_u and does
not silently promote the frozen small universe.

For every T:y(n)→N, the decoder comparison

    El_U(JT) ≅ D_N(T)

is generic evaluation, includes every tuple entry and compatibility equation,
and identifies the selected filler. It commutes with endpoints and every
Cartesian substitution. Its identity and composite substitution laws are
chart associativity. This gives more than an agreement of closed readouts.

For an actual finite bijection e, compare ua_U(e) with J(ua_N(e)), conjugating
through the displayed endpoint decoder isomorphisms. Tuple transport and β_e
identify their complete coe records in the discrete family of bijections.
Lift both into the same contractible fiber of coe and connect them there.
Projection gives a selected two-path with the exact endpoint code boundary.
The fiber lift includes its path-to-e component; it is not an assertion that
universe path bodies are equal. Since the finite equivalence family is
presented discrete, its generic paths and complete equivalence witnesses are
unique. This is where the finite hypothesis is used.

Freeze #600's Fin3 target square T and the original source square H as in
that report. In U, independently construct the composition comparison of
ua_U(swap12∘swap01) with the selected concatenation. Use the preceding
endpoint two-paths to align J(T) to those same boundary paths. Both squares
map to the same constant complete finite equivalence in Equiv(El a,El a).
Lift them to the corresponding contractible coe fiber, prescribe both squares
and their shared boundary, and apply relative extension. Projection is a
native three-path Ω_U, retaining both complete square bodies as faces.

In RU, retain the *original* #600 construction Ω_R from exact H to the
boundary-aligned Real_C(T), using its exact j_S, α, δp and δq. It is not
recomputed from U, nor replaced by equality after an observation. The comparison
is the span with common mediator T:

    H  ~[Ω_R]~  aligned Real_C(T)     T     aligned J(T)  ~[Ω_U]~ H_U.

The two middle realizations have the specified tuple decoder isomorphisms.
This is a comparison on the finite overlap, not a map RU→U or a native path
between terms of different universes. Each leg retains the original witness
as a face; it is not claiming to recover arbitrary source interiors from N.
If #602 requires a single global RU→U map, this candidate does not provide it.

Fix the finite choices at the closed client, then define their values at every
base substitution by pullback. Thus Ω(σ∘τ)=Ω(σ)[τ] including all faces; do not
invoke fresh unspecified choices at each substituted instance. The separate
N→U classifier and Glue/ua operations themselves are natural for arbitrary
inputs. Bool identity/negation retain true/false transport, and Fin3 swap
orders retain 0↦2 versus 0↦1. The complete inverse/composite records and all
five Fin3/Phase package fields continue to be identified by #600's presented
discrete proof. None of these arguments establishes arbitrary higher fillers
are unique.

## Higher consumer and separating observation

Use the one-object groupoid B(Z/2), whose automorphisms are 0 and 1 under
addition mod 2. Let A=N(B(Z/2)) using the all-box nerve recipe of #600, now as
a **decoded family over terminal**, not as the finite-set code nerve. A has
one vertex, but two based paths. A square with constant vertical sides and
bottom g, top h satisfies h=g by the groupoid functor equation. Therefore the
two based paths are not relatively homotopic. This rules out classification
of A, even up to native equivalence, by any decoded finite local system:
those fibers have contractible or empty path spaces, whereas A has these
two distinct based-path components. It is a specific obstruction to reusing
the old decoder for the enlarged domain, not an obstruction to U.

There is a higher test of U itself. For z∈Z/2, the central natural automorphism
of the identity functor of B(Z/2) induces a homotopy h_z:id_A~id_A. On a cube
F:V_n→B(Z/2) and a new Boolean coordinate ε, define its arrow between (v,ε)
and (w,ε') by

    h_z(F)((v,ε),(w,ε')) = F(v,w) + (ε'-ε)z.

Evaluate interval terms at vertices. This formula commutes with Cartesian
substitution, has identity-map endpoints and evaluates at the sole vertex
to the loop z. It therefore constructs the homotopy rather than inferring
it from a cardinality argument.

Each time slice h_z(i) is an equivalence: transport the identity equivalence
structure along the map homotopy, and use the proposition property of
isEquiv to align its endpoint records with the chosen identity record.
Equivalently, relative extension in the contractible isEquiv fibers makes
this alignment. This yields a loop E_z at the full identity equivalence.
Any two-path between E_0 and E_1 would, after projecting to maps and evaluating
at the sole vertex, give a relative homotopy between 0 and 1 in A, impossible.

Applying ua_U to E_z gives a two-path at ua_U(id), a universe loop based at
code(A). Applying coe and the natural β comparison recovers E_z up to native
homotopy. Thus a three-path between the two resulting universe two-paths
would contradict the same evaluation test. The distinction is higher universe
data that cannot be encoded by a tuple decoder of sets. No truncation or
vertex-only comparison is used for this consumer. This calculation uses only
finite groups and the existing nerve recipe, but its decoded family has
non-discrete paths; it is beyond the finite-local-system domain.

## Challenge questions and validation boundary

The proposed outcome is the full-sieve declared-domain classifier and the
finite common-nerve comparison span. Its new paper-level derivations are
represented Cartesian classification, overlap comparisons and the explicit
higher consumer. Glue/univalence construction dependencies remain externally
proved and must be ported to count as local formal results.

Challenge the universe sizes and strictification under arbitrary substitutions;
check that alignment really preserves complete composition structures, including
overlap identity witnesses. Check the claimed nontrivial two-path consumer,
and whether the two-leg native span meets the requested cross-model comparison
rather than silently weakening it. Check the stronger Cof domain restriction:
families with only finite-formula filling are not silently included. Consider
using exactly the finite face/diagonal lattice instead; its ∀I closure can be
proved by generic-variable elimination, avoiding this strengthening, but that
proof is not included in this candidate.

No Lean changes, builds or proof audits were run. The source PDF checksum and
named local declarations were inspected; the external Agda development was
not executed. Research adoption requires the three design lenses and separate
Standards/Spec review. Formal implementation must independently verify code/
decode/filler recovery, Glue's diagonal and ∀-alignment laws, ua transport,
the complete finite square span, and the Z/2 higher separation case.
