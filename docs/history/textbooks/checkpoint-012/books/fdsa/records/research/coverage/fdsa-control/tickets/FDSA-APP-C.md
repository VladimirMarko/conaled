# FDSA-APP-C — Notation

State: accepted at f17cc6b; all ninety notation-correspondence rows covered; acceptance checkpoint saved/uploaded.
Triage: ready-for-agent. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, starting printed page 355.
Depends on: Chapter1 and shared list interface candidates; no sequential chapter activation.

Development starts from draft shared foundation candidate
`df116c2f6d834eeb952157505b5c93a9ab5497e8`, branch
`work/fdsa-list-foundations`. Combined foundation review base remains
`1aabd512284fe86254278ac631eda061d311050b`. This is the user-authorized
cross-cutting exception: every chapter relies on faithful notation translation.

## Scope

Cover every mathematical construction, theorem and exercise in this source unit,
with exact scope and reusable existing declarations inventoried before implementation.
Preserve the book's assumptions and cost model; harmonize with conaled interfaces.

## Completion gates

- [x] Item-by-item source coverage and reuse/gap map completed.
- [x] Definitions and proofs implemented without admissions or additional axioms.
- [x] Checked uses and statement review retained.
- [x] Applicable immutable-candidate build and exhaustive proof audit passed.
- [x] Independent Standards and Spec reviews have no unresolved findings.
- [x] Accepted candidate verified and recovery checkpoint saved/uploaded.

## Primary source links

No direct source hyperlink in the pinned PDF.

## Exact implementation scope

All 90 ordered items AC-001 through AC-090 in
`research/appendix-c-obligations.md` must be mapped to standard Lean semantics.
No theorem per editor glyph or parallel notation library is required. Preserve
explicit types, grouping, standard binders and the Prop/Bool boundary.

Retain meaningful connected checks for:

- Function composition and Boolean/propositional truth; list comprehensions
  preserving generator order and duplicate occurrences.
- Set membership, proper subset, image, restricted/two-variable comprehension,
  bounded quantification and unions/intersections without global decidability.
- The printed upper-interval error: correct `{..y}` to `Set.Iic y`, distinguish
  it from `Set.Ici y` by checked Nat cases at 0 and 2 with endpoint1; retain
  membership of all six interval forms.
- Integer division through `Int.fdiv`, with its nonnegative-divisor bridge and
  checked `5 fdiv (-2) = -3` versus Lean default quotient -2. Preserve typed
  natural/real division, integer floor/ceiling, and natural exponent meaning.
- List/multiset/set multiplicity distinctions, including submultiset `≤`
  versus support-only `⊆`, map/filter cardinality and indexed list updates.
  Reuse existing FunctionalBasics and ListLibrary clients where sufficient.
- Finite set sums/products through standard Finset operations with required
  commutativity; list folds retain the weaker ordered monoid capability.
  For unrestricted index sets, expose an explicit finite-set/otherwise-neutral
  adapter unless an existing exact standard construction is found. Prove its
  finite and infinite equations; demonstrate a function supported at one Nat
  over `Set.univ` still gives the source's neutral fold. Do not substitute
  `finsum`, an infinite series or a support-based fold.
- Record complete standard reuse mappings and per-claim statement review;
  preserve all required validation and independent review gates.

No acceptance is claimed by this in-progress ticket.

## Development record

The complete 90-row source map is retained in
`docs/research/fdsa-notation-map.md`. `Examples.FunctionalNotation` contains
typed standard-library correspondences, source-error counterexamples and a
small finite-index-set fold adapter with additive transport. It is written
but not yet compiled; focused validation follows the running XB01 build.
Root retains source/statement review and final independent review duties.

Draft durability candidate: `c994c22b754db5300d28670dff6b6f83ad56df02`.
No focused compile or acceptance is yet claimed.

A source-level refinement commit `50dc7df3649d9f4f33bc6b3464c2c9fb6399aa46`
adds the explicit Nat Finset interval dependency/type and uses the exact
`Finset.finite_toSet_toFinset` bridge. It remains uncompiled.

Latest draft durability candidate: `c80eec92f5458eccfd1c34c8314d666c2a1e3847`. This adds the
`Empty` index-type case for both finite-index fold adapters and updates its
statement-review notes. It remains uncompiled and unaccepted.

## Source-scope reconciliation, 2026-11-02

Current inventory: `research/appendix-c-obligations.md`,
SHA-256 `499d6d0632bf6f160add2edb7171588f1b23b96a314f25f7543a62c9ae614e2f`.
The earlier snapshot is preserved byte-for-byte under
`reviews/source-inventories-before-scope-repair/`. Reasons, IDs,
old/new hashes and remaining source gaps are recorded in
`research/scope-reconciliation.md` (SHA-256
`21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87`).
This clarifies required coverage without implementation or acceptance
credit. The chapter/appendix retains its current dependency gates.

The finite/infinite set-fold correspondence remains mandatory. The earlier
XB01 focused build was stopped; this draft still awaits compilation
using the idle isolated cache after Chapter 1 acceptance.


## Accepted foundation continuation — 4 November 2026

Accepted and integrated locally at `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`, from accepted Chapter1 base `07e480f6ec9958d4975bb90151005b84f2907614`. The original four-unit/nine-path scope and prefix c80eec92 are unchanged. The recovered full normal candidate check and exhaustive audit passed (967 checked project modules;45,294 kernel-safe declarations,25,117 theorems; only propext,Classical.choice,Quot.sound). These are whole-project counts. All145 actual public types were fully assessed by both independent axes with matching before/after inputs. Standards and Spec both passed with zero unresolved findings; FDN-ELAB-001/002 are resolved.

Qualified immediate `./check.sh --verify-candidate HEAD` passed at exactF before the local fast-forward at13:55:30UTC. The unrelated baseline file, tracked/index state and accepted Chapter1 history were preserved. No GitHub mutation or push occurred. The authoritative evidence and exact hashes are in `provenance/foundation-acceptance-20261104/acceptance.json`, with full/145/final-review/immediate/fast-forward records. Earlier development paragraphs above are historical, including interrupted or unknown-terminal attempts; their outcomes are not rewritten.

Acceptance checkpoint creation/upload is the remaining durability action; the combined checkpoint checkbox stays pending until that upload actually succeeds. No Chapter2, Chapter3 or other shared-unit acceptance follows automatically.

Accepted inventory coverage is AC-001 through AC-090 as typed notation correspondence, including the printed interval correction, integer-division distinction, multiplicity and finite/otherwise-neutral set folds.


Durability completed 2026-11-04T14:08:43.703250+00:00: verified/uploaded checkpoint0109,22,290,443bytes,SHA949b1525e093857799316ea33e22f82cec9056abbd2ef393a1fa8657b04a1e08,libfile_84959da777948191832d2e322bf6fb16. The earlier pending-upload wording records the capture boundary. See provenance/foundation-acceptance-20261104/durability.json.
