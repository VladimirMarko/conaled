# FDSA-APP-C — Notation

State: cross-cutting implementation in progress; acceptance pending.
Triage: in-progress. Parent: FDSA-000.

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

- [ ] Item-by-item source coverage and reuse/gap map completed.
- [ ] Definitions and proofs implemented without admissions or additional axioms.
- [ ] Checked uses and statement review retained.
- [ ] Applicable immutable-candidate build and exhaustive proof audit passed.
- [ ] Independent Standards and Spec reviews have no unresolved findings.
- [ ] Accepted candidate verified and recovery checkpoint saved/uploaded.

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
