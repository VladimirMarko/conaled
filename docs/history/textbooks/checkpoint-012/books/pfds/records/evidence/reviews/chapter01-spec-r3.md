# Chapter 1 independent Spec review — round 3

Reviewer: `/root/chapter01_review/spec`, 2026-11-02.

**Outcome: Passed.** Zero unresolved Spec findings; worst unresolved severity:
none. This is approval of the introductory source-accounting documentation,
not proof acceptance for the thesis summary bounds, ticket10013, or the whole
book/thesis union.

## Pinned scope and requirements

- Fixed base and confirmed merge-base:
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Candidate: `1ce161412a2cfb725f27525ff98d400209163316`.
- Clean isolated checkout: `review-ch01-r3`.
- Full-scope comparison:
  `git diff 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd...1ce161412a2cfb725f27525ff98d400209163316`.
- Commits: `99340c7` (introductory contracts), `cbb1e27` (source qualification
  and terminology correction), `1ce1614` (book/thesis union).
- Entire diff: 375 added lines in `docs/SOURCES.md`,
  `docs/research/pfds-reconstruction.md`, and
  `docs/research/pfds-union-coverage.md`. No Lean, configuration, dependency,
  tooling, or mathematical declaration change is included.
- Independent formal ticket10013 is excluded by ancestry, not silently omitted
  from an integrated formal review. It remains unaccepted under this review.

Requirements read in full and fingerprinted:

| Requirement | SHA-256 |
| --- | --- |
| Original `requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `requirements/REQUEST-union-v2.md`, version2 | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `requirements/chapter01-union-v2.md`, version2 | `635724779ed3ea1d5ffd9779df943c1ce9e30ba5cf43a82024c3feb80fea1741` |

The original whole-book objective, chapter order, local tracking, recovery
checkpoints, and architecture requirements remain binding. The user's later
message expands the source to the union; it does not replace those conditions.
The bounded chapter01 requirements are assessed under that original objective,
not treated as permission to discard source mathematics.

## Primary-source and statement review

Both complete introductions were independently read from the supplied PDFs:
book printed pp1–6 and thesis printed pp1–6, each physical PDF13–18. The book
has 232 physical pages and the thesis 162. The recorded source SHA-256 values
identify the exact copies checked by the matching validation record:

- Book: `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
- Thesis: `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`.

Primary files are `research-pfds/source-assets/okasaki-book-2003.pdf` and
`research-pfds/source-assets/okasaki-thesis-1996.pdf`. I independently viewed
`research-pfds/full-book-render/pdf-018.png`: the missing book printed p6 is
blank. I also viewed `research-pfds/union/thesis-p3.png` to check the table's
operation names, logarithms, and dagger qualifications; this avoids relying on
the damaged mathematical OCR. Thesis p6 is substantive roadmap prose.

The candidate preserves the book's five section distinctions and all six thesis
introductory topics. The source-language paragraph retains polymorphic recursion
and recursive modules as later implementation/correspondence obligations. The
operator/invocation and logical-identity distinctions are accurate. Historical
lower-bound references and the introduction's broad strict/lazy comparison are
not silently made axioms or unrestricted impossibility theorems; their relevant
evaluation, memoization, history, and resource premises remain later work.

### All sixteen forward contracts

The ledger at `pfds-union-coverage.md:17–55` accurately retains every Table1.1
row, its operations, mode, printed target page, section and later book owner:

- T1.01–T1.05 retain the five queue realizations. In particular T1.04 retains
  constant worst-case `head` and amortized iterated-logarithmic `snoc`/`tail`;
  it is not substituted with the later constant-amortized variation.
- T1.06–T1.08 retain all six deque end operations and distinguish the two
  amortized rows from the real-time worst-case row.
- T1.09–T1.11 retain catenation, including logarithmic amortized append for the
  simple catenable deque and constant amortized append for the other two rows.
- T1.12–T1.14 retain the separate constant/logarithmic operation bounds for
  random-access lists, skew binomial heaps and bootstrapped heaps, all with
  the table's worst-case qualification.
- T1.15–T1.16 retain logarithmic `add` and linear `sort`, distinguishing
  amortized sortable collections from worst-case scheduled collections.

The owner choices match the book's roadmap: Ch6 amortized queues/sorting; Ch7
scheduled queues/sorting; Ch8 deques; Ch9 numerical structures; Ch10
bootstrapping/catenable lists; Ch11 implicit structures/catenable deques.
The source table's `++` is explicitly represented as `append`.

Every row is unproved. Size, operation-domain, primitive-cost, demand and
persistence assumptions must be fixed by the owning specification. This is an
honest forward obligation, not a vacuous or circular theorem: no Lean result
is introduced or allowed to depend on the table as an axiom. The
example-driven-development statement-review criteria were applied to these
intended contracts and to their distinction from value-only equality; a
documentation inventory is not counted as a checked mathematical application.

### Initial crosswalk and eight known supplements

I checked the consequential claims directly against the following primary
source passages, in addition to the saved inventories:

| Item | Primary evidence and assessment |
| --- | --- |
| TU.A | Thesis pp131–136: syntax/static/dynamic additions, fresh thunk allocation, effectful matching, nonmemoized failed forcing, recursive environment updates and optional blackhole detection are accurately retained. This is distinct from the book's Haskell appendix and is not a claim to implement the entire external SML Definition. |
| TU.SEG | Thesis pp75–76: common real-time deque representation, bulk linking/unlinking, minimum-root-at-smallest-tree invariant and exact list/heap bounds are preserved. Source `findMin` is logarithmic here. Book pp127–129 describe related numeral schemes without supplying this same construction. |
| TU.DIG123 | Thesis pp110–111 versus book pp126–127: thesis digits1/2/3 with safe2 differ from book digits0/1/2 with safe1. The incompatible ordinary-binary debit invariants and alternating-operation counterexample are retained. A constructor rename is correctly insufficient. |
| TU.SCHEDULE | Thesis pp109–110 and book p91: both use completed-zero range separation, but digit increment and scheduled binomial heaps remain separate realizations requiring checked instances of any shared proof. Thesis Theorem8.1 remains a separate amortized claim. |
| TU.FORCE | Thesis pp8–10 and107, book pp32–33: delayed pattern matching versus early forcing, `take`, deliberate one-level-ahead increment, and `fun lazy` desugaring are accurately distinguished. Fully forced result equality is correctly insufficient. |
| TU.TRACE | Thesis pp19–24: cycles, parallel edges, multiple arguments/results, different persistent identities, fresh debit sets and discharge/realization multisets are retained. Realized cost counts the union of memoized debits; repeated discharges may still contribute repeatedly. No DAG or single-path reduction is assumed. |
| TU.MODULES | Thesis pp4,86–90,100–102: nonuniform-to-uniform representation translation and the generic higher-order heap bootstrap remain obligations with primitive cost premises and the source restriction on effectful functors. A single concrete heap is not claimed to cover the transformation. |
| TU.BOOTVAR | Thesis p90 and book p150 Exercise10.5: both extra constant-amortized queue sketches are retained, and the book's primitive-queue functor exercise is not assumed to discharge them. The second thesis sketch's limited detail is explicit. |

The candidate clearly labels this an initial later-source crosswalk, not an
exhaustive union inventory. Its exercise/theorem heading counts are navigation
from `book-full-inventory.md` and `book-exercise-index.json`, not a claim that
every later theorem, exercise subpart, algorithm or invariant has been reviewed
or proved. Chapter2 accounting retains all six exercises and the distinction
between copying, comparisons, visits and shared graph space.

The unchanged interfaces referenced in the reconstruction were inspected:
`AbstractFIFO.Ops`, `Simulation`, `Simulation.client_eq`, `Resources.Measured`,
`Resources.Workload`, `TreeFlattening.appendWithCost_exact`,
`FIFOContracts.appendRun_exact`, and the basic `Durability.Heap`/`Extends`/`put`
laws. The documentation accurately distinguishes interface evidence, sequential
observations, copied-cell count, terminating-node visits, and immutable heap
extension. It claims neither stack coverage from FIFO nor machine allocation
or crash durability from these definitions.

## Prior findings

| Stable ID | Severity when raised | Round3 disposition and evidence |
| --- | --- | --- |
| CH01-SPEC-001 | Medium | **Resolved.** The primary complete book supplies the previously uninspected p6, independently viewed as blank. Reconstruction lines39–45 correct the completeness boundary while retaining the history of withheld acceptance. The prior source-completeness gate is now satisfied. |
| CH01-SPEC-002 | Low | **Fixed, retained.** Reconstruction line51 maps operators to function fields and invocations to commands/events, and separates logical persistent identity from root/cell addresses. This agrees with book pp3–4 and thesis pp4–5. |

No new Spec finding is established. No historical finding was dropped or
renumbered.

## Validation, completion boundary and integration

Reused `reviews/chapter01-validation-r3.txt` and inspected its
`validation/check-ch01-union.py` implementation. It records the successful
pinned-Nix checks for exact clean candidate identity, original merge-base,
three-file scope, whitespace, fifteen local Markdown targets, both source
fingerprints, sixteen row IDs/owners/modes and eight supplement IDs. The table
check agrees with an inventory; it is not a mathematical/source-truth test.
The primary-source review above supplies that independent content assessment.
I also confirmed the isolated checkout remains clean at the exact candidate.

No Lean build/audit was run or asserted. There is no formal source change in
this scope, and artifact-appropriate document validation is sufficient for this
milestone. The independent formal ticket10013 needs its own applicable full
validation and review; this outcome supplies none of them.

The original chapter-order requirement is preserved. The fully inspected book
introduction is expository and contains no numbered theorem, exercise,
algorithm or code listing. Its later technical claims and the thesis table
are explicitly retained with owners. Thus an accepted **introductory
source-accounting milestone** can move the primary book frontier to Chapter2.
It must not be reported as proof of thesis Table1.1, as completion of either
whole source, or as removal of those later proof obligations. Candidate
reconstruction lines81–94 and union-ledger lines19–55 state this boundary
correctly; no wording found overstates it.

The planned integration onto the main local branch containing unrelated
formal work is acceptable only as scoped documentation integration: all three
reviewed file blobs must remain identical, the integration commit and equality
evidence must be recorded, and ticket10013 must remain explicitly excluded.
Any conflict resolution or change to those blobs requires renewed review.
This review does not approve the future integration commit or unrelated formal
content in advance. Source manuscript copies remain excluded from delivered
repository/checkpoint payloads; identities and recovery records are retained.

**Final disposition:** base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, candidate
`1ce161412a2cfb725f27525ff98d400209163316`; **Passed**, zero unresolved Spec
findings, worst unresolved severity none.
