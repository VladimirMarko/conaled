# Independent bounded review — #1016 Decide plan

**Outcome: clear for planning; no actionable findings.**
This reviews a frozen source/reuse plan within the existing whole-book
workflow. It is not an ordinary implementation review axis, a compiler result,
or acceptance of Decide or the running candidate. The proposed source
presentations, adapters, computations and connected examples remain future
checked implementation obligations.

## Exact reviewed inputs and scope

- Root announced `../specs/1016-Decide.md` frozen before assessment:
  SHA-256 `ca2a19ddf844a90d8647fe4209fe0ea4302de6578df90541b5a2b143ad9b94e0`,
  31,410 bytes, 438 lines. The identity was independently checked before
  and after the complete plan read. No correction was requested or made.
- Full VFA 2.1 `Decide.v`: SHA-256
  `f929d55e2b7b39f2ba0bb72f2e70285dc8e10e64cf18322060bdbfc0552a4b26`,
  19,701 bytes, 506 lines. I independently read the complete source,
  including both scratchpads, the unnamed closed goal, the abandoned opaque
  computation, the source's two pedagogical axioms and the final tradeoff
  discussion. The release cover and chapter footer are distinguished.
- Full inventory metadata: `../source/Decide.inventory.json`, SHA-256
  `5db3fc7c2f070863f2dc63271512d26b54a18d0d2c3cc198a162cc48221a322c`.
- Project HEAD at the final read-only check was
  `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, with clean working tree.
  No accepted Binom predecessor is claimed. Current Perm code and predecessor
  plans remain evidence for proposed reuse, not already accepted APIs.

Applicable AGENTS, architecture/domain guidance, GLOSSARY, language direction,
ADRs 0001/0002/0010, the implementation workflow, README build/audit rules and
local user requirements were followed. The computational-assumptions note
was read in full, and the relevant resource/execution boundaries were checked.
The report is the only file written for this Decide assignment.

## Coverage reconciliation

The plan contains all **32 inventory IDs exactly once and in inventory order**.
Their classifications agree: seventeen definitions, eight source-proved
records, one transparently proved definition, three admissions, two source
assumptions and one pedagogical abort. Both standard two-star exercises retain
their exact source ranges, 267–285 and 460–472. All **15 command kinds and line
numbers** match in order; both modules have explicit dispositions.

The complete source read also confirms coverage beyond named exercises:

- The unnamed closed comparison goal is retained as a checked calculation.
- The two reflected proofs of the same inequality retain their method
  distinction rather than becoming unrelated arithmetic demonstrations.
- The generic sum permits both tags when both propositions hold, and the
  impossible right-tag example retains its actual false proposition.
- The decision-definition equality has separate computational observations.
- The two global assumptions become scoped parameters with concrete Nat
  realizations; neither is imported as a trusted declaration.
- The aborted computation is treated as an explanation of the source's
  mechanism, not as a missing theorem requiring a fabricated Lean failure.
- The admitted membership definition and admitted exact source example are
  both required. Positional list equality is not replaced by permutation.
- Historical and consistency discussions are context; the plan does not
  silently introduce a universal decider, a consistency theorem or a new
  reflection engine.

## Actual pinned decision representation

I inspected the consequential declarations directly in the installed Lean
4.35.0 sources, rather than relying on an older description of Decidable.
`Init/Prelude.lean` defines `Decidable p` as a class whose data field is a Bool
and whose proof field establishes `Bool.Reflects p` for that Bool. Its actual
constructor is `Decidable.intro`; `isFalse` and `isTrue` are match-pattern
abbreviations, and `falseTrueCases` supplies the familiar eliminator.

The plan accurately separates source `reflect P b`, which is Set-valued,
from Lean's Prop-valued `Bool.Reflects`. It preserves the intended information
using existing Bool correctness laws and native decisions. The true and false
reflection cases have the claimed propositions, and the stated converse
providers require a decision instance as described.

`Init/Core.lean`'s `decidable_of_decidable_of_iff` copies the existing decision's
Bool and transports only its proof. `Init/PropLemmas.lean`'s Boolean adapter
stores the supplied Bool directly. The unprimed and primed iff adapters have
the orientations stated in the plan. Thus an opaque Prop proof supplied to
this adapter does not become the data being inspected to choose the branch.
The provider's warning about rewriting computational decision data through
propositional extensionality is accurately represented.

The actual `Subsingleton (Decidable p)` instance supports mathematical
equality for decisions of the same proposition. The plan correctly refuses
to infer a particular definition's reduction or execution behavior from that
equality alone. Existing Perm `reflectedLt` stores the decidable Nat comparison
through the Boolean adapter; its positive and negative branch equations have
the advertised source forms. Their future reuse is conditional on acceptance.

## Generic proof sums and their specialization

The pinned `PLift` and `Sum` are appropriate existing carriers for arbitrary
propositions A and B. Proof irrelevance within a lifted branch does not
identify Sum's left and right tags. The plan therefore preserves both values
of the both-true example, their distinguishability, and the refutation of a
right value whose proof payload would assert the false inequality.

The switch to Decidable is explicitly limited to the proposition/negation
specialization. The proposed two case maps, round trips and tag equations
connect that specialization to the generic source examples. They are a small
source correspondence obligation, not a proposed parallel decision hierarchy.
There is no impossible claim that arbitrary `sumbool A B` is equivalent to
`Decidable A`.

Both source presentations of strict comparison remain ordinary computable
definitions. Their direct agreement and their positive/negative Boolean
observations are required separately. The plan retains both arguments in
the quantified Nat decision interface and the actual inequality directions
in the source's occasionally misleading declaration names.

## Sorting and the checker consumer

Direct inspection of the pinned Mathlib list sort confirms the source
recurrence: insertion stops at the first successful comparison and places
the new element before that head; the sorter is the corresponding right
fold. The plan requires operation equality on every input before consuming
accepted Sort laws. Sortedness is a theorem premise, not an execution
precondition. The Nat source's nil/singleton/adjacent-cons presentation is
retained through an explicit accepted sortedness equivalence.

The insertion exercise still exposes the proof-carrying decision branch.
Its negative evidence is precisely the negation of the tested non-strict
comparison. The source prose incorrectly negates the strict comparison;
the plan records and corrects that typo. Generic decidability is not treated
as supplying totality, transitivity or reflexivity. The inspected Mathlib
sortedness proofs have genuine totality/transitivity requirements, while
their permutation facts do not depend on those order laws.

The proposed ordering-checker consumer matches the actual project API.
`reference_correct` needs the Boolean comparator law; `adjacent_correct`
characterizes IsChain without transitivity. Refinement to Pairwise and the
composed checked-length consumer require `IsTrans`, exactly as the plan says.
For the source Nat sorter these hypotheses are available. The promised
`some xs.length` result follows only after the source operation bridge,
sortedness and length/permutation facts, so the example is a real client of
the chapter's interfaces. No output equation is presented as a cost proof.

## Scoped assumptions, opacity and execution

The plan's maximum correctly branches on a supplied decision, returning the
second operand on a true strict comparison and the first otherwise. For the
3/7 case, its proof may use the decision's branch evidence for every supplied
decision even when the parameter has no reducible Boolean value. A subsequent
Nat instance supplies the concrete computational realization. This retains
the source distinction between a provable result and a chosen reduction.

The bare excluded-middle parameter is proposition-valued; it is not passed
off as executable branch data. The plan also corrects the source's assertion
that Or is not inductive. Its proposed lesson concerns the restriction on
general elimination from proof data into Nat, while retaining the separate
rules for False and permitted singleton elimination.

Actual `Classical.propDecidable` is a noncomputable scoped instance using
choice. The plan does not substitute it for constructive Nat or list
operations. The source relative-consistency discussion is not converted into
a new axiom or an unsupported formal metatheorem.

The source's opaque Set-valued reflection derivation can block the displayed
Rocq reduction. The chosen Lean Bool/proof packaging has different behavior,
which the plan explicitly requires implementation to demonstrate. It does
not assert that opaque Lean declarations with bodies are universally
unexecutable. Any optional expected-failure or opaque-value demonstration
must record actual observed behavior; no diagnostic is fabricated here.

## List decisions and related existing clients

The inspected core Nat equality and order decisions are constructive. The
list equality implementation compares corresponding positions and length.
The actual list membership instance consumes BEq plus LawfulBEq, with the
standard constructive DecidableEq path supplying the lawful instance. The
plan preserves that law boundary rather than trusting arbitrary Boolean
equality.

The exact source lists give the intended false/true equality outcomes and
the present-key membership result. Absence and empty-list checks expose the
negative branch. Membership does not produce an index or count occurrences;
the permutation-but-unequal list example retains this distinction. The
membership result must be a kernel-checked theorem in addition to any
evaluator display.

The optional language client also matches actual providers. Regex membership
uses a proved recognizer iff and `decidable_of_iff`, with DecidableEq on the
alphabet. The separate parser Decision carries an actual Type-valued witness
or its refutation, and its test characterizes Nonempty. The plan does not
erase those witnesses or replace ordinary proposition decisions with the
parser's more informative type.

## Identities, findings and disposition

All **19 hashes** in the frozen identity table match the actual named files,
including the five core files read from the pinned installed toolchain.
Consequential source types and bodies were inspected directly. All reads and
bookkeeping checks are source evidence, not new elaboration, native execution
or axiom-audit evidence.

| ID | Status | Finding |
| --- | --- | --- |
| — | None | No actionable omission, false provider claim, weakened source requirement, unjustified extra premise or unsupported completion claim found. |

The frozen plan is clear as preparation. Acceptance still requires the actual
accepted #1015 baseline, integrated source coverage, checked computations and
consumers, stable isolated candidate validation and exhaustive audit, both
independent implementation review axes and final candidate verification.
No ticket is closed by this review.

Only this review file was written. No compiler, proof, algorithm, benchmark,
cache/configuration/checkout/tracker/GitHub mutation or chapter acceptance
was performed. Root retains all gate and durability-checkpoint ownership.
