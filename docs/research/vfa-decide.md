# VFA Decide: proof-carrying decisions and their computation

This is the implementation correspondence for CTB-18, continued by CTB-98
after secured checkpoint046. The mathematical owner is
[Examples/DecisionProcedures.lean](../../Examples/DecisionProcedures.lean).
It reuses the accepted comparison, insertion-sort and ordering-checker owners;
it does not introduce another decision class or sorting library.

**Current status: CONTENT candidate, acceptance pending.** This note maps the
complete source scope to the actual implementation and separately records
observed chapter probes and core-only computational fixtures. It does not claim source
qualification, independent review approval, a whole-library receipt or receiving
integration acceptance. The probe identities below record actual runs; the
continuing CTB/coverage owners record subsequent candidate validation and review.

## Source identity and scope

The primary is the complete VFA 2.1 `Decide.v`, release cover
`2026-08-24 10:11`, chapter footer `2026-08-24 09:43`. The versioned source is
[Decide](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Decide.html), obtained
from the authenticated release archive. The exact source and complete
[canonical plan](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1016-Decide.md)
were read. The existing [VFA MIT notice](../licenses/vfa-MIT.txt) preserves
source attribution; downloaded primary bodies remain external.

| Input | Identity |
|---|---|
| VFA 2.1 archive | SHA-256 `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8` |
| `Decide.v` | 19,701 bytes, 506 lines; SHA-256 `f929d55e2b7b39f2ba0bb72f2e70285dc8e10e64cf18322060bdbfc0552a4b26` |
| Canonical `1016-Decide.md` | 31,410 bytes; SHA-256 `ca2a19ddf844a90d8647fe4209fe0ea4302de6578df90541b5a2b143ad9b94e0` |
| Source inventory | 32 records, two standard exercises, 15 pedagogical commands, two scratchpad modules |

The 32 lexical records comprise 17 definitions, eight source-proved records,
one transparently proved definition, three admissions, two pedagogical global
assumptions and one abandoned computation proof. Their dispositions below
retain those distinctions. An admitted source declaration becomes a proved
or constructively implemented obligation; a source assumption becomes a scoped
parameter with an explicit Nat realization; the abandoned Rocq computation
requires an accurate explanation and the actual Lean computation, not a new
false theorem or a fabricated Lean failure.

## Actual owners and representation boundaries

The new module imports
[Examples.ComparisonPermutations](../../Examples/ComparisonPermutations.lean)
and [Examples.InsertionSorting](../../Examples/InsertionSorting.lean). Through
these existing owners it uses
[OrderCertificate](../../Applications/Checking/OrderCertificate.lean), the
standard list operations and their semantic contracts. Its public namespace is
`Examples.DecisionProcedures`, with `ScratchPad` and `ScratchPad2` subnamespaces.

The pinned Lean 4.35.0 representation matters. `Decidable P : Type` is a class
with constructor `Decidable.intro`, a field `decide : Bool`, and a proof field
`reflects_decide : decide.Reflects P`. `Bool.Reflects : Bool → Prop → Prop`
reduces to `P` at true and `¬ P` at false. `Decidable.isTrue` and
`Decidable.isFalse` are match-pattern abbreviations, with
`Decidable.falseTrueCases` providing the familiar case interface; they are not
the underlying two constructors of this pinned class. The source's
`reflect P b : Set` therefore has a different sort and packaging from the
native Bool/proof interface.

For arbitrary propositions `A` and `B`,
`Examples.DecisionProcedures.ScratchPad.ProofSum A B` is exactly
`Sum (PLift A) (PLift B)`. Its two tags remain computational data even when both
propositions hold. The source's generic proof sum cannot be replaced by
`Decidable A`, because its right branch need not assert `¬ A`. Only the
specialization `ProofSum P (¬ P)` is connected to `Decidable P`, by the two
explicit maps `proofSumToDecidable` and `decidableToProofSum`, both round trips,
and the two tag/Bool equations. Proof irrelevance identifies proof payloads
inside a fixed tag; it does not equate the left and right tags.

The strict and non-strict Bool laws are the existing
`Examples.ComparisonPermutations.ltb_reflect` and `leb_reflect`.
`Examples.ComparisonPermutations.reflectedLt` already calls
`decidable_of_bool (decide (a < b)) (ltb_reflect a b)`. Both new strict-decision
presentations use that same provider; their equality is definitional and their
Bool projections have separate equations. This preserves the chosen
computation without using decision subsingletonhood as an execution argument.

## All 32 source records, in inventory order

Every row names an actual declaration in the current module. Supplemental
declarations described later establish the round trips, branch observations,
edge cases and connected checker consumer. These are implementation
correspondences, not assertions that the acceptance gates have passed.

| Exact source ID | Actual Lean declaration and disposition |
|---|---|
| `Decide.goal_at_line_63@63` | `Examples.DecisionProcedures.three_lt_seven_bool`: `decide ((3 : Nat) < 7) = true`, by kernel computation. |
| `Decide.three_less_seven_1@73` | `Examples.DecisionProcedures.three_lt_seven_cases`: inspect the selected `reflectedLt 3 7` decision; its false Bool contradicts the independently calculated true result, while its true branch supplies the proof. |
| `Decide.three_less_seven_2@89` | `Examples.DecisionProcedures.three_lt_seven_reflection`: directly consume the accepted decision's true reflection field. This retains the second proof method. |
| `Decide.ScratchPad.sumbool@121` | `Examples.DecisionProcedures.ScratchPad.ProofSum`, with `Examples.DecisionProcedures.ScratchPad.proofSumTag`: alias existing `Sum (PLift A) (PLift B)` for arbitrary propositions, keeping both data tags. |
| `Decide.ScratchPad.t1@127` | `Examples.DecisionProcedures.ScratchPad.T1`: the two true propositions are `3 < 7` and `2 < 3`, the latter being the source's `3 > 2`. |
| `Decide.ScratchPad.less37@128` | `Examples.DecisionProcedures.ScratchPad.less_three_seven`: the reflected proof of `3 < 7` used in the left payload. |
| `Decide.ScratchPad.greater23@129` | `Examples.DecisionProcedures.ScratchPad.greater_three_two`: proves `2 < 3`; the source name does not reverse its actual `3 > 2` statement. |
| `Decide.ScratchPad.v1a@131` | `Examples.DecisionProcedures.ScratchPad.v1a`: left-tagged `T1`; `Examples.DecisionProcedures.ScratchPad.v1a_tag` observes true. |
| `Decide.ScratchPad.v1b@132` | `Examples.DecisionProcedures.ScratchPad.v1b`: right-tagged `T1`; `Examples.DecisionProcedures.ScratchPad.v1b_tag` observes false, and `Examples.DecisionProcedures.ScratchPad.v1a_ne_v1b` separates the tags although both propositions hold. |
| `Decide.ScratchPad.t2@140` | `Examples.DecisionProcedures.ScratchPad.T2`: right proposition `3 < 2`, exactly the source's false `2 > 3`. |
| `Decide.ScratchPad.v2a@141` | `Examples.DecisionProcedures.ScratchPad.v2a`; `Examples.DecisionProcedures.ScratchPad.t2_eq_v2a` eliminates an impossible right payload and proves every inhabitant equals this left value; `Examples.DecisionProcedures.ScratchPad.t2_tag` observes true. |
| `Decide.ScratchPad.t4@157` | `Examples.DecisionProcedures.ScratchPad.T4`: `∀ a b : Nat, Decidable (a < b)`. The explicit proof-sum/decision adapters justify this proposition/negation specialization while retaining both quantified Nat arguments. |
| `Decide.ScratchPad.v3@165` | `Examples.DecisionProcedures.ScratchPad.v3`: left-tagged proof sum for `3 < 7` versus its negation; `Examples.DecisionProcedures.ScratchPad.v3_decision` identifies its adapter result with the actual strict decision. |
| `Decide.ScratchPad.is_3_less_7@167` | `Examples.DecisionProcedures.ScratchPad.isThreeLtSeven` and `Examples.DecisionProcedures.ScratchPad.isThreeLtSeven_eq_true`: observe the source data tag and prove true. |
| `Decide.ScratchPad.lt_dec@192` | `Examples.DecisionProcedures.ScratchPad.ltDecision`: ordinary expression definition reusing the accepted reflected Nat decision. |
| `Decide.ScratchPad.lt_dec'@201` | `Examples.DecisionProcedures.ScratchPad.ltDecision'`: ordinary definition constructed through proof/term elaboration with the same provider; it is not an opaque theorem returning data. |
| `Decide.ScratchPad.lt_dec_equivalent@208` | `Examples.DecisionProcedures.ScratchPad.ltDecision_eq_ltDecision'`: definitional equality for every `a b`, supplemented by both projection laws and separate true/false examples for each presentation. |
| `Decide.ScratchPad2.lt_dec@232` | `Examples.DecisionProcedures.ScratchPad2.ltDecision`: namespace alias of the earlier standard decision; no second reflected-decision implementation. |
| `Decide.ScratchPad2.le_dec@238` | `Examples.DecisionProcedures.ScratchPad2.leDecision`: existing Bool adapter with accepted `leb_reflect`; `Examples.DecisionProcedures.ScratchPad2.leDecision_decide` preserves the supplied Bool, and the true/false iff laws expose the exact branch propositions. |
| `Decide.ScratchPad2.insert@247` | `Examples.DecisionProcedures.ScratchPad2.insert`: source recurrence with a local instance supplied by `leDecision`; `Examples.DecisionProcedures.ScratchPad2.insert_eq_source` identifies the actual operation with accepted insertion on every input. |
| `Decide.ScratchPad2.sort@253` | `Examples.DecisionProcedures.ScratchPad2.sort`: tail-first sort followed by the actual decision-based insertion; `Examples.DecisionProcedures.ScratchPad2.sort_eq_source` gives the all-input accepted-operation bridge. |
| `Decide.ScratchPad2.sorted@259` | `Examples.DecisionProcedures.ScratchPad2.Sorted`: accepted Nat `IsChain (· ≤ ·)` interface, with `Examples.DecisionProcedures.ScratchPad2.sorted_nil`, `sorted_singleton` and `sorted_cons_iff` exposing the source's nil/singleton/adjacent-cons cases. |
| `Decide.ScratchPad2.insert_sorted@268` | `Examples.DecisionProcedures.ScratchPad2.insert_sorted`: complete preservation theorem via the operation bridge and accepted proof; `Examples.DecisionProcedures.ScratchPad2.insert_sorted_decision_cases` explicitly consumes both proof-carrying branches. The source admission is not retained. |
| `Decide.ScratchPad2.lt_dec_axiom_1@328` | `Examples.DecisionProcedures.ScratchPad2.NatLtCases`: ordinary proposition-parameter type; `Examples.DecisionProcedures.ScratchPad2.nat_lt_cases` supplies a constructive Nat witness and `Examples.DecisionProcedures.ScratchPad2.nat_lt_cases_use` consumes a supplied witness within Prop. No global source axiom is added. |
| `Decide.ScratchPad2.lt_dec_axiom_2@341` | `Examples.DecisionProcedures.ScratchPad2.NatLtDecision`: separate data-parameter type; `Examples.DecisionProcedures.ScratchPad2.natLtDecision` is the constructive `Nat.decLt` realization. No global source axiom is added. |
| `Decide.ScratchPad2.max_with_axiom@343` | `Examples.DecisionProcedures.ScratchPad2.maxWithDecision`: selects `j` when the supplied `d i j` Bool is true and `i` otherwise; `Examples.DecisionProcedures.ScratchPad2.maxWithDecision_eq_max` proves the generic maximum law using the supplied decision's evidence. |
| `Decide.ScratchPad2.prove_with_max_axiom@359` | `Examples.DecisionProcedures.ScratchPad2.maxWithDecision_three_seven`: result 7 for every valid supplied decision, distinguished from reduction before a computational implementation is supplied. |
| `Decide.compute_with_lt_dec@388` | `Examples.DecisionProcedures.ScratchPad2.compute_with_reflected_decision`: the actual Lean reflected adapter computes to 7. The abandoned Rocq proof is explained by its Set-valued opaque reflection path; the separate observed Bool/opaque-Prop-proof fixture documents the different Lean behavior. |
| `Decide.compute_with_StdLib_lt_dec@407` | `Examples.DecisionProcedures.ScratchPad2.compute_with_standard_decision`: closed kernel-checked result 7 from constructive `Nat.decLt`; concrete/reversed/equal maximum cases provide connected boundaries. |
| `Decide.list_nat_eq_dec@450` | `Examples.DecisionProcedures.listNatEqDecision`: synthesize the standard constructive list-of-Nat equality decision; `Examples.DecisionProcedures.listNatEqDecision_correct` states its positional equality meaning. |
| `Decide.list_nat_in@464` | `Examples.DecisionProcedures.listNatIn`: standard constructive Nat list-membership decision, with `Examples.DecisionProcedures.listNatIn_correct` and `listNatIn_false_iff`; no replacement search algorithm or source admission. |
| `Decide.in_4_pi@467` | `Examples.DecisionProcedures.in_four_pi`: kernel-checked true result on the exact source list; `Examples.DecisionProcedures.four_mem_pi` consumes its correctness law. The source admission is discharged in the implementation. |

## Both exercises and both namespaces

| Exercise | Implementation and retained lesson |
|---|---|
| `insert_sorted_le_dec`, source 267–285; two stars, standard | `Examples.DecisionProcedures.ScratchPad2.insert_sorted` preserves the accepted sortedness of the actual inserted list. `insert_sorted_decision_cases` matches `leDecision a h`; the true branch receives `a ≤ h` and uses `insert_sorted_true_branch`, while the false branch receives `¬ a ≤ h` and uses `insert_sorted_false_branch`. The latter specializes the reused general insertion theorem to the selected recursive output; it is not presented as an independent reconstruction of the full sorting proof. |
| `list_nat_in`, source 460–472; two stars, standard | `Examples.DecisionProcedures.listNatIn` uses standard membership decidability. `in_four_pi` checks the exact source computation; `four_mem_pi` derives membership through its law. `absent_from_pi`, `eight_not_mem_pi`, `listNatIn_nil` and `listNatIn_duplicate` preserve negative, empty and repeated-value boundaries. |

Neither exercise is optional or advanced. The first source exercise has one
admitted theorem; the second contains the admitted function and admitted
example, giving all three source admissions accounted for.

| Source module | Lean scope and distinction |
|---|---|
| `ScratchPad`, line 108 | `Examples.DecisionProcedures.ScratchPad`: generic lifted proof sums, observable tags, proposition/negation adapters and two strict-decision definitions. |
| `ScratchPad2`, line 224 | `Examples.DecisionProcedures.ScratchPad2`: standard decision presentation, decision-based sorting, scoped assumption interfaces and maximum/computation examples. |

Source notation, implicit arguments, `Locate`, `End`, warnings and imports are
language presentations. Lean namespaces and existing providers preserve their
purpose; they do not claim Rocq module sealing or reproduce its notation engine.

## All 15 pedagogical commands

The following are the concrete source-command adaptations. The chapter-wide
`#check`/`#print`/`#reduce`/`#eval` probe ran successfully on the preliminary
immutable content candidate identified below. Core-only observations
are separately identified in the computational section below. The
source's incidental `Search` listing is a library-discovery lesson, not a
requirement to reimplement every listed standard-library function.

| Source command | Lean inspection or computation and its meaning |
|---|---|
| `Check`, line 13 | `#check Nat.lt`: the proposition-valued Nat comparison interface. |
| `Check`, line 14 | `#check (fun a b : Nat => decide (a < b))`: the constructive Bool presentation used by the actual accepted reflection adapter. |
| `Print`, line 21 | `#print Bool.Reflects` and `#print Decidable`: retain the source Set versus native Prop distinction and the actual Bool/proof fields. |
| `Check`, line 26 | `#check Examples.ComparisonPermutations.ltb_reflect`: the existing `(decide (a < b) = true) ↔ a < b` correctness law. |
| `Eval`, line 173 | `#eval Examples.DecisionProcedures.ScratchPad.isThreeLtSeven`; expected true, with the independent kernel theorem `isThreeLtSeven_eq_true`. |
| `Print`, line 175 | `#print Examples.DecisionProcedures.ScratchPad.T4`: both Nat arguments remain quantified in the constructive decision interface. |
| `Check`, line 188 | `#check Examples.ComparisonPermutations.ltb_reflect`, together with `#check Examples.ComparisonPermutations.reflectedLt`: inspect the law and the actual Bool-to-decision provider consumed by `ltDecision`. |
| `Print`, line 205 | `#print Examples.DecisionProcedures.ScratchPad.ltDecision`: ordinary term-defined provider. |
| `Print`, line 206 | `#print Examples.DecisionProcedures.ScratchPad.ltDecision'` and `#check Examples.DecisionProcedures.ScratchPad.ltDecision_eq_ltDecision'`: the proof-elaborated definition and its actual equality. |
| `Locate`, line 225 | `#check @Decidable.intro`, `#check @Sum.inl`, `#check @PLift.up`, and the concrete `ProofSum` alias identify native decision and generic proof-sum providers without claiming a Coq name exists in Lean. |
| `Print`, line 226 | `#print Decidable`, `#print Decidable.isTrue`, `#print Decidable.isFalse`, and `#check @Decidable.falseTrueCases`: distinguish the actual constructor/fields from case-pattern abbreviations. |
| `Eval`, line 352 | `#reduce Examples.DecisionProcedures.ScratchPad2.maxWithDecision`: display the open decision projection before supplying `d`. Closed evaluation must first instantiate `natLtDecision`; the theorem for every `d` remains a separate result. |
| `Search`, line 418 | Inspect `Nat.decEq`, `Nat.decLe`, `Nat.decLt`, `decidable_of_bool`, `decidable_of_iff`, the inferred `DecidableEq (List Nat)`, and `Examples.DecisionProcedures.listNatIn`. These show the relevant native comparison/list composition interfaces. |
| `Eval`, line 454 | `#eval (Examples.DecisionProcedures.listNatEqDecision [1, 3, 4] [1, 4, 3]).decide`; expected false, with `Examples.DecisionProcedures.lists_unequal`. |
| `Eval`, line 457 | `#eval (Examples.DecisionProcedures.listNatEqDecision [1, 3, 4] [1, 3, 4]).decide`; expected true, with `Examples.DecisionProcedures.lists_equal`. |

## Decisions, actual insertion, and a connected checker consumer

The insertion implementation installs the particular constructive
`leDecision x h` as the local decision instance. Its actual recurrence returns
`[x]` on nil; on `h :: t`, true returns `x :: h :: t` and false returns
`h :: insert x t`. Sorting first sorts the tail and then inserts its former
head. `insert_eq_source` and `sort_eq_source` quantify over **every** list,
without a sorted-input condition. They connect these actual recursions to
`Examples.InsertionSorting.insert` and `sort`, which are the accepted standard
ordered insertion and insertion sort.

`Sorted` is the accepted Nat adjacent-chain predicate. Its nil, singleton and
adjacent-cons interfaces are exposed explicitly. `insert_sorted` requires a
sorted input; `sort_sorted` does not. `sort_perm` preserves all occurrences,
and `sort_length` follows from that permutation. The concrete expected
calculation `[3, 1, 2, 1] ↦ [1, 1, 2, 3]` is connected to those same generic
contracts by `sort_calculation_contract`.

The exact source false-branch correction is encoded in
`leDecision_false_iff` and `insert_sorted_false_branch`: the tested proposition
is `a ≤ h`, so its false evidence is **`¬ a ≤ h`**, not `¬ a < h` as the
source's nearby prose says. Equal endpoints select the true branch. The
all-input recurrence and `insert_ties_before_head` retain insertion before
an equal head. Because these entries are Nat values, that concrete equal-value
list alone is not a tagged-record stability theorem. No new stability or
runtime-cost equivalence is inferred from it.

`unsorted_insert_boundary` checks `insert 1 [2, 0] = [1, 2, 0]` and proves
that result is not sorted. It separates the unconditional operation bridge
from the conditional insertion-preservation theorem. Mere decidability would
not establish sortedness for an arbitrary relation; these are concrete Nat
specializations using the accepted order laws.

`Examples.DecisionProcedures.sort_adjacent_checked` feeds the actual sorted
result to the independently implemented `OrderCertificate.adjacent` and
consumes `adjacent_correct` with the accepted `leb_reflect`. This adjacency
contract describes `IsChain` without requiring transitivity. The stronger
`Examples.DecisionProcedures.sorted_checkedLengthSquare` uses
`OrderCertificate.checkedLengthSquare_correct` and the Nat chain/pairwise bridge;
the underlying generic consumer requires `IsTrans`, supplied here by Nat's
non-strict order. The proved result is exactly

```lean
(OrderCertificate.checkedLengthSquare
    Examples.ComparisonPermutations.leb_reflect).impl
    (Examples.DecisionProcedures.ScratchPad2.sort xs) = some xs.length
```

Length is justified by the real permutation theorem, not assumed as a separate
execution postcondition. `sort_checked_calculation` yields `some 4` on the
duplicate-rich source-facing example, and `empty_checked` yields `some 0`.
This is the chapter's cross-application consumer. The canonical plan's optional
language-recognizer client is not newly implemented; no parser or witness
erasure claim is needed for this ordering-checker composition.

## Scoped assumptions, maximum, equality and membership

`NatLtCases : Prop` is the source proposition-valued interface
`∀ i j : Nat, i < j ∨ ¬ i < j`. `NatLtDecision` is the distinct data-valued
interface `∀ i j : Nat, Decidable (i < j)`. They are parameter types, not
global axioms. The constructive `nat_lt_cases` proves the first using Nat
comparison, while `natLtDecision` explicitly selects `Nat.decLt` for the
second. `nat_lt_cases_use` simply consumes a supplied proof within Prop; it
does not extract a computational branch from Or.

`maxWithDecision` takes its decision explicitly and retains the source's
orientation: true means `i < j` and returns `j`; false means `¬ i < j` and
returns `i`. `maxWithDecision_eq_max` consumes those branch proofs to establish
agreement with Nat maximum for every valid supplied decision. Consequently
`maxWithDecision_three_seven` proves 7 for every `d`, even though reduction of
the open term cannot inspect a concrete Bool yet. `maxWithDecision_concrete`,
`maxWithDecision_reverse` and `maxWithDecision_equal` cover the selected
constructive realization at true, false and equal endpoints. Logical knowledge
of a result is not the same observation as reducing an uninstantiated program.

The chapter's list decisions reuse standard constructive equality and
membership for Nat. Equality compares positions and lengths: `lists_unequal`
and `lists_equal` preserve the two exact source calculations.
`permuted_but_unequal` additionally proves that `[1, 3, 4]` and `[1, 4, 3]` are
a permutation but unequal lists. Neither equality decision nor membership
is substituted for occurrence counting.

Membership uses the exact source list `[3, 1, 4, 1, 5, 9, 2, 6]`: 4 is
present and 8 absent, and all Nat inputs are absent from nil. The positive and
negative correctness laws turn actual decision observations into `∈` and `∉`.
`listNatIn_duplicate` proves that duplicating a head leaves the Bool unchanged,
matching propositional membership rather than multiplicity. This interface
returns neither an index nor a proof-relevant parse witness. Its concrete
standard Nat equality has the required lawful behavior; an arbitrary `BEq`
without a correctness law would not justify the same mathematical claim.

## Actual elimination and opacity evidence

Three core-only fixtures were actually run with pinned Lean 4.35.0, compiler
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, through the existing native profile.
They imported only `Init`, used `lean -EhasSorry`, requested no `.olean`, and
produced no `.olean` output. The original commands and stream identities were
recorded in external checkpoint047 evidence. The filenames and hashes below
preserve that historical attribution without asserting present raw-file
availability; the meaningful observation and opacity distinctions are here.

| Fixture identity | Observed result |
|---|---|
| `DecideOrToNatRejected.lean`, 420 bytes; SHA-256 `dc5b0454e3e647117dc80e62638e9d8e2fc6c7d14589927b1effb77d04c9a8e1` | Exit 1, expected: `nested.lean.propRecLargeElim`; `Or.casesOn` can only eliminate into `Prop`. |
| `DecidePermittedElimination.lean`, 632 bytes; SHA-256 `4286b11334874d0ccda1b836b0de08354962a10a01a52cf017ccc8e30c2331f3` | Exit 0: False and True elimination to Nat typecheck; the True case is proved by `rfl`, reduces to 7 and evaluates to 7. |
| `DecideOpacity.lean`, 1,666 bytes; SHA-256 `2b9114ba0036d6e1666b115088ccf6e5acbb25f75492d897ef3605c76ec12112` | Exit 0: Bool/maximum equations with an opaque Prop correctness theorem are proved by `rfl`; `#reduce` and `#eval` give true/7. Open-parameter and opaque-data observations are distinct below. |

The exact rejected lesson is this attempted definition, retained only in the
external negative fixture:

```lean
def maxFromProposition
    (h : ∀ i j : Nat, i < j ∨ ¬ i < j) (i j : Nat) : Nat :=
  match h i j with
  | Or.inl _ => j
  | Or.inr _ => i
```

Or **is inductive**. Its recursor restricts the target motive to Prop, which
explains this rejection. The positive fixture separately defines
`fromFalse (h : False) : Nat := False.elim h` and a match on `True.intro`
returning 7. Printed `False.rec` and `True.rec` have Sort-valued motives,
whereas `Or.rec` has a Prop-valued motive. No False inhabitant is provided or
executed. Thus the observation is not a claim that every Prop-to-data
elimination is forbidden, nor an impossibility claim about defining Nat maximum.

The opacity fixture uses an ordinary opaque theorem
`opaqueComparisonLaw : (true : Bool) ↔ (3 < 7)` and the actual provider:

```lean
def decisionFromOpaqueProof : Decidable (3 < 7) :=
  decidable_of_bool true opaqueComparisonLaw

def maximumFromOpaqueProof : Nat :=
  @ite Nat (3 < 7) decisionFromOpaqueProof 7 3

theorem opaqueProof_decide : decisionFromOpaqueProof.decide = true := rfl
theorem opaqueProof_maximum : maximumFromOpaqueProof = 7 := rfl
```

Both equations checked, and separate kernel reduction and evaluation commands
returned true/7. The actual pinned `decidable_of_bool` stores the supplied Bool
directly; the opaque theorem occurs in the Prop proof field. The source's
abandoned proof branches through a Set-valued reflection derivation whose
Rocq opacity blocks its computation. Its obstruction does not require the
corresponding Lean Bool projection to fail. The main module independently
retains `compute_with_reflected_decision` and
`compute_with_standard_decision` as kernel theorems for its actual providers.

The successful fixture also prints the reduction of an uninstantiated
decision-based maximum. It retains `Bool.rec` on `(d i j).1`, with false and
true branches returning `i` and `j`. No failing `#eval` of an open parameter
was invented. A separate one-line computational declaration
`opaque opaqueNumber : Nat := 7` remains `opaqueNumber` under `#reduce`, but
returns 7 under `#eval`. Opaque computational data and an opaque Prop proof
field are different, and an opaque declaration with a body is not universally
unexecutable.

The positive fixtures' six printed named axiom inspections reported no axioms;
that observation concerns only those named fixture declarations and does not
replace the project audit. Core source inspection also confirms the provider's
warning that iff-based decision transport avoids the kernel obstruction that
can arise from rewriting computational data through `propext`. That latter
rewriting behavior was not separately tested here.

The historical external observation record was `computational-evidence.json`,
9,280 bytes, SHA-256
`9eab90faea48f37afbc60b8215b9f58e62757b0f23ca8e19ece594ac1c8b071a`.
Its interpretation note is 5,735 bytes, SHA-256
`c79190228e329e3f6ba385eb68da31842b0df41df3a0d97e59c2cacfc6b3cdf9`.
These identities preserve attribution to the original fixture runs. They do
not assert that the old raw files are available at a current source path.
The substantive elimination/opacity cases and their assumptions are retained
above and in the corresponding fixture/source owners. [CTB-98](../textbooks/CTB.json)
owns their historical qualification; CTB-78 receiving validation remains separate.
Six named inspections neither replace the project audit nor establish a current pass.

## Complete substantive prose disposition

| Source span | Treatment and boundary |
|---|---|
| 3–26 | Source warnings/import names become ordinary Lean imports; Prop versus Bool and the actual reflection interfaces are described above. Reuse accepted Perm reflection rather than reproduce `bdestruct` as a new tactic. |
| 28–53 | Computational-reflection motivation and the source's historical references remain context. The concrete bridge relates existing Nat decisions to propositions; no universal reflection engine, metatheory of consistency or new undecidability formalization is claimed. |
| 55–103 | Preserve the closed true Bool result and both proof methods, including the impossible false branch and direct true-field consumption. `reflectedLt_reverse` and `reflectedLt_equal` provide false and equal-endpoint cases. |
| 110–213 | Generic proof sums retain arbitrary A/B, two observable tags, the both-true example, an impossible right branch, both Nat arguments, two decision definitions and their equality. Round-trip/tag adapters connect only the proposition/negation specialization. |
| 216–242 | Standard namespace and implicit-argument presentation use native providers. The source's computability warning is interpreted through the actual Lean Bool/proof separation, not copied as a claim that the new adapter is noncomputable. |
| 244–284 | Preserve the exact non-strict insertion and tail-first sorting recurrences and complete the preservation exercise through accepted operations. The false hypothesis is `¬ a ≤ x`; the source's `¬ a < x` prose is corrected. |
| 290–325 | Distinguish computable decision data from logical excluded-middle evidence. Contextual halting/normal-form discussion is not an implementation of a universal decider. Logical classical decidability, where available, is not used as an executable realization of the concrete Nat/list examples. |
| 328–371 | Both pedagogical assumptions are scoped interfaces with constructive Nat realizations. Preserve the exact maximum branch order and proof-versus-reduction distinction. Correct the assertion that Or is not inductive using the observed elimination boundary and its positive exceptions. Source relative-consistency remarks remain context, not a consistency theorem established here. |
| 377–411 | Account for the abandoned Rocq opaque-reflection computation, successful actual Lean Bool/proof computation, and constructive standard Nat result. Opaque proof fields, open data parameters and opaque computational data have separate observations. |
| 413–458 | Relevant native comparison and list-decision composition replaces incidental search output. Positional list equality retains the two exact results and is separated from permutation. |
| 460–476 | Complete membership construction and exact source sanity check, including absent and empty cases. Standard decidability composition is reused without creating another calculus or returning an index/witness the interface does not promise. |
| 480–504 | Explain Boolean-plus-law and proof-carrying decision tradeoffs. In this Lean version the native decision already packages a Bool and proof; fewer surface interfaces do not imply a universal speed, allocation or efficiency advantage. |

## Validation and acceptance boundary

The preliminary immutable content candidate
`f26213ba1930040701952e02d31b1713660431f2` built in the retained isolated
acceptance checkout with the pinned native profile, using
`lake --no-cache --rehash build +Examples.DecisionProcedures`: exit 0,
944 jobs. Its mathematical owner is 14,195 bytes, SHA-256
`a138634cdcbfca4e8432b8c03f6bf11abcdd059e7036a4844a0b84ea39958a38`.
Subsequent text changes to this note do not change that mathematical source.

Two independent probe inputs then ran through `lake env lean -EhasSorry`,
each exiting 0 without requesting an output object. The statement probe
printed all 100 explicitly authored declarations: 75 theorems and 25
definitions/aliases. Root inspected their elaborated types together with
their bodies, the accepted predecessor definitions and their concrete uses.
The assessment checked arbitrary A/B proof sums and both tags; both adapter
round trips; exact strict/non-strict branch evidence; unconditional operation
bridges versus conditional insertion preservation; scoped constructive
parameters; positional equality and propositional membership; and the actual
checker consumer with Nat transitivity and permutation-derived length.
The standard pretty-printer elides decision-instance details in several
`decide` expressions; the source bodies and printed provider definitions
retain the chosen instances, so those displayed equalities are not used alone
as an execution argument. The external complete assessment lists every
authored declaration. Private/generated logical declarations belong to the
separate exhaustive imported-project audit.

| Actual probe | Input SHA-256 | Output SHA-256 |
|---|---|---|
| `Statements.lean`, 6,107 bytes; output 16,875 bytes | `a2c8573d9ab5656368ae634654b9051d6d3027cbcf75a55744d48ce83e7b8caa` | `025bbc741453ebf21a3d8d27bc0a98bff295f3baa91efab3cc1ba3d27c162d72` |
| `ChapterCommands.lean`, 2,191 bytes; output 2,815 bytes | `d8033c70ae085c97131892a4869833de8bf378f02bb5acad2f4cb4cdfb8fe3c6` | `dc86cb11a6088b1bd1f437379e220c19d74fb3311201248d936cdf4cd6f1dda2` |

The command output displays the pinned Bool/proof class, both identical
strict-decision bodies, lifted sums, the pattern abbreviations and actual
Nat/list providers. Its open maximum retains a `Bool.rec` branch on
`(d 3 7).1`. Actual evaluator results were: source tag true; unequal/equal
lists false/true; present/absent/empty membership true/false/false;
both-true proof-sum tags true/false; sorted output `[1, 1, 2, 3]`; checked
length `some 4`; reflected reduction/evaluation 7/7; and concrete maximum
results 7, 7 and 3 on `(3,7)`, `(7,3)` and `(3,3)`. These agree with the
independently expected cases and the separate kernel theorems.

The final content candidate must still pass the guarded focused build/audit,
public-source coverage and both independent Standards/Spec CONTENT axes.
Exact-candidate receipts and review outcomes are retained by the continuing
coordinator and qualification owners after their actual checks. These
preliminary observations do not assert those outcomes in advance.

The chapter supplies no quantitative complexity theorem for these adapters.
Equal outputs and all-input operation bridges do not establish equality of
comparison observations, physical allocation, sharing, collection, stack use
or wall-clock time. Kernel equations, kernel reduction, `#eval`, proof-audit
results and measured native performance are distinct forms of evidence.
Native implementation overrides are not verified merely by a mathematical
decision law, and no new timing experiment is reported here.

After actual CONTENT acceptance, qualification must be derived in the continuing
CTB/coverage owners; final artifact review, exact archive reconstruction, final
live verification and durable publication remain separate gates. Color begins
only after the required secured checkpoint. Every remaining FDSA/PFDS chapter
and appendix and the delegated receiving whole-library/quality assessment
remain part of the continuing work.
