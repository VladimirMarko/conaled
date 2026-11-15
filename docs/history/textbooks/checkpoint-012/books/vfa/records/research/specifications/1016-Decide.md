# Local #1016 — VFA Decide: requirements and reuse plan

**Planning only. Implementation is blocked until #1015 Binom is accepted.**
This preparation adds no Lean definition, algorithm, compiler result or chapter
acceptance. Proposed names must be reconciled with the actual accepted
predecessor APIs. The running Preface/Perm candidate is independent of this
plan; its source and validation inputs remain unchanged.

## 1. Source and scope

The complete pinned VFA 2.1 chapter
[Decide](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Decide.html),
`reference/vfa/vfa/Decide.v`, has 506 lines and SHA-256
`f929d55e2b7b39f2ba0bb72f2e70285dc8e10e64cf18322060bdbfc0552a4b26`.
The release cover is `2026-08-24 10:11`; the chapter footer is
`2026-08-24 09:43`. Root read every source line before writing this plan.

The inventory contains 32 records: 17 definitions, eight source-proved
records, one transparently proved definition, three admissions, two
pedagogical global assumptions, and one abandoned computation proof.
Both exercises are standard; neither is optional or advanced. All 15
inventoried pedagogical commands and both scratchpad modules are covered.
The unnamed closed Boolean goal and the admitted membership example remain
substantive obligations.

This chapter teaches interfaces to decision procedures and their computational
behavior. It does not supply an implementation of a universal halting decider,
a formal metatheory of consistency, or a general reflection engine. Its
historical/undecidability discussion is motivating context; the concrete
reflection, decision, sorting, maximum, equality and membership developments
are the formal scope. Do not turn historical prose into unsupported new
theorems or claim that Lean decides arbitrary propositions algorithmically.

Follow `../source/SOURCE-RECOVERY.md` for the exact official archive and its
hash, preserve source attribution, and exclude downloaded research copies
from deliverables under ADR 0001. The pinned source inventory defines scope,
not a later revision of a moving web page.

The inspected project is `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, not an
accepted predecessor baseline. Lean is 4.35.0 at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Mathlib is
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and Batteries is
`66e469188fe07963e5cf666c7d4433f45b8131c5`.

AGENTS, architecture/domain guidance, GLOSSARY, ADRs 0001/0010, implementation
and example-driven-development guidance, README build/audit rules, local
whole-book requirements and the computational/resource source notes apply.
This planning work starts no additional implementation review loop.

## 2. Architecture and exact pinned APIs

Most of the chapter belongs in a bounded Examples module, provisionally
`Examples/DecisionProcedures.lean`, with its explanation and coverage in the
VFA research documentation. Generic Boolean/decision transport and list
instances already exist. Reuse them and the accepted Sort realization; do
not introduce a new decision class, reflection language, sorter hierarchy,
or emulation of Coq's module/opacity system.

Cross-domain composition with an ordering checker or a language recognizer
belongs in Examples. An Applications module must not import the existing
`Examples.ComparisonPermutations` merely to acquire a standard reflection
lemma. A generic fact can use the core adapter directly; source-facing
pedagogy can refer to the accepted Perm example from the new Examples module.

### The installed Decidable representation matters

In this pinned Lean version, `Decidable p` is a **class carrying a Bool**
`decide` and a proof `reflects_decide : decide.Reflects p`. Its actual
constructor is `Decidable.intro`. `Decidable.isFalse` and `isTrue` are
match-pattern abbreviations presenting the familiar false/true cases, with
`falseTrueCases` supplying the standard cases/induction interface. Do not
describe them as the underlying two constructors of this version's class.

`Bool.Reflects` is a Prop-valued abbreviation: at true it reduces to p, and
at false to Not p. It is propositionally equivalent to `b = true ↔ p`.
This differs in sort and packaging from source `reflect P b : Set`.
The existing Bool plus correctness law and the native Decidable class
together preserve the intended computation/proof relationship without a
new parallel inductive type.

| Actual provider | Reuse and hypotheses |
| --- | --- |
| `Bool.Reflects`, `Decidable`, `Decidable.isTrue/isFalse`, `Decidable.falseTrueCases`, `decide`; core Prelude | Existing Boolean result with a proof appropriate to the result; true/false presentations and computational branch selection. Keep the actual representation and proof/data sorts clear. |
| `decide_eq_true`, `decide_eq_false`, `of_decide_eq_true`, `of_decide_eq_false`; core Prelude | Both directions of the decision/proposition relationship, including negative outcomes. Require the relevant decision instance. |
| `decidable_of_decidable_of_iff`; core Core | Carries the input decision's Boolean unchanged and transports its proof. Inspect the actual iff orientation rather than cast computational data by propositional extensionality. |
| `decidable_of_iff`, `decidable_of_iff'`, `decidable_of_bool`; core PropLemmas | The Boolean adapter stores the supplied Bool directly. Its proof field can use an opaque theorem in Prop without blocking projection of the Boolean. The first iff adapter transports a decision for a across a↔b to a decision for b; the primed one reverses that direction. |
| `Subsingleton (Decidable p)`; core Core | Mathematical equality of decisions for the same proposition. Equality alone is not evidence of how a chosen opaque/parameterized definition reduces or executes. |
| `PLift`, `Sum`; core Prelude | `Sum (PLift A) (PLift B)` retains two observable data tags for arbitrary propositions A and B, even when both are true. This is the generic source sumbool adaptation. |
| `Nat.decEq`, `Nat.decLe`, `Nat.decLt`; core Prelude | Constructive concrete decisions for Nat equality and order. Preserve which decision is supplied to executable branches, especially in parameterized examples. |
| `ite`, `dite`; core Prelude | Branch on a proposition using supplied Decidable data; the dependent form also supplies the corresponding branch proof. A bare proof of an Or is not this instance. |
| `Classical.propDecidable`; core Classical | Explicitly noncomputable scoped instance built using choice. It demonstrates logical availability, not an algorithm deciding every proposition. Do not use it as the executable realization of the chapter's Nat/list examples. |
| `List.beq`, `List.hasDecEq`, the `DecidableEq (List α)` instance; core Prelude | Constructive list equality from element DecidableEq. It compares corresponding positions and length; it does not identify permutations. |
| `List.elem`, `mem_of_elem_eq_true`, `elem_eq_true_of_mem`, list membership Decidable; core List/Basic | Actual membership decision uses BEq and LawfulBEq. Standard constructive DecidableEq supplies the lawful equality path. Arbitrary BEq without a law cannot justify mathematical membership. |
| Accepted Perm reflection examples | Reuse its exact accepted Bool/Prop and `reflectedLt` definitions and checked true/false cases; current source is pending, not already accepted. |
| `List.orderedInsert`, `List.insertionSort` and accepted Sort source adapters/specifications | Exact first-satisfying-comparison insertion and tail-first insertion sort under an explicit DecidableRel. Use actual operation bridges before consuming sortedness/permutation/stability results. |
| `OrderCertificate.reference_correct`, `adjacent_correct`, `checkerSquare`, `checkedLength_correct` | Independent Boolean checker client. Reference correctness needs only the comparator law; adjacency describes IsChain without transitivity; Pairwise refinement and the composed checked-length client require IsTrans. |
| `LanguageDerivatives.recognize_correct`, `decideMembership` | Existing Boolean recognizer to proof-producing membership decision, through actual iff transport. Retain its DecidableEq alphabet premise. |
| `LanguageWitnesses.Decision`, `test_correct` | Existing witness-valued parser distinction: returns an actual value of a Type or a refutation and tests Nonempty. It is not a replacement for ordinary proposition-valued Decidable or a reason to erase parse witnesses. |

All these are read-only provider observations. No new import closure or compiler
result is asserted by this plan. Core providers live in the exact installed
toolchain; their inspected identities are recorded below.

## 3. Required formal presentations and computations

### Boolean reflection and generic proof sums

Retain the source's closed `(3 < 7)` Boolean equality and two derivations of
`3 < 7` from reflected evidence. One can explicitly inspect the decision's
cases; the other can consume its true-branch correctness directly. These are
method demonstrations, so merely invoking an unrelated arithmetic tactic
twice would lose their purpose. Include a false comparison and equal endpoints
as connected boundaries; the accepted Perm cases can be reused where exact.

For arbitrary A B : Prop, use a small source-facing alias of
`Sum (PLift A) (PLift B)`. Supply the exact source t1/t2 values and observable
left/right tags. When both `3 < 7` and `3 > 2` hold, v1a and v1b are distinct
data by Sum constructor disjointness. When the right proposition is `2 > 3`,
prove the impossibility of a right-tagged value from its proof payload.
Proof irrelevance within either branch does not identify the two data tags.

Only for B = Not A use the standard Decidable specialization. Retain t4's
quantification over both Nat arguments, v3 and the true result of is_3_less_7.
Generic sumbool A B must not be silently replaced with Decidable A, because
the latter cannot represent the source example where both branches are valid.
At that specialization, give the small explicit two-way adapter between
`Sum (PLift P) (PLift (Not P))` and `Decidable P`, with both round trips and
agreement of the observed left/true and right/false tags. Reuse an existing
exact adapter if available at implementation time; otherwise these are two
case maps, not a new decision framework. This connects the generic example
to the standard decision interface instead of leaving unrelated analogies.

Supply both source ways of constructing lt_dec: an ordinary expression and
an ordinary definition written using proof/term elaboration. Preserve their
equality and the intended true/false computational observations. The simplest
route uses the same existing Bool-to-decision adapter so that the equality
does not conceal different execution behavior. Distinguish that direct
equation from a proof using decision subsingletonhood.

### Sorting through decisions

The ScratchPad2 less-than and less-or-equal decisions use accepted reflection
laws and the constructive core adapter. The source recurrence is:

```text
insert x [] = [x]
insert x (h::t) = if the supplied le_dec x h says true
                 then x::h::t else h::insert x t
sort [] = []
sort (h::t) = insert h (sort t).
```

Retain the source Nat sorted predicate's nil/singleton/adjacent-cons interface
through the accepted Sort equivalence with IsChain/Pairwise. Prove the exact
decision-based operations equal the accepted source Sort operations on every
input, with the same comparison orientation and tie-before-head behavior.
Then consume their actual sortedness and permutation contracts. The exercise
specifically needs the proof-carrying branch lesson: checked local branch
lemmas or a short decision-case preservation derivation must exhibit the
positive `a ≤ h` and negative `Not (a ≤ h)` evidence.

Do not add sortedness as an execution precondition or rebuild a full sorting
library. If presenting a generic relation, preserve actual law assumptions
for sortedness and stability; bare DecidableRel does not imply totality,
transitivity or reflexivity. No repeated cost proof is needed merely because
the same operation now presents its decisions differently. A source-level
cost correspondence would require an explicit comparison-observation bridge,
not just equal outputs.

### Assumptions, logical proofs and blocked reduction

Introduce neither pedagogical source axiom globally. Present their interfaces
as ordinary scoped parameters:

```text
h : ∀ i j : Nat, i < j ∨ Not (i < j)
d : ∀ i j : Nat, Decidable (i < j).
```

The first is a proposition-valued excluded-middle witness; the second
contains branch data. For Nat, concrete constructive realizations already
exist. A generic illustrative maximum can use the second parameter and return
j on its true branch and i on its false branch. Prove the source instance
`maxWithDecision d 3 7 = 7` for every such d by using the branch evidence.
A generic equality to Nat.max is a useful connected law, with its proof
and branch orientation independently checked.

Before d is supplied, reduction of its Boolean field has no concrete branch
to inspect. This is a statement about the displayed parameterized term, not
a theorem that its result is logically unknowable: the source proves the
closed result from the decision's law. Instantiate Nat.decLt and retain a
closed computational equality. Do not fabricate a failed `#eval` output or
assert an unproved formal impossibility of implementing an arbitrary decider.

The rejected attempt to match a bare Or into a Nat is a sort/elimination
lesson. Or is inductive. Lean restricts general elimination of proof data
into computational data; False and permitted singleton-elimination cases
have different rules. A narrowly scoped expected-failure example can
demonstrate the actual restriction if needed, with its observed diagnostic
recorded. Do not claim that every elimination from Prop is forbidden.

The source's relative consistency remarks are context, not a proof of a
foundational consistency theorem in this development. Standard allowed Lean
axioms remain governed by conaled's exhaustive audit. No global axiom,
admission, unsafe code, native_decide or kernel bypass is introduced to
reproduce the lesson.

### Opacity and execution in Lean

Record why the Rocq proof at line 388 is abandoned: its definition branches
on a Set-valued reflection proof whose opaque derivation blocks that Coq
reduction. This need not reproduce as a Lean failure. Here the actual
`decidable_of_bool` stores the Bool separately from its Prop proof. Preserve
the corresponding positive Lean computation with the chosen definition and
the standard Nat decision, explaining the implementation difference.

If adding an actual Lean opaque-value demonstration, inspect its behavior
under both kernel reduction and compiled evaluation before stating it;
opaque declarations with bodies are not universally unexecutable. Such an
extra mechanism is unnecessary if the parameterized maximum and actual
Boolean-adapter computation already explain the required distinction.
No emulation framework or new opaque primitive is required.

Prefer `decidable_of_iff` over rewriting computational decision data by
propositional extensionality. The actual provider warns that the latter can
block kernel computation. Opaque proof fields and opaque computational data
are different situations. Record actual reduction/evaluation evidence,
separately from theorem equality and separately from native performance.

### List equality, membership and connected clients

Use constructive Nat equality with the standard list equality and membership
decisions. Preserve exactly:

```text
[1,3,4] =? [1,4,3]  → false
[1,3,4] =? [1,3,4]  → true
4 ∈? [3,1,4,1,5,9,2,6] → true.
```

Add an absent element and empty-list case to check negative evidence.
The first pair of lists is a permutation but not equal; retain this useful
connection to the earlier permutation/multiset chapters. The duplicate 1
does not change membership's meaning, and membership is not occurrence
counting or a returned index. The exact source in_4_pi theorem must be
kernel checked, not only printed by an evaluator.

Compose the accepted decision-based sort with the existing ordering checker:
derive an accepted Boolean certificate and checked length from the actual
sort theorem and the comparator reflection law. This supplies a real consumer
of the chapter's interface. A bounded language-recognizer example may also
consume the existing recognize_correct/decideMembership bridge to demonstrate
that the technique is not restricted to arithmetic. Reuse existing cases
when they already exhibit the exact boundary; do not add a new parser or
replace proof-relevant parser witnesses with booleans.
The concrete consumer contract is that checking the decision-based sort
returns `some xs.length`, using its sortedness and length/permutation facts.
For example, the independently expected output for `[3,1,2,1]` is
`[1,1,2,3]`, and the checked length is `some 4`.

## 4. Complete 32-record disposition

Each lexical inventory ID appears once below. Targets describe future checked
work, not already implemented declarations.

| Source record | Intended obligation / adaptation |
| --- | --- |
| `Decide.goal_at_line_63@63` | Closed comparison Boolean is true; kernel-checked source calculation. |
| `Decide.three_less_seven_1@73` | Derive 3<7 by the reflected decision cases and eliminate the impossible false branch. |
| `Decide.three_less_seven_2@89` | Derive the same proposition by directly consuming true-branch reflection, preserving the alternate method. |
| `Decide.ScratchPad.sumbool@121` | Alias of Sum of lifted proofs, retaining arbitrary A/B and two observable data tags. |
| `Decide.ScratchPad.t1@127` | Both-true source proof-sum type with propositions 3<7 and 3>2. |
| `Decide.ScratchPad.less37@128` | Checked arithmetic proof used as the left payload. |
| `Decide.ScratchPad.greater23@129` | Checked proof of 3>2 used as the right payload; do not reverse the inequality from its name. |
| `Decide.ScratchPad.v1a@131` | Left-tagged t1 value, with an observable tag equation. |
| `Decide.ScratchPad.v1b@132` | Right-tagged t1 value, distinct from v1a even though both propositions hold. |
| `Decide.ScratchPad.t2@140` | Proof sum whose right proposition is the false 2>3. |
| `Decide.ScratchPad.v2a@141` | Exact inhabited left branch; rule out a right value from its payload. |
| `Decide.ScratchPad.t4@157` | Nat-indexed constructive strict-order decision interface, with both arguments quantified. |
| `Decide.ScratchPad.v3@165` | Positive decision/proof-sum specialization for 3<7. |
| `Decide.ScratchPad.is_3_less_7@167` | Data-tag-to-Bool observation and true computation. |
| `Decide.ScratchPad.lt_dec@192` | Existing reflection-to-Decidable adapter with executable Boolean retained. |
| `Decide.ScratchPad.lt_dec'@201` | Ordinary definition through term/tactic elaboration, not an opaque theorem asserted to return data. |
| `Decide.ScratchPad.lt_dec_equivalent@208` | Actual equality of the two presentations and separate branch computations. |
| `Decide.ScratchPad2.lt_dec@232` | Standard namespace/implicit-argument adaptation of the same strict decision. |
| `Decide.ScratchPad2.le_dec@238` | Non-strict decision from the correctly oriented Bool law. |
| `Decide.ScratchPad2.insert@247` | Exact decision-branch insertion, tied to accepted Sort on every input. |
| `Decide.ScratchPad2.sort@253` | Exact tail-first decision-based sort and accepted operation bridge. |
| `Decide.ScratchPad2.sorted@259` | Accepted adjacent sortedness interface with source constructor characterizations. |
| `Decide.ScratchPad2.insert_sorted@268` | Complete preservation exercise, showing both proof-carrying branch hypotheses. |
| `Decide.ScratchPad2.lt_dec_axiom_1@328` | Scoped proposition parameter with constructive Nat witness; no new global axiom. |
| `Decide.ScratchPad2.lt_dec_axiom_2@341` | Scoped decision parameter with constructive Nat witness; no new global axiom. |
| `Decide.ScratchPad2.max_with_axiom@343` | Parameterized maximum branching on decision data; retain exact branch orientation. |
| `Decide.ScratchPad2.prove_with_max_axiom@359` | Prove the result 7 for all supplied valid decisions; distinguish proof from reduction before instantiation. |
| `Decide.compute_with_lt_dec@388` | Explain the abandoned Rocq opaque-reflection reduction and demonstrate the actual Lean adapter behavior. Not a false theorem or required Lean failure. |
| `Decide.compute_with_StdLib_lt_dec@407` | Kernel-checked result using the concrete constructive core decision. |
| `Decide.list_nat_eq_dec@450` | Standard constructive equality for lists of Nat; exact unequal/equal computations. |
| `Decide.list_nat_in@464` | Standard constructive membership decision; no hand-written replacement search or admission. |
| `Decide.in_4_pi@467` | Checked true result for the exact source list, plus negative/empty connected boundaries. |

## 5. Exercises, commands and modules

| Exercise and exact source range | Completion evidence |
| --- | --- |
| `insert_sorted_le_dec`, 267–285, standard, 2 stars | Actual decision-based insertion preservation, accepted operation/specification bridges, and checked positive/negative branch evidence. |
| `list_nat_in`, 460–472, standard, 2 stars | Constructive standard membership adapter and exact source computation theorem, with no source admission. |

| Source command | Lean adaptation |
| --- | --- |
| Check at 13 | Inspect the actual Nat less-than proposition interface. |
| Check at 14 | Inspect its executable Bool comparison/decide presentation. |
| Print at 21 | Show native Bool.Reflects and Decidable packaging, explaining the source Set versus Lean Prop distinction. |
| Check at 26 | Inspect the actual accepted reflection theorem's elaborated type. |
| Eval at 173 | True evaluation and checked equation for is_3_less_7. |
| Print at 175 | Inspect the two-argument constructive decision interface t4. |
| Check at 188 | Reuse the reflection theorem needed to construct lt_dec. |
| Print at 205 | Inspect the term-defined decision. |
| Print at 206 | Inspect the tactic/term-elaborated decision and its equality. |
| Locate at 225 | Identify the standard Decidable and generic proof-sum providers, not a nonexistent Coq name in Lean. |
| Print at 226 | Show actual pinned constructor/field/abbreviation details. |
| Eval at 352 | Explain the uninstantiated decision parameter's unresolved branch; preserve actual displayed behavior without fabricating a failure transcript. |
| Search at 418 | Inspect the relevant core comparison, list equality and list membership decision signatures; incidental Coq search-result enumeration is not a requirement to reimplement each library item. |
| Eval at 454 | Unequal positional lists return false. |
| Eval at 457 | Identical lists return true. |

ScratchPad at line 108 and ScratchPad2 at line 224 become bounded namespaces
or example sections. Preserve the distinction between the explicitly lifted
generic sum and ordinary standard decisions; namespace/notation/implicit
argument commands are not logical assumptions or an emulation requirement.

## 6. Prose coverage and source qualifications

| Source span | Required treatment |
| --- | --- |
| 3–26 | Adapt warning/import names, Prop/Bool distinction, actual reflection interface and accepted Perm branch method. |
| 28–53 | Computational-reflection motivation and historical references are context. No universal reflection system or separate formal undecidability development is introduced. |
| 55–103 | Preserve both evidence cases, the closed true result, and the two proof methods. Explain native representation accurately. |
| 110–213 | Generic data sums, both-true versus impossible branch, constructive predicate decisions, two definitions and their equality. |
| 216–242 | Explain the source's computability warning and standard implicit-argument presentation through the actual Lean API. |
| 244–284 | Exact insertion-sort recurrence, sortedness exercise, branch evidence and negative-branch typo correction. |
| 290–325 | Decidability versus logical excluded middle, computable realization versus proof availability, and contextual undecidability discussion. Do not claim an arbitrary classical decision is executable. |
| 328–371 | Parameterize the two pedagogical axioms, preserve maximum proof/computation distinction, and correct the claim that Or is not inductive. |
| 377–411 | Opaque Rocq proof obstruction, actual Lean Bool/proof separation, successful constructive standard decision. No universal claim that opaque Lean code cannot execute. |
| 413–458 | Relevant library decision composition, order-sensitive list equality, exact positive and negative results. |
| 460–476 | Complete membership exercise and source sanity check; discuss composability without building a new calculus. |
| 480–504 | Boolean-plus-law and proof-carrying-decision tradeoffs. In this pinned Lean representation the latter explicitly packages a Boolean and proof; fewer source interfaces do not establish a universal runtime advantage. |

Two concrete corrections must appear in the chapter documentation and statement
review: the false branch of le_dec a x supplies Not (a≤x), not Not (a<x);
and Or is inductive, with the relevant limitation coming from proof/data
elimination. Keep exact statement forms in connected examples so these
corrections cannot be lost in explanatory prose.

The chapter makes no quantitative complexity theorem for these adapters.
Do not invent timing claims from source discussion of possible efficiency.
Kernel computation, theorem equality, compiled evaluation and measured native
cost are distinct observations. Native implementation overrides in core are
not verified by proving the mathematical decision law.

## 7. Statement review, validation and acceptance

After #1015 acceptance, record the actual accepted baseline and predecessor
APIs before implementing. Develop independent expected examples alongside the
source-facing definitions, respecting the repository's example-driven workflow.

Statement review must check the actual elaborated types and consumers:

- Generic A/B proof sums retain both tags; proposition/negation specialization
  uses ordinary Decidable without changing the generic source example.
- Bool correctness includes both truth and falsity, with the selected runtime
  Bool preserved by the adapter and its proof kept in Prop.
- Strict/non-strict and operand orientations match every source branch;
  negative evidence is the exact negation of the tested proposition.
- Sorting has the exact all-input recurrence and accepted sortedness relation;
  logical relation assumptions are not inferred from mere decidability.
- Parameters replace global axioms; their concrete constructive instances are
  supplied before a computation is claimed. A theorem for every decision is
  distinguished from a reduction before that decision is known.
- List equality is positional, membership is a proposition, and neither is
  substituted for permutation, multiplicity, index retrieval or parse witness.
- The ordering-checker client retains its transitivity premise where needed;
  the language client retains its actual alphabet equality assumptions.

Use kernel-checked examples for 3/7, false/equal endpoints, both generic tags,
the maximum parameter and its concrete realization, source sorting plus the
checker consumer, both list equality results, and present/absent/empty
membership. Actual evaluator observations are useful execution evidence but
do not replace theorem proofs. Negative typechecking demonstrations, if used,
must concern the exact source lesson and record their actual diagnostics.

Integrate all source targets in the repository roots and coverage ledger.
Run the applicable focused checks, stable isolated exact-candidate full Nix
guard/build/exhaustive audit, required proof-audit regression, both independent
Standards/Spec implementation review axes and root's final candidate
verification immediately before acceptance. Preserve raw outcomes and exact
source identities. This plan neither starts those gates nor waives them.

Only after actual acceptance may root close the local chapter ticket and
create, restore-check, expose and upload its durability checkpoint. Then
Color implementation may begin. All 32 records, both exercises, 15 commands,
two modules and substantive prose dispositions need actual coverage evidence.

## 8. Exact inspected identities

The table below records inspected bytes, not newly compiled or accepted code.
The core path refers to the pinned toolchain and must be recovered from its
version, rather than assumed to exist at the same absolute path after restore.
Predecessor plans and current Perm examples remain pending at this writing.

Core root `LC` = `/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean`.
All other paths are relative to the workspace.

| File | SHA-256 |
| --- | --- |
| `reference/vfa/vfa/Decide.v` | `f929d55e2b7b39f2ba0bb72f2e70285dc8e10e64cf18322060bdbfc0552a4b26` |
| `work-state/source/Decide.inventory.json` | `5db3fc7c2f070863f2dc63271512d26b54a18d0d2c3cc198a162cc48221a322c` |
| `work-state/source/COMPUTATIONAL-ASSUMPTIONS.md` | `eb4e8eb1cc4d04f6fe536e87622c4943d6af160b555e7ae4266979484f3eca30` |
| `work-state/source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` | `5d26488e0127a072c61c3db0323deececfd428023d71cf51b4db6b4055e5e03f` |
| `work-state/specs/1003-Sort.md` | `fcc06acf05245de79637600479006e3d4a98f8bdf85c2537f5e7451cf3042955` |
| `work-state/specs/1010-ADT.md` | `f53d2e54b8d587e27e486f5a08fb1746cc8e2ee16810d0c28c9e44c8e3bfa3e8` |
| `work-state/specs/1011-Extract.md` | `eccc61e739b5a3ccc0e496ad13828a93b76ec925f3bd80047b799c833a9846ff` |
| `conaled/Examples/ComparisonPermutations.lean` | `325df7f29e321436e8bd09fa5eada9af614847825c06028af3933b3f447f393d` |
| `conaled/Applications/Checking/OrderCertificate.lean` | `288987762306ccde366d3471a2f731a214721895f52cbce4ae42a9f0862d479c` |
| `conaled/Applications/Languages/Regex.lean` | `031769848bcf6a2975e6b6620a09e3d73caa2e8f32bb346be5f579a7891bc082` |
| `conaled/Applications/Languages/Parser.lean` | `704f091282da8113c6a4354fe83dcffe58befb1ed6f5fc4c48985e84d3aa11ef` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/List/Sort.lean` | `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9` |
| `conaled/AGENTS.md` | `5d017d009307c72a7616d7afe0bee9fb5a7105fe2f6f4e1da3fdccf070d4b4fe` |
| `work-state/REQUIREMENTS.md` | `85fbb013efa28c2aa1827dfaaab9cca5c3498f1da51b446972aa67dd690a7f84` |
| `LC/Init/Prelude.lean` | `390e6b57ead28cb821a65533b21357f2f02d0a1525602f5a1ce9ee3eeb81fd12` |
| `LC/Init/Core.lean` | `264a0b48fedc91fadf55fc5caac8d91003e3908a6e5e42736e2ac8bf1f7cdf99` |
| `LC/Init/PropLemmas.lean` | `fd1e5105ce5d47da84164126280c06b5b3e69756dc41e3287046c7d10c01e1bc` |
| `LC/Init/Classical.lean` | `9217cf075cac15875b6fb5073ce5d150037953623fbfacac8a181214d42edd0b` |
| `LC/Init/Data/List/Basic.lean` | `566e74dd5c3e72b2111af000b8bd1552f1aaffe29be317ba01bc91c9e5b55293` |

Read-only reconciliation matched all 32 source records exactly once and in
inventory order, both exercise names/ranges, all 15 command kinds/lines, both
module dispositions and all 19 source/provider digests. These checks establish
planning bookkeeping, not mathematical completion or chapter acceptance.
