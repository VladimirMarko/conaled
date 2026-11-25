# Paid native-to-combined-action adapter: public contract

This is an uncompiled implementation contract. The frozen cases are in
`EXPECTATIONS.md`. Root owns every compiler, source installation, checkpoint,
and existing review. This directory supplies implementation assistance only.

## Target operation and finite data

The selected published convention is the combined print/move machine of
Stephen Cook, *The P versus NP Problem*, official Clay Mathematics Institute
PDF, appendix pages9–10:
https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf . Its transition
chooses the new control, printed letter and one-square direction together;
accept/reject controls stop. Input excludes blank and is initialized literally,
with the head on the first input symbol or a blank for empty input. The root
and this implementer read the pertinent definition pages1–2 and appendix,
without claiming a whole-paper reading.

Use the actual native `Turing.Tape` representation. The target step performs
literally `(T.write action.letter).move action.direction`; no source instruction
or unproved simulation relation substitutes for that operation. The generic
target step may be represented by an optional successor, with an explicit
proof that the adapter is total at every nonterminal control. A corresponding
total delta on the nonterminal subtype exposes the published transition type.

For native alphabet Γ and control Q, target control is the inductive finite
carrier with `normal q`, `returning q`, `accept`, and `reject`. Its cardinality
is `2 * card Q + 2`. The alphabet, blank and literal input list are Γ and the
original values; no symbol packing or input conversion occurs. Initialization
uses the supplied actual start q, even if an unrelated ambient default differs.
Normal start, accept and reject are distinct by their constructors.

## Executed adapter

At normal q, inspect the actual value `M q a` for the scanned a.

| Actual native selection | Actual combined action | Following action |
|---|---|---|
| move d to q' | print a, move d, enter normal q' | none needed for simulation |
| write b to q' | print b, move right, enter returning q' | print the new scanned letter unchanged, move left, enter normal q' |
| none | print a, move right, enter accept iff a equals the fixed true output letter, else reject | terminal |

The action function compares actual letters using a fixed `DecidableEq Γ`.
This equality instance is an explicit parameter of the generic construction.
The existing native decider contract supplies Fintype but does not itself
supply executable equality; a noncomputable finite existence instantiation is
not advertised as an exported executable transition table.

## Required witnesses and counts

The one-move lemma supplies an actual one-transition native `EvalsTo` value
for the new combined step. The one-write lemma supplies a two-transition value,
including the actual intermediate rightward tape and returning control. Both
end with exactly the native successor control in its normal copy and the
complete native successor tape, not merely the head value.

For an actual native live-endpoint witness with T successful steps, define the
sum of 1 for each selected move and 2 for each selected write along its literal
native prefixes. Prove an actual combined witness to the exact normal endpoint
with that count, and prove the count at most2*T. The zero-step witness must
lift with count0 without a positivity premise.

Given an actual stopped native endpoint whose head equals the injective fixed
Boolean output letter for b, append the actual single decision action. Its
control is accept for true and reject for false; its complete tape is the native
endpoint tape moved right. The final count is exactly the simulated count+1,
bounded by2*T+1, and a bounded native witness B yields2*B+1. There is no assumed
output decoder or arbitrary Boolean-output premise in a generic simulation
lemma. Output evidence is consumed only at the paid decision extension.

The actual accepting/rejecting cfg is the end of the published computation.
An additional optional-step observation returning outer none remains a separate
one-step event and is never included invisibly in that terminal cfg count.

## Space and later consumers

The target position trace must inspect every actual combined action. Writes in
the source create real temporary right visits; the final decision creates one
more right visit. The exact frozen cases observe both. A generic target-prefix
interval bound `max inputLength 1 + combinedSteps`, composed with the actual
witness, gives a conservative bound `max inputLength 1 + 2*T + 1`. This is not
a claim of identical visited space at normal boundaries.

The reusable existing `PolynomialBooleanDecider` consumer must fix all machine
data before the raw-word quantifier, preserve its blank/start and per-letter
input injection, and use a fixed natural polynomial `2 * time + 1`. It retains
the source stopped/output evidence and constructs the actual target witness.
It does not define an NP class or remove the independent delimiter protocol,
small-certificate correspondence, or polynomial-normal-form obligations.

The native sources remain pinned to Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The source142 primitive/controller
baseline and the now root-checked space draft are unchanged. No previous case
expectation, qualification, build result, or review decision is replaced here.
