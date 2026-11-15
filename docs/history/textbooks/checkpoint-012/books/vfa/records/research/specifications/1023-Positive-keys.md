# Local #1023: shared positive binary key observations

## Purpose and boundary

Prepare a small reusable, checked representation adapter while the current
Preface/Perm full gate runs. The user explicitly permits cross-cutting concerns.
This representation seam supports later source extraction/key transport, Trie
and Color reasoning; it does not implement or accept any chapter algorithm.
All later chapter dependencies and acceptance gates remain unchanged.

Use the existing read-only source audit source/POSITIVE-KEY-REUSE.md and pinned
VFA 2.1 references. Main and isolated candidate remain at de575a8. Work only in
work-state/staging/positive-keys, with a clearly staged namespace. Do not edit
main/candidate sources, dependency caches, tooling/configuration, or active
processes. No extra shared key datatype, comparator class, table hierarchy,
resource language, or unrelated API redesign is wanted.

## Required mathematical seam

Reuse PosNum and PNat with the existing Mathlib numeric/cast facts. Preserve the
source constructor correspondence one/xH, bit0/xO, bit1/xI and prove its numeric
equations for arbitrary subtrees, with positive values. Keep these observations
explicitly distinct:

- Numeric observation of a positive binary value is at least 1.
- Shifted natural-key observation subtracts one, taking positive 1 to Nat 0.
- Nat encoding uses ofNatSucc (or an exactly proved existing equivalent).
  Unshifted ofNat clamps zero and is not injective over all Nat.

Prove both shifted round trips and both injectivity results, reusing existing
PosNum cast injectivity and PNat predecessor/successor infrastructure. A plain
Equiv with PNat or Nat is appropriate if it packages those established laws;
avoid duplicate conversion algorithms when an existing operation suffices.
The PNat correspondence must retain the positivity witness and relate numeric
value separately to the shifted key.

Reuse existing PosNum numeric comparison correctness to expose useful equality,
less-than and greater-than branch observations. This is numeric order only.
Do not implement Color's distinct bit order or its root-first choose, source
carry arithmetic, trie insertion/lookup, map/set implementations, or later
chapter algorithms in this shared adapter. No native runtime or cost claim
follows from these value conversions.

## Checked uses and statement review

Follow the repository's example-driven-development guidance. Start from the
independent expected key boundary 0 -> one -> 0, then retain distinct small keys,
a nontrivial binary-constructor value, and both numeric versus shifted values.
Connect cases to the general round-trip/comparison facts. Preserve a checked
counterexample to treating ofNat as injective on all Nat, and, if useful, the
positive predecessor's clamp at one versus the natural predecessor observation.
One connected client should recover a Nat-indexed observation through encoded
binary keys using the proved inverse law and an existing conaled Square or
ordinary function composition. This demonstrates actual reuse without building
a new table implementation. Keep Type/universe assumptions explicit.

Review statements for constructor direction, arithmetic offsets, positivity,
quantifier order, actual key equality, default/absence confusion, and accidental
identification of numeric order with Color's bit order. These are representation
lemmas, not source algorithm fidelity or traversal-cost proofs.

## Bounded development and evidence

Inspect relevant pinned declarations before coding. Preserve full source pins
and hashes in a concise README. Use the pinned Nix/Lean environment and a
focused staging-only compile; source, .olean/.ilean outputs and logs must stay
under this new folder. Reuse completed dependencies read-only, without a Lake
build or cache fetch. At most one auxiliary compiler may run alongside the
primary gate. Initial complete-draft invocation is bounded to 180 seconds plus
a five-second grace, with LEAN_NUM_THREADS=1. If it fails or times out, preserve
and report the concrete result before another invocation; root will decide
whether a bounded correction is warranted. Do not hide failed attempts.

Completed claims must have no admissions, added axioms, unsafe code, native_decide,
or skipped checking. Record exact commands, toolchain/source/dependency identities,
return codes, diagnostics and meaningful case/statement evidence. Preserve
output hashes and remove generated staging artifacts after extraction. Leave
all integrated chapter/ticket status to root. After a successful draft check,
obtain one independent bounded source/spec review within the existing workflow;
integration/full audit remains for the consuming chapter. Root will preserve
this work in a subsequent immediately exposed/uploaded recovery checkpoint.
