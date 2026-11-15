# Positive binary keys: bounded reuse check

2026-11-02; preparation only. No Trie/Color implementation, compilation, or acceptance.
Sources: VFA 2.1, Lean 4.35.0, Mathlib revision recorded in `../environment.md`.
`Trie.v` SHA-256: `a5af2b4db4c2cb639a8deb063e57909e11eb44ee763782ad0af9afbf45a78f3e`.
`Color.v` SHA-256: `67b3410af5fece56c69f4e8301fd6505e89371cfa1279d069ca945b9b2b33370`.
Paths below beginning `Mathlib/` are relative to the pinned Mathlib checkout;
`Std/` paths are relative to the pinned Lean toolchain's `src/lean` directory.
All named Lean declarations below were located in source, not tested by compilation.

## Representation and conversion reuse

| Source shape | Existing representation/fact | Boundary or remaining transport |
| --- | --- | --- |
| `positive.xH`, `xO p`, `xI p` (`Trie.v131–151`, standard positive at 338–342) | `PosNum.one`, `PosNum.bit0 p`, `PosNum.bit1 p`; `Mathlib/Data/Num/Basic.lean`. Both are canonical positive binary trees with no zero constructor. | Reuse this existing datatype; record the constructor correspondence. The book's experimental `Integers.positive` and later Stdlib `positive` are separately scoped source types, despite identical constructor shapes. |
| `positive2nat` / `Pos.to_nat` | `castPosNum : PosNum → Nat`; `PosNum.cast_one`, `cast_bit0`, `cast_bit1`, `to_nat_pos`, `to_nat_inj` in `Mathlib/Data/Num/Lemmas.lean`. | Equations are 1, `n+n`, `(n+n)+1`; source uses `0+2*n`, `1+2*n`. Prove the all-input arithmetic bridge, using addition identities, not only numeral cases. |
| Positive numeric observation | `PNat := {n : Nat // 0 < n}` in `Mathlib/Data/PNat/Notation.lean`; `PNat.pos`, `ne_zero`, `coe_injective`, `coe_lt_coe`, `coe_le_coe` in `PNat/Defs.lean`. | `p ↦ ⟨(p : Nat), PosNum.to_nat_pos p⟩` is the narrow proposed adapter; no existing direct PosNum/PNat equivalence was found in the pinned Mathlib source search. PNat does not expose binary constructors. |
| Source `nat2pos n = of_succ_nat n`; `pos2nat p = pred (to_nat p)` (`Trie.v577–608`) | `Nat.succPNat`, `PNat.natPred`, `Nat.natPred_succPNat`, `PNat.succPNat_natPred` in `PNat/Defs.lean`; `Equiv.pnatEquivNat` in `PNat/Equiv.lean`. | This is the shifted bijection: positive 1 corresponds to Nat 0. It is not the unshifted numeric cast. Transport both inverse equations and both injectivity exercises to the chosen binary representation. |
| Binary-side inverse candidate | `PosNum.ofNatSucc`, `PosNum.ofNat` in `Num/Basic.lean`; `PosNum.succ_to_nat` in `Num/Lemmas.lean`. | `ofNatSucc n` targets `n+1`; `ofNat 0 = ofNat 1 = one`, so `ofNat` is not injective on all Nat. The corresponding cast/inverse lemmas for `ofNatSucc` remain a small proof obligation; do not misread `PosNum.of_to_nat`, whose result is `Num.pos p`, as that inverse. |
| Source predecessor observation at 1 | `PNat.natPred 1 = 0`; `PosNum.pred'_to_nat` relates `pred' : PosNum → Num` to Nat predecessor. | `PosNum.pred : PosNum → PosNum` clamps at 1, so it cannot itself implement source `pos2nat`. |

`PNat/Basic.lean` also supplies `PNat.natPred_injective`, `natPred_lt_natPred`,
`natPred_le_natPred`, `Nat.succPNat_injective`, and `OrderIso.pnatIsoNat`.
These shifted order facts concern numeric order; they do not transport Color's bit order.
No finite machine-word bound is imposed by PosNum or PNat. A bounded integer key would
require an additional range contract and would not represent all source positives.

## Arithmetic comparison and constructor traversal

`PosNum.succ` follows exactly the source successor constructor cases.
`PosNum.succ_to_nat`, `add_to_nat`, `cmp_to_nat`, `cmp_eq`, `lt_to_nat`,
`le_to_nat`, `lt_iff_cmp`, and `le_iff_cmp` are in `Num/Lemmas.lean`.
`PosNum.cmp_to_nat` distinguishes lt / eq / gt and gives actual key equality
in the eq branch, sufficient to recover the source numeric equality branch.
The source's comparison definition still contains an explicit placeholder case
(`Trie.v283–291`); a completed algorithm and its fidelity are later obligations.
The library's `PosNum.add` uses a different recurrence from source `addc` with its
carry argument. Its arithmetic correctness does not discharge source carry fidelity
or traversal costs. `PosNum.natSize_to_nat` proves binary height equals `Nat.size`
of the numeric value; `size_eq_natSize` and `natSize_pos` are also available.
These are size facts, not runtime claims; `ofNatSucc` itself recurses on Nat.
Trie paths inspect the low bit first (`bit0` left, `bit1` right, `one` stop),
whereas source `print_in_binary` presents the high bit first (`Trie.v160–165`).

## Color needs two distinct nonnumeric observations

`Color.v73–120` chooses `PositiveOrderedTypeBits`, explicitly not numeric order.
The official [Rocq 9.0 OrderedTypeEx source](https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Structures.OrderedTypeEx.html)
defines `bits_lt`: every `xO _` precedes `xH`, which precedes every `xI _`;
equal `xO` or equal `xI` outer constructors recurse. Consequently 2 precedes 1.
Source `domain_example_map` returns `[2,9,3]` (`Color.v144–146`), not numeric order.
`PosNum.cmp`, `PosNum.linearOrder`, and PNat's inherited order are numeric;
none can silently replace this relation. Use an explicit comparator parameter,
with a small proved constructor adapter, rather than replacing the global order.

Choice is a further distinction: official [Rocq 9.0 FSetPositive source](https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.FSets.FSetPositive.html)
defines `PositiveSet.choose` root-first, then left, then right; `min_elt` is
left-first, then root, then right. From those equations, on the set `{1,2}`,
choose returns 1 and the bit-order minimum returns 2. This is a source-derived
counterexample, not a newly compiler-checked Lean case. Thus even a TreeSet
minimum under the correct bit order does not implement source `S.choose`.
Transport ordered enumeration and concrete choice separately. A generic choice
with membership/empty laws may prove an abstract coloring theorem, but cannot
by itself recover the source algorithm's choices and computed coloring example.

## Available finite-map interfaces

| Existing interface | Located reusable declarations and assumptions |
| --- | --- |
| `Std.TreeMap K V cmp` (`Std/Data/TreeMap/Basic.lean`) | `empty`, `insert`, `erase`, `get?`, `getD`, `keys`, `toList`, `foldl`, `map`; explicit comparator avoids a new key wrapper hierarchy. |
| `Std.TreeMap` laws (`Std/Data/TreeMap/Lemmas.lean`) | `getElem?_emptyc`, `getElem?_insert`, `getElem?_erase`, `size_erase`, `size_map`, `ordered_keys`, `ordered_keys_toList` use `Std.TransCmp cmp`; `mem_keys` and `getElem?_map` additionally use `Std.LawfulEqCmp cmp`. The insert/erase tests are `cmp stored query = .eq`. |
| `Std.TreeSet` laws (`Std/Data/TreeSet/Lemmas.lean`) | `mem_toList` needs `TransCmp` and `LawfulEqCmp`; `ordered_toList` and `size_erase` need `TransCmp`. `min?_eq_none_iff` and `min?_eq_some_iff_mem_and_forall` specify minimum selection, not the source root-first choose. |
| Numeric order infrastructure | `PosNum.linearOrder` (`Num/Lemmas.lean`) and PNat's derived `LinearOrder` (`PNat/Defs.lean`); `compare_lt_iff_lt`, `compare_eq_iff_eq`, `compare_gt_iff_gt` plus the `Std.LawfulBCmp compare` instance in `Mathlib/Order/Defs/LinearOrder.lean`. The explicit source bit comparator still needs its own laws. |
| Extensional finite-map specification | `Finmap` in `Mathlib/Data/Finmap.lean`: `lookup`, `lookup_empty`, `lookup_insert`, `lookup_insert_of_ne`, `lookup_erase`, `lookup_erase_ne`, `ext_lookup`, `keys`, `mem_keys`, `keys_erase`; lookup/update use `DecidableEq K`. Its `foldl` requires a commutation proof and its entries are a multiset, so this supplies no ordered list or root-first choice automatically. |

These are existing alternatives to reuse according to the later specification;
this note selects no new map implementation and proposes no additional map hierarchy.
Extensional lookup equivalence alone does not imply equality of internal trees.

## Explicit later transport obligations

1. Establish the constructor/numeric adapter, positivity, numeric comparison branches,
   and shifted inverse equations. Keep `positive2nat p` distinct from `pos2nat p`.
2. For Trie, preserve the `look`/`ins` constructor recurrences and default at Leaf,
   then prove same-key/other-key lookup and `abstract t n = lookup (nat2pos n) t`.
   The shifted key equality must justify `lookup_relate` and `insert_relate`.
3. For Color, prove the bit comparator's equality, transitivity and order correspondence;
   transport list membership, sortedness, nodup keys, erase/filter and cardinal decrease.
   Preserve optional lookup: absence differs from a present binding to an empty set.
4. Connect folds to the actual source traversal, or prove the needed commutation result;
   separately reproduce root-first choice for source-faithful selection/coloring and
   the source's computed examples. Keep abstract choice-parametric correctness explicit.
5. Check boundary clients later: key 1 ↔ Nat 0, constructor ten, different numeric/bit
   ordering, `{1,2}` choice versus minimum, and zero rejection/noninjective `ofNat`.
   Neither library conversions nor extensional laws imply source bit-operation costs.

Only this note was written. No compiler, build, dependency, cache, or chapter state changed.
