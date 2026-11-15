# Tail arithmetic: exact pinned source/API assessment

Recorded: 2026-11-04T09:23:44.997922+00:00. Author: `/root/shared_acceptance_sequence`.

**Proof-development support only.** No compiler, Lake, build, cache, check,
audit, verification or process-polling operation was run. No repository/ref
or existing provenance record was edited. Proposed Lean code below has been
source-assessed but **has not been compiled by this author**. This is not an
independent final review or evidence of candidate acceptance.

## Scope and actual observations

The complete261-line `Examples/PermutationTailBoundary.lean` was read from
immutable `13fc137c67e1dc974c833e81cd46042d757fa546`. Its bytes also match the
file at central `6b95185ac51bcb21ab5b7b3ed4fe309bda55855a`. The bounded repair
concerns only the final arithmetic steps of `counter_joint21_mass`,
`outside_order_12_mass` and `outside_order_21_mass` at source lines210–252.
All previously established event identities, probability formulas and case
hypotheses are outside this change.

The saved focused8 diagnostic extract reports `simp made no progress` at
225,237,249. Its own receipt labels the log a partial prefix; no aggregate
terminal result is inferred from it. Root subsequently supplied a completed
three-obligation arithmetic probe. Its complete928-byte log and result were
read and hash-verified: exit1 at clean unchanged Q. `norm_num [← ENNReal.coe_div]`
leaves exactly:

```lean
(6 : ENNReal)⁻¹ + 6⁻¹ = 3⁻¹
(2 : ENNReal) * 6⁻¹ = 3⁻¹
(2 : ENNReal) * 3⁻¹ = 2 / 3
```

These are the same intended numerical equations after simplification, not a
changed mathematical obligation. The source formulas are 1/6+1/6=1/3,
2*(1/6)=1/3 and2*(1/3)=2/3.

## Exact APIs

Mathlib HEAD and source objects match the pinned
`56a005855ea17e0b0958f73ec801ae140b0a1679`; the project toolchain pin is
`leanprover/lean4:v4.35.0`. The old `Mathlib/Data/ENNReal/*` paths are
compatibility imports; substantive declarations are under `Mathlib/Basic/`.
The actual source excerpts and whole-file identities are preserved in
`api-excerpts.txt` and `receipt.json`.

The following signatures spell out coercions present in the source; they
are source-interface descriptions, not newly printed elaborated-type output.

| API | Exact relevant source | Role |
| --- | --- | --- |
| `ENNReal.coe_div {r p : NNReal} (hr : r ≠ 0)` | `Mathlib/Basic/ENNReal/Inv.lean:78–80` | `↑(p / r) = (↑p : ENNReal) / ↑r`; the denominator condition is essential. |
| `ENNReal.coe_inv {r : NNReal} (hr : r ≠ 0)` | Same file:68–70 | `↑(r⁻¹) = (↑r : ENNReal)⁻¹`; it also requires nonzero denominator. |
| `ENNReal.coe_add (x y : NNReal)` | `Mathlib/Basic/ENNReal/Basic.lean:405` | `↑(x+y) = (↑x : ENNReal)+↑y`, proved by `rfl`. |
| `ENNReal.coe_mul (x y : NNReal)` | Same file:407 | `↑(x*y) = (↑x : ENNReal)*↑y`, proved by `rfl`. |
| `ENNReal.coe_one` | Same file:275 | `↑(1 : NNReal) = (1 : ENNReal)`, proved by `rfl`. |
| `ENNReal.coe_ofNat (n : Nat) [n.AtLeastTwo]` | Same file:414 | Explicit numeral coercion to the corresponding ENNReal numeral, proved by `rfl`. |
| `ENNReal.coe_natCast (n : Nat)` | Same file:509 | Casted natural coefficient bridge for a variable natural, proved by `rfl`. |
| NNReal `Semifield` instance | `Mathlib/Basic/NNReal/Defs.lean:111–118` | Supplies rational arithmetic for the auxiliary equations. |

## Why the original simplification does not transfer the goal

The reversed `coe_div` rules match expressions whose numerator and
denominator are **explicit NNReal coercions**. The source targets use bare
ENNReal numerals. Although `coe_one`/`coe_ofNat` prove the finite numeral
identifications by reflexivity, this does not force `simp only` to present
the goal in the desired coerced syntax. The supplied reverse rules and
`coe_inj` do not first construct that finite-source equality.

Pinned Lean uses `.reducible` transparency both for simplifier indexing and
for its matching `isDefEq` (`Lean/Meta/Tactic/Simp/Types.lean:138–174`);
`Rewrite.lean:115–142` performs that matching, and215 retrieves indexed
candidates. Thus unrestricted kernel definitional equality is not itself a
promise that a reverse rule on explicit coercions will rewrite a numeral-form
goal. Explicit theorem arguments may also use wildcard argument indexing
(`DiscrTree/Main.lean:257–290`), so this assessment does **not** claim an
uncollected trace proving that discrimination-tree retrieval alone was the
particular rejection point. The evidence establishes the coercion/matching
mismatch and the unsuccessful selected simplification; the proposed repair
avoids either matching-stage issue.

The failed shorter probe has a second clear limitation: `norm_num`'s
`evalDiv` (`Mathlib/Tactic/NormNum/Basic.lean:571–573`) and `evalInv`
(`Mathlib/Tactic/NormNum/Inv.lean:245–248`) require `DivisionSemiring`.
NNReal has the required Semifield structure. ENNReal has an extended inverse:
its pinned `inv_zero` theorem says zero inverse is infinity, not zero
(`Mathlib/Basic/ENNReal/Inv.lean:54–55`). It cannot be treated as an ordinary
division semiring for these normalizations. Adding reverse coercion lemmas
to `norm_num` does not automatically supply the missing finite representation.

## Proposed bounded proof

For each obligation, first prove the identical rational equation in NNReal
with `norm_num`. Apply `congrArg (fun x : NNReal => (x : ENNReal))` to obtain
an equality explicitly between coerced NNReal expressions. Then use only
**forward** `coe_add`/`coe_mul`, the appropriate forward `coe_div` instances
with explicit nonzero3/6 proofs, `coe_one` and `coe_ofNat`.

The complete unexecuted program is `ProposedObligations.lean`. Each proof
body can replace the corresponding final arithmetic block while retaining
every theorem statement and preceding event/measure argument. No helper
axiom, evaluation oracle, mathematical hypothesis or runtime/profile change
is introduced. The finite denominator restrictions are proved rather than
silently dropping ENNReal's exceptional zero behavior.

This is a source-supported repair strategy, not a claimed elaboration pass.
The root should obtain a closed result for the actual three-obligation probe
and then validate the complete changed module/candidate under the retained
workflow. No optional alternate method is required if this transfer succeeds.

## Read boundary and completion

The complete original Tail boundary source, saved diagnostic extract,
closed arithmetic probe source/result/log and complete proposed obligations
were read. The relevant exact API and simplifier source ranges are retained;
the complete surrounding Mathlib/Lean files were not represented as reviewed.
Earlier broad search output was truncated and was used only for navigation;
every declaration/configuration section relied on here was re-read in a
bounded nontruncated excerpt. No full mathematical review beyond the three
arithmetic proof interfaces is claimed.

All writes are confined to this new assessment directory. **HOLD:** complete
source/API support, no source application or validation credit.
